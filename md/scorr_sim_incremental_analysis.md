# `&scorr` — Sim 阶段 Incremental 可行性分析 + Profiling 分支说明

> 配套分支：`scorr_profiling`（从 `incremental_pr` 切出）
> 用途：回答 Alan 的两个问题 —— (a) "为什么 p 很小的行还是慢"，(b) "类似的 avoid-recomputation 还能用在哪里、能不能更高效"。
> 配合阅读：[scorr_incremental_discussion_notes.md](scorr_incremental_discussion_notes.md)

---

## 0. TL;DR

| 问题 | 结论 |
| --- | --- |
| Sim 阶段能不能也做 incremental？ | **能，但属于中等 ROI**，且有一个真实的 soundness 陷阱（见 §3）。 |
| Sim 为什么从 6.55s 涨到 9.06s？ | 最可能是 **cache footprint 回归**（H2），不是仿真算法本身变慢。如果是，**几乎零成本就能修回 +2.5s**，根本不用动仿真算法。 |
| 优化效果上界 | 真·incremental sim 约能省 **3–5s**；若只是 cache 回归，修 footprint 省 **~2.5s**。占总时间 4–9%。 |
| 比 Sim 更值得打的是什么？ | `p` 很小却仍要 30–40ms 的 floor，根因是 **每个 iteration ~7 个 O(N) / O(pairs) 的全量 pass + ~5MB 的 alloc/free**。这才是 Alan 说的 "surprising"。Profiling 分支就是为定位它而做。 |
| 编译/运行内存 | 编译峰值 ~2–3GB（`make -j8`），磁盘 <1GB；跑这个 case 运行时 ~几百 MB。**16GB Mac 完全够，可以放心配环境。** |

---

## 1. Sim 阶段到底是什么（代码路径）

`&scorr` 主 loop 里 "Sim" 计时桶只包住一个调用：

```
Cec_ManResimulateCounterExamples( pSim, vCexStore, nFrames )   // cecCorr.c
├─ Gia_ManCorrCreateRemapping( pAig )      // O(N)  —— 建 repr 重映射表 vPairs
├─ Gia_ManCreateValueRefs( pAig )          // O(N+E)—— 引用计数
├─ Vec_PtrAllocSimInfo( ... )              // 分配仿真字缓冲
└─ while ( 还有 CEX 批次 )
   ├─ Cec_ManStartSimInfo / LoadCounterExamples   // 把 CEX 位填进仿真字
   ├─ Gia_ManCorrPerformRemapping( vPairs, ... )  // 按 repr 重映射
   └─ Cec_ManSeqResimulate( pSim, vSimInfo )      // ★ 真正的位并行仿真 + 类细化
```

关键点：
- **`Cec_ManSeqResimulate` 才是仿真本体**，复杂度 `O(N × nWords × nFrames)`，是 memory-bandwidth bound 的流式 kernel。
- 它前面的 `Gia_ManCorrCreateRemapping` + `Gia_ManCreateValueRefs` + 分配是 **每个 iteration 都做一遍的 O(N) 固定开销**，跟 CEX 多少无关。
- 仿真是 **全 AIG 跑**的 —— 这就是 incremental 化的发力点，也是目前没碰的东西（见 notes §2.4）。

---

## 2. Sim 为什么不降反升（6.55s → 9.06s）

三个假设，按可能性排序。Profiling 分支能直接判定是哪个。

### H2（最可能）：cache footprint 回归
- incremental 版在整个 run 期间常驻多了：static fanout 数组（245K 对象 → ~2–3MB）、两份 snapshot 向量（`vReprPrev`/`vNextPrev`，各 ~1MB）、`pTfoMark`（~1MB）。合计 **常驻多 ~6MB**。
- `Cec_ManSeqResimulate` 是带宽受限 kernel，多出来的 6MB 常驻结构把仿真的工作集挤出 L2/L3 → **每个节点的仿真变慢**。
- +38% 的涨幅，在带宽受限 kernel 上和 "工作集被挤出 cache" 完全吻合。
- **如果是 H2：修复几乎免费** —— 在进入主 refinement loop 之前、确实不需要 static fanout 的阶段把它释放；或把两份 snapshot 换成更紧凑的表示（只存 dirty 列表而非全量数组）。不用动仿真算法就能修回 +2.5s。

### H1：O(N) setup floor（解释 floor，不解释回归）
- `Gia_ManCorrCreateRemapping` + `Gia_ManCreateValueRefs` 每个 iteration 跑一次，332 次。
- 但 baseline 和 incremental **iteration 数相同**（都到 332），所以这块固定开销两边一样 → 它构成 floor，但**不构成回归**。

### H3：CEX 数量不同（基本排除）
- CEX 数量 ≈ `d` 列。对照两份 profile：BMC 段 line 17–77 的 `d` 列**逐行相同**，主 loop 段两边 `d` 几乎全 0。
- → 两边重仿真的 CEX 体量一致，H3 排除。

**结论**：回归几乎肯定是 H2。Profiling 分支里 `sim=...(rmp=.. run=..)` 把 setup 和仿真本体拆开 —— 如果同样 CEX 体量下 incremental 的 `run=` 更大 → 实锤 cache；如果 `rmp=` 占大头 → 是 O(N) remapping。

---

## 3. 把 Sim 做成 incremental —— 可行性 + 正确性

### 3.1 朴素想法（**不正确**）
"只仿真『repr 变了的节点』的 TFO" —— 这是错的。一个注入到输入的 distinguishing pattern 会沿**整个 fanout cone** 传播；一个离任何 changed-repr 都很远的节点，仍可能被某个 CEX pattern 区分开。漏掉它 → 漏掉 class split → 产生 **spurious equivalence（不 sound）**。

### 3.2 正确的 incremental sim
要重仿真的集合不是 "changed-repr 的 TFO"，而是：

> **所有 CEX 的输入 support 的 fanout 闭包的并集。**

理由：本轮 CEX 全部来自 active SRM，而 active SRM 的 PO 只有 active pairs。一个 CEX 只能让"在该 pattern 下取值发生变化"的节点被新区分；取值可能变化的节点 = 该 CEX support 可达的 cone。所以：
- **proof 用窄 IFO**（已实现：active pairs 的 TFO）；
- **sim 用宽 IFO**（CEX support 的 fanout 闭包）—— 两个集合不同，sim 的必须是 sound 的 over-approximation。

这个集合是可算的，而且在后期 iteration（CEX 很少、很局部）通常远小于 N。

### 3.3 安全落地路径
1. 先做 **dual-sim 模式**：full sim 跑出 ground truth，incremental sim 跑出结果，逐 iteration assert 两者把类切得完全一致。
2. 跑通若干 HWMCC case 后，再去掉 full-sim 这根拐杖。
3. ⚠️ 注意：`Cec_ManResimulateCounterExamples` 除 CEX 位外可能还 random-fill 非 CEX 字（`Cec_ManStartSimInfo`）。随机 pattern 是全局的 —— 要么 incremental sim 也覆盖随机字影响的 cone，要么随机字单独走 full path。这一点要在 discussion 上跟 Alan 确认清楚。

---

## 4. 优化效果估计

| 情形 | 预计省下 | incremental 总时间 |
| --- | ---: | ---: |
| 现状 | — | 61.89s |
| 若回归是 H2 → 修 footprint（近零成本） | ~2.5s | ~59s |
| 真·incremental sim（后期跳过 70–90% 节点求值） | 3–5s | ~57–58s |

Sim 占比只有 14.6%，**即使做满也就 4–9% 总时间**。所以建议：
- **先用 profiling 确认 H2**。是 H2 就先免费修回退化，性价比最高。
- incremental sim 作为第二梯队，价值中等。
- **真正的大鱼是 §5 的 per-iteration floor**，不是 Sim。

---

## 5. "p 小却仍慢" 的根因（Profiling 分支要锤的就是这个）

`pAig` 在整个 refinement loop 里 **对象数恒为 ~245,698 不变**（化简发生在最后的 `Gia_ManCorrReduce`）。因此**每个 iteration，不管 p 是 2 还是 17 万，都要付**：

| # | 固定开销 | 量级 |
| --- | --- | --- |
| 1 | `Gia_ManCorrSpecReduce_Active`：`Vec_IntFill(vCopies, 2·245698, -1)`（~2MB 填充）+ `Gia_ManStart(245698)`（预分配 ~3MB 并 memset）+ `Gia_ManSetPhase` + `Gia_ManForEachObj1` 遍历全部对象/全部 ring class（即使只 emit 几个 PO）+ `Gia_ManCleanup` | O(N) + ~5MB alloc/free |
| 2 | `Cec_IncrMgrCountActivePairs`：遍历**每一对** candidate pair（后期仍 ~170K 对） | O(pairs) |
| 3 | `Cec_IncrMgrComputeSeeds` | O(N) |
| 4 | `Cec_IncrMgrCountNextChanges` | O(N) |
| 5 | `Cec_IncrMgrSnapshotClasses` | O(N)，每对象 2 写 |
| 6 | `Cec_ManRefinedClassPrintStats` | O(N) |
| 7 | `Cec_ManResimulateCounterExamples` 里的 remapping + valuerefs | O(N) |

即使 p=2，一个 iteration 也要跑 **~7 趟 O(N≈245K) / O(pairs≈170K) 的全量 pass + ~5MB 的 alloc/free**。这就是那 30–40ms 的 floor，也就是 Alan 说的 "surprising"。

可攻击方向（discussion 备选）：
- **复用 SRM 的 `Gia_Man_t`**：不要每个 iteration `Gia_ManStart`/`Gia_ManStop` 一个 245K 容量的对象，改成 reset + 复用 → 砍掉 #1 的 alloc/free。
- **CountActivePairs 增量化**：用 IFO 已有的信息，只数受影响的 pair，而非每轮全扫 170K 对。
- **snapshot 差量化**：只记 dirty 列表，不每轮全量拷贝 2×N。
- **seeds/next 合并成一趟 traversal**，减少 cache miss。

---

## 6. Profiling 分支 `scorr_profiling` 说明

### 6.1 加了什么
| 文件 | 改动 |
| --- | --- |
| `src/misc/util/abc_global.h` | 新增 `Abc_ClockHr()` —— 纳秒级 wall-clock。`Abc_Clock()` 在 macOS 上回退到 `clock()`（CPU 时间、精度粗），`Abc_ClockHr()` 始终用 `CLOCK_MONOTONIC`（现代 macOS/Linux 都支持），子毫秒的 per-proof 阶段才看得清。 |
| `src/proof/cec/cecCorr.c` | 主 loop + BMC loop 每个 iteration 的相位拆解；Sim 内部 remap/run 拆分；per-proof 计数汇总；末尾打 `ALL` 总行。 |
| `src/aig/gia/giaCSat.c` | `Cbs_ManSolveMiterNc`（主 loop 用的电路 SAT）：拆 setup 与 per-PO solve。 |
| `src/aig/gia/giaCTas.c` | `Tas_ManSolveMiterNc`（BMC 用的电路 SAT）：同上。 |
| `src/proof/cec/cecSolve.c` | `Cec_ManSatSolveMiter`（`-c` 关掉时的 MiniSat 路径）：同上。 |
| `src/proof/cec/cecInt.h` | profiling 全局量的 extern 声明。 |

> 说明：这个 token_ring case 默认 `CSat=1`，主 loop 实际走 `Cbs`、BMC 走 `Tas`。`Cec_ManSatSolveMiter` 也一并插桩，方便将来 `-c` 关掉时对比。

### 6.2 怎么用
profiling 输出 **只在 `-w`（very verbose）下打印**；`-v` 的输出**逐字节不变**，Alan 的 side-by-side 对照不受影响。

```
./abc -c "&r <case>.aig; &scorr -ivw"      # incremental + profiling
./abc -c "&r <case>.aig; &scorr -vw"       # baseline + profiling（同样能用，可对照）
```

每个 iteration 多打一行（时间单位 ms）：

```
[prof  330] wall=  39.800 p=     2 | ifo=  8.100(sd=2.200 nx=2.000 tfo=0.100 cnt=3.800) snap= 1.100 srm= 21.400 sat=  6.200(set=5.900 slv=0.250 max=0.1800 n=2) sim= 2.100(rmp=1.800 run=0.300) chk= 0.300 stat= 1.400 rest= 0.300
```

字段含义：
- `wall` 整个 iteration 的高精度墙钟；`p` 本轮 per-PO solve 调用数（≈ 证明数）。
- `ifo` = `sd`(ComputeSeeds) + `nx`(CountNextChanges) + `tfo`(ComputeTfo) + `cnt`(CountActivePairs)。
- `snap` snapshot；`srm` SRM 构建（含上面 §5#1 的 alloc/fill/cleanup）。
- `sat` = `set`(solver alloc + AIG prep) + `slv`(所有 per-PO solve 之和) + `max`(最慢的单次 solve) + `n`(per-PO solve 次数)。**这就是 per-proof 信息**。
- `sim` = `rmp`(O(N) 重映射 setup) + `run`(`Cec_ManSeqResimulate` 仿真本体) —— 直接判定 §2 的 H1/H2。
- `chk` CheckRefinements；`stat` 打印 stats 本身；`rest` = wall 减去以上全部 = 纯 loop/housekeeping 开销。

末尾还会打一行 `[prof  ALL]` / `[bmc-prof ALL]` 把全程各相位累加 —— 一眼看出总账里固定开销占多少。

### 6.3 怎么读结果（给 discussion）
- 如果某个小 p 行 `srm` 远大于 `sat` → 实锤 §5#1，下一步复用 `Gia_Man_t`。
- 如果 `ifo` 里 `cnt` 大 → CountActivePairs 全扫太贵，要增量化。
- 如果 `sat` 里 `set ≫ slv` → SAT 时间花在 solver cold start，不在真正 solve → 印证 notes §4/§5.1 "跨 iteration 复用 solver"。
- 如果 incremental 的 `sim run` 比 baseline 大而 CEX 体量相同 → §2 的 H2 cache 实锤。

---

## 7. 编译 / 运行环境与内存

测过本机：Apple clang 17，10 核，16GB RAM。仓库 102MB。

**编译**
- ABC 单文件编译大多 <100MB；最大的 `src/base/abci/abc.c`（2.1MB 源码）在 `-g -O`（默认 `OPTFLAGS`）下约 0.8–1.2GB。
- `make -j8` 峰值 ~2–3GB（多个大文件并行）；磁盘：.o + 二进制 <1GB。
- 首次编译约 3–6 分钟；Makefile 自动启用 ccache，二次编译近秒级。
- macOS 注意：若卡在 readline，用 `make ABC_USE_NO_READLINE=1`。`gcc` 在 Mac 上通常已别名到 clang，否则 `make CC=clang CXX=clang++`。

**运行这个 case**
- 输入 AIG：236K ANDs / 245K 对象，ABC 自报 `mem = 2.85 MB`。
- `&scorr` 运行峰值 RSS 估 **~150–400MB**（原 AIG + 每轮临时 SRM + SAT 结构 + 仿真字 + incremental manager 的 static fanout/snapshot ~6MB）。这个 case 本身不大（60–120s 跑完）。

**结论：16GB Mac 绰绰有余，可以放心配置环境、本地编译运行。** 真正占内存的 HWMCC 大 case 才可能上 1–4GB，本 case 不会。

---

## 8. 建议的下一步顺序

1. **编译 `scorr_profiling`，跑 `&scorr -ivw` 和 `&scorr -vw`**，拿到 per-iteration 相位拆解。
2. 用 `[prof ALL]` 总行 + 几个代表性小 p 行，确认 floor 的构成（§5）和 Sim 回归的归因（§2 H1/H2）。
3. 若 Sim 回归是 H2 → 先做近零成本的 footprint 修复，拿回 ~2.5s。
4. 主攻 §5 的 per-iteration floor：优先 **复用 SRM 的 `Gia_Man_t`** + **CountActivePairs 增量化**。
5. incremental sim（§3）作为第二梯队，且必须走 dual-sim 验证。
6. 把数据画成 notes §7 的图 C（小 p iteration 的 micro-profile breakdown）带去和 Alan 讨论。
