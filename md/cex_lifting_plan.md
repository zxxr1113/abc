# CEX Lifting — 设计方案 (cex_lifting branch)

> Branch: `cex_lifting` (基于 `rIC3_sim`)
> 目标: 在 `&scorr` 的归纳主循环中, 把每个 SAT 反例从"一条向量"扩展为"一个 cube + 多个随机扩展", 提高每次 SAT 调用对等价类的细化产出.

---

## 0. TL;DR

每次 `Cbs_ManSolveMiterNc` / `Cec_ManSatSolveMiter` 返回的 vCexStore 已经是 partial assignment (cube), 但没有做到最小化, 也只塞进一个 bit-slot. 我们的改造是两层正交优化:

1. **Ternary Lifting** — 在 SRM 上做 3-valued 仿真, 把 cube 中可以丢掉的 literal 丢掉, 得到极小化 cube.
2. **Cube Replication** — 极小化后, 把同一个 cube 复制到 K 个 bit-slot, 每个 slot 用不同随机比特填充自由位置.

两者都在 `Cec_ManResimulateCounterExamples` 的入口处插入, 不动 SAT 求解器、不动 SRM 构造、不动 sequential resim 后端. 接口最小侵入.

---

## 1. 当前状态分析 (rIC3_sim 分支)

### 1.1 数据流

```
Cec_ManLSCorrespondenceClasses (cecCorr.c:935)
  └─ loop:
       ├─ Gia_ManCorrSpecReduce          → pSrm  (SRM AIG, ROs 替换为 PIs)
       ├─ Cbs_ManSolveMiterNc(pSrm)      → vCexStore  ← 反例
       └─ Cec_ManResimulateCounterExamples(pSim, vCexStore, ...)
            └─ while (iStart < |vCexStore|):
                 ├─ Cec_ManStartSimInfo(vSimInfo, nReg)   ← PI 位随机化, RO 位清零
                 ├─ Cec_ManLoadCounterExamples(vSimInfo, vCexStore, iStart)
                 │     └─ 对每条 record: 找一个非冲突 bit-slot, 把 cube literals 写入
                 ├─ Gia_ManCorrPerformRemapping
                 └─ Cec_ManSeqResimulate(pSim, vSimInfo)
```

### 1.2 vCexStore 格式

每条 record:
```
[ iOut, nLits, lit_0, lit_1, ..., lit_{nLits-1} ]
```
- `iOut`: SRM 的输出索引 (用于 dependence 分析, 在 sim path 中只是跳过)
- `nLits`: cube 中 literal 个数
- `lit_i = Abc_Var2Lit(varId, isComplemented)`, `varId` 是 SRM 的 CI 索引 ∈ [0, nReg + nFrames*nPi)

### 1.3 现有 bit-packing 行为 (cecCorr.c:431-498)

`Cec_ManLoadCounterExamplesTry` 已经实现了"一个 word 内多 cube 共存": 对每个 cube, 在 1..nBits-1 的 bit-slot 中找第一个跟 `vPres` (pinned 位掩码) 不冲突的 slot, 写入 cube literals 并更新 `vPres`.

**关键观察**:
- 每个 cube 占用 **恰好 1 个 bit-slot**. 即使有 `nBits-nCexes` 个空 slot 也不会复用.
- 自由位 (cube 不约束的 PI) 在 `Cec_ManStartSimInfo` 已被随机化, 所以"cube + 1 个随机扩展"是隐式发生的.
- 但 SAT 解出的 cube **不一定最小** — Glucose/MiniSat 的默认 partial assignment 包含全部 decision variables, 通常远大于使 property fail 所必需.

### 1.4 量化基线 (待测)

实现前需要在几个标准 benchmark 上 (例如 `bob*`, `intel*`, `pdtvis*` MCNC seq) 采集:

- 每轮 SAT 返回的平均 nLits / 总 CI 数 → cube 紧度
- vCexStore 每轮 record 数
- 每轮 SAT 时间 vs sim 时间占比
- 等价类 lit 数随轮次衰减曲线

这些数字直接决定了改造的上限. **如果 cube 已经很紧 (nLits/nCI < 5%), ternary lifting 收益小**; **如果 record 数 << nBits, 复制收益大**.

---

## 2. 理论基础

### 2.1 Ternary Lifting (Bradley, *Understanding IC3*, SAT 2012)

给定 cube `C` 在电路 `F` 上使输出 `o` 取目标值 `v`, 我们希望找到 `C` 的子集 `C' ⊆ C` 仍然让 `o = v` 在所有 `C' \ C'` 之外的输入扩展上成立.

3-valued (Kleene) 仿真:
- 输入域 `{0, 1, X}`
- AND: `0 ∧ * = 0`, `1 ∧ 1 = 1`, 其他 = X
- NOT: `¬0=1, ¬1=0, ¬X=X`

算法 — 对 cube 中每个 literal `l` 试探:
1. 暂时把 `l` 置 X (其他保持 cube 值)
2. 3-valued sim 整个 fanin cone 至 `o`
3. 若 `o` 仍 = `v` (不是 X), 该 literal 可以丢
4. 否则保留

复杂度: `O(nLits × |fanin cone|)`. 对于典型 SRM (combinational, 几千到几十万 AND), 一次完整 lift 在毫秒量级.

**收益**: 文献和 IC3 实现报告 cube 缩小 2-10×; 在 scorr 场景中 SRM 是组合的且未做窗口化, fanin cone 大, 缩小幅度估计 3-5×.

### 2.2 Cube Replication

设缩小后 cube `C'` 有 `m'` 个 fixed lits, 总 CI 数 `n`. 对 `C'` 的任意扩展 `e ∈ {0,1}^{n-m'}`, `(C', e)` 都是 SRM 的有效反例 (即让某 spec mux 激活).

每条扩展是一个完整的 PI/RO 赋值. 喂给 sequential resim 后, 都会让 `pSim` 在原 AIG 上展开 `nFrames` 帧仿真, 每帧把仿真值传播一次, 检查等价类是否仍然封闭. **不同的随机扩展会在原 AIG 上沿不同轨迹激活不同节点, 因此分裂的等价类对完全不同**.

**收益估算**:
- 复制系数 `K`. 在 64 words = 2048 bits 容量下, 若每轮 SAT 产 50 record, K 可达 ~40.
- 经验上, 等价类细化的边际产出在 K=8~16 时已饱和 (random sim 的 saturate 行为).
- 因此实际取 `K = min(8, nBits/nRecords)` 较合理, 上限设为可调参数 `nReplicate`.

### 2.3 与 SAT-guided sim (rIC3_sim 已有) 的关系

| 时机 | 来源 | 角色 |
|------|------|------|
| 主循环 **前** init 阶段 | `Cec_ManSimClassesSatGuided` (CBS DFS 探索 reachable states) | 主动生成多样化 reachable 状态, 把简单等价类提前消掉 |
| 主循环 **内** 每轮 SAT 后 | (本设计) CEX lifting + replication | 把每个 SAT 反例榨干, 加速归纳收敛 |

**正交**: 前者帮 SAT 少调用 (类已被 sim 排除), 后者帮单次 SAT 多产出. 两者协同, 不冲突.

---

## 3. 数据结构设计

### 3.1 lifted CEX 内存结构

不引入新文件, 复用 `Vec_Int_t` 储存. 对每条原始 record `[iOut, nLits, lits...]`, 产出 lifted record `[iOut, nLits', lits'...]` 其中 `lits'` 是 `lits` 的子集.

输出仍是 `Vec_Int_t`, 格式与 vCexStore 相同, 可以直接喂给 `Cec_ManLoadCounterExamples`.

### 3.2 ternary sim 的 per-node 编码

3-valued 用 2-bit 表示 — 经典做法是双 bit pair `(pVal0, pVal1)`:
- `(0,0)` = 0
- `(1,1)` = 1
- `(1,0)` 或 `(0,1)` 选一种当 X (惯例: `(0,0)` = 0, `(1,1)` = 1, `(1,0)` = X)

但这样 3-valued AND 需要分支. 更紧凑的做法用 packed simulation 的等价 trick:
- `pCare[i]` 1 bit: 节点是否被 cube 约束 (1 = care, 0 = X)
- `pVal[i]` 1 bit: 在 care=1 时的值

3-valued AND:
```
care_out = (care0 & care1) | (care0 & !care0_val) | (care1 & !care1_val)
val_out  = val0 & val1   (only meaningful when care_out=1)
```
即"任一输入是 0 则输出 0 (care)", "都是 1 则输出 1 (care)", 其他 X.

每个 GIA 节点用两个 `int` 数组, 总内存 `2 * nObj * sizeof(int)` = 8 MB / 1M nodes — 接受.

### 3.3 接口设计

新增一个文件 `src/proof/cec/cecCexLift.c`, 暴露:

```c
// In: vCexStore (原 SAT 输出), pSrm (用于 ternary sim).
// Out: 新分配的 Vec_Int_t, 每条 record 已 lift; 调用方负责 free.
// nReplicate: 每条 cube 复制次数 (1 = 不复制, 仅 lift).
extern Vec_Int_t * Cec_ManCexLiftAndReplicate(
    Gia_Man_t * pSrm,
    Vec_Int_t * vCexStore,
    int nReplicate,
    int fVerbose
);
```

声明加到 `cecInt.h`, 注册到 `module.make`.

### 3.4 主循环挂接 (cecCorr.c:1029-1047)

```c
// 现有:
if ( pPars->fUseCSat )
    vCexStore = Cbs_ManSolveMiterNc( pSrm, ... );
else
    vCexStore = Cec_ManSatSolveMiter( pSrm, ... );
Gia_ManStop( pSrm );
...
RetValue = Cec_ManResimulateCounterExamples( pSim, vCexStore, ... );

// 改为 (注意 Gia_ManStop 移到 lift 之后):
if ( pPars->fUseCSat ) ...
else                   ...
if ( pPars->fCexLift && Vec_IntSize(vCexStore) > 0 )
{
    Vec_Int_t * vLifted = Cec_ManCexLiftAndReplicate(
        pSrm, vCexStore, pPars->nCexReplicate, pPars->fVerbose );
    Vec_IntFree( vCexStore );
    vCexStore = vLifted;
}
Gia_ManStop( pSrm );
...
```

新增参数到 `Cec_ParCor_t` (cec.h):
- `int fCexLift;`         默认 0 (向后兼容), 通过 `&scorr -L` 打开
- `int nCexReplicate;`    默认 8, 通过 `&scorr -K <num>` 调整

---

## 4. 算法详细设计

### 4.1 Ternary lift 单条 cube

```
function LiftCube(pSrm, cube_lits, iOut)
    n      = Gia_ManCiNum(pSrm)
    pCare  = calloc(nObj)        // 0 = X
    pVal   = calloc(nObj)
    cube_idx[]                    // 把 lits 按 ciVar 排序进数组以便快速删除

    // 1) Seed: cube 约束的 CI 设 care=1, val=phase
    for lit in cube_lits:
        ci = Gia_ManCi(pSrm, Abc_Lit2Var(lit))
        id = Gia_ObjId(pSrm, ci)
        pCare[id] = 1
        pVal [id] = !Abc_LitIsCompl(lit)
    // 未在 cube 中的 CI: pCare=0 (X), 不需显式设

    // 2) 拓扑序传播至所有 AND
    for each AND obj i in topo order:
        c0,v0 = ApplyEdge(pCare, pVal, fanin0, complC0)
        c1,v1 = ApplyEdge(pCare, pVal, fanin1, complC1)
        // 3-valued AND
        if c0=1 and v0=0:   pCare[i]=1, pVal[i]=0
        elif c1=1 and v1=0: pCare[i]=1, pVal[i]=0
        elif c0=1 and c1=1: pCare[i]=1, pVal[i]=v0&v1
        else:               pCare[i]=0

    // 3) 检查目标 CO
    pOut = Gia_ManCo(pSrm, iOut)
    cOut, vOut = ApplyEdge(pCare, pVal, fanin0(pOut), complC0(pOut))
    assert cOut=1 and vOut=1   // 不变量: 原 cube 必须使 CO=1

    // 4) 一次扫描, 试探每个 cube literal
    for each lit_k in cube_lits:
        ci_id = Gia_ObjId(pSrm, Gia_ManCi(pSrm, Abc_Lit2Var(lit_k)))
        save_care = pCare[ci_id]; pCare[ci_id] = 0    // 暂置 X
        // 局部重传播: 只重算 ci 的 fanout cone
        Repropagate(pSrm, ci_id, pCare, pVal)
        if (cOut=1 and vOut=1 仍成立):
            mark lit_k as droppable
        else:
            pCare[ci_id] = save_care                  // 恢复
            Repropagate(pSrm, ci_id, pCare, pVal)
    return cube_lits 中 droppable=false 的子集
```

### 4.2 局部重传播 (避免每次全图 sim)

`Gia_ManCi` 的 fanout 不是显式存储的 — 标准 GIA 没有 fanout pointer. 三种实现方案:

**方案 A: 全图重传播**
- 每次试探都全图扫一遍 AND
- 复杂度 `O(nLits × nAnd)` — 对 1M-AND, 1000-lit cube 是 `10^9`, 偏慢
- 实现 5 行, 适合原型

**方案 B: 增量 fanout**
- 用 `Gia_ManStaticFanoutStart(pSrm)` 建一次 fanout (在主循环 SAT 解完后)
- 每次试探从 `ci_id` 出发 BFS/DFS fanout 标记 `dirty`, 然后只重算 dirty 节点
- 复杂度 `O(nLits × |fanout cone|)` — 通常小于 5% nAnd, 总 `~5×10^7`
- 但 SRM 每轮重建, fanout 数据每轮也要重建 — 一次性 cost 摊销给同一轮所有 cube

**方案 C: Dual-rail event-driven**
- 维护 worklist, 仅在节点状态改变时入队
- 跟标准 simulator 实现接近
- 复杂度最优但最复杂

**决定**: 一阶段做方案 A (全图重传播), 测出 lifting 时间后若 > 总 sim 10%, 升级到方案 B.

### 4.3 Replication

```
function ReplicateCubes(vLifted, K)
    if K <= 1: return vLifted   // 无操作
    vOut = empty Vec_Int_t
    iStart = 0
    while iStart < |vLifted|:
        record = parse_record(vLifted, iStart)
        for k in 0..K-1:
            append record to vOut    // 同样 record 写 K 次
    return vOut
```

效果: `Cec_ManLoadCounterExamples` 看到 K 倍的 record. 由于每条 record 找的"非冲突 slot"是顺序扫描, K 个相同 record 会写到 K 个不同 slot (除非容量耗尽). 不同 slot 的自由位由 `Cec_ManStartSimInfo` 已经预填了不同随机数.

**重要**: replication 是 cube **副本**, 不是文字相同的 simulation 向量. 自由位的随机化在 `Cec_ManStartSimInfo` 阶段完成, 与 cube 写入是 **正交** 的两个步骤. 这正是该方案 elegant 的地方 — 不需要在 lift 这一层手工生成 random extension.

### 4.4 自适应 K 选择

固定 K 不优. 推荐:
```
K_actual = clamp(nBits / max(nRecords, 1), 1, K_max)
```
其中 `K_max = pPars->nCexReplicate` (默认 8). 这保证容量充足时复制到 8, 容量紧张时退化为不复制.

可以更聪明: 优先复制 cube 大的 record (更紧的约束 → 随机扩展更可能落入未探索区域). 但一阶段先用均匀 K, 实验定位收益后再做加权.

---

## 5. 边界与正确性

### 5.1 不变量

**Lift 后的 cube 仍是合法反例** — 这是 ternary sim 的定义保证: 凡是 ternary sim 输出 = 1 (care) 的, 在所有具体 0/1 扩展下都让真实仿真输出 = 1. 因此 `Cec_ManLoadCounterExamples` 看到的 cube literal 集合 ⊆ 原 cube 集合, 写入 vSimInfo 的位置仍然是有效反例.

**Replication 后的等价类细化语义不变** — `Cec_ManSeqResimulate` 在原 AIG (不是 SRM) 上跑 sequential simulation, 它从 vSimInfo 取 PI/RO 序列, 传播, 验证等价类闭合. 不同的随机扩展只会让某些等价类被分裂得更早或更彻底, **永远不会错误地把不等价的节点判为等价** (sim 是 sound for refinement).

### 5.2 边界条件

| 情况 | 处理 |
|------|------|
| 原 cube nLits = 0 (空 cube, 罕见: SAT 已找到平凡 PI=*) | 跳过, 不 lift, 不 replicate |
| Lift 后 nLits = 0 | 同上, 不写入 — replicate 一份会把整个 word 不变, 浪费 |
| iOut 越界 | 已被 SAT 求解器保证, assert 即可 |
| pSrm 已 free | bug — 必须在 lift 之后才 stop pSrm. 见 §3.4 |
| nReplicate = 1 | 等价于 lift only — 仍然有 cube 紧化收益 |
| nReplicate = 0 / 未启用 | 完全 bypass, 行为同当前 |
| ternary sim 检测到原 cube 让 CO ≠ 1 | bug — assert 失败. 这意味着 SAT 给出不正确 CEX 或 SRM 编码不一致, 需停止主循环排查 |

### 5.3 与 `pPars->fUseCSat` 路径的兼容

`Cbs_ManSolveMiterNc` 和 `Cec_ManSatSolveMiter` 输出格式相同 (vCexStore 同 schema), 因此 lift 模块对两条路径都适用, 不需要分支处理.

### 5.4 与 `pPars->fLatchCorr` 的兼容

latchCorr 模式下 SRM 的 nFrames=0+1=1 (纯 latch correspondence), CI 数较少, lift 收益减少但仍正确. 实验时分别测两种模式.

### 5.5 与 init-state 模式 (`Cec_ManLSCorrespondenceBmc`) 的兼容

`Cec_ManLSCorrespondenceBmc` 调用 `Gia_ManCorrSpecReduceInit` 走 BMC 路径, 共享相同 vCexStore 格式. 第一阶段不动这条路径, 等基础版本验证后再扩展.

---

## 6. 实施里程碑

| 阶段 | 内容 | 验收 |
|------|------|------|
| **M0** | 在 rIC3_sim 当前代码上跑 baseline 实验 (5-10 个 benchmark, 收集 cube 紧度/record 数/SAT 时间占比) | 数据表确认改造方向 |
| **M1** | 新建 `cecCexLift.c`, 实现方案 A 的 ternary lift (无 replicate). 加 `-L` flag. 主循环挂接 | scorr -L 跑通, 输出等价数与无 -L 一致 (sound), 单轮 cube 平均长度下降 ≥ 2× |
| **M2** | 加 replication (K=8), `-K` flag | 同 benchmark 上等价类收敛轮次减少 ≥ 30% |
| **M3** | 自适应 K, verbose 统计 (lift time, drop ratio, slot 利用率) | 整体 wall-clock 提升 1.5-2× (按方向 1 估算的下界) |
| **M4** | 若 lift 时间 > 10%, 升级方案 B (静态 fanout + 局部重传播) | lift 时间 < 5% |
| **M5** | 把 lift 模块也接入 BMC 路径 (`Cec_ManLSCorrespondenceBmc`) 与 `&srm` | 全引擎 ≥ 1.3× |

---

## 7. 实验验证策略

### 7.1 Soundness 回归

- 跑 ABC 自带 `&scorr` regression set (HWMCC seq miter benchmarks)
- 对每条 benchmark, 比较 `&scorr` 和 `&scorr -L -K 8` 的等价 lit 数 — 必须完全一致
- 进一步: `&equiv -C 1000` 或 `&cec` 验证消减后 AIG 与原 AIG 序列等价

### 7.2 性能基准

每个 benchmark 测三组:
- baseline: `&scorr` (rIC3_sim 现状)
- lift only: `&scorr -L`
- lift + replicate: `&scorr -L -K 8`

记录: wall-clock, SAT 调用次数, sim 调用次数, 等价 lit 数收敛曲线.

### 7.3 微观指标

verbose 模式打印:
- 平均 cube 缩小率 `(原 nLits - lifted nLits) / 原 nLits`
- 每 SAT call 平均触发的等价类分裂数
- bit-slot 利用率 (写入了多少 slot vs nBits)
- lift overhead 时间占比

---

## 8. 风险与回退

| 风险 | 缓解 |
|------|------|
| Ternary sim 在大 SRM 上慢 | 先方案 A 测, 慢则 B |
| Replication 让 sim 时间反超 SAT 时间, 总时间退步 | K 自适应, K=1 时只 lift |
| 某些 SAT solver 已经返回最小 cube, lift 无收益 | M0 阶段数据决定是否继续 |
| Lift 引入隐含 bug 让等价类被错误合并 | M1 验收用 `&cec` 严格回归 |
| 与 `fUseRings` 路径交互问题 (rings 加 stop flop, vCexStore 含额外 CI) | 该路径走 `Gia_ManCorrSpecReduce` 同一接口, 不变 |

回退方案: 所有改动通过 `pPars->fCexLift` 控制, 默认关闭. 单一 `git revert <merge-commit>` 即可还原.

---

## 9. 文件改动清单 (实施时)

| 文件 | 改动类型 | 估算行数 |
|------|----------|----------|
| `src/proof/cec/cecCexLift.c` | 新建 | ~250 |
| `src/proof/cec/cecInt.h` | 添加 `Cec_ManCexLiftAndReplicate` 声明 | +1 |
| `src/proof/cec/cec.h` | `Cec_ParCor_t` 加 `fCexLift`, `nCexReplicate` | +2 |
| `src/proof/cec/cecCore.c` | `Cec_ManCorSetDefaultParams` 初始化新字段 | +2 |
| `src/proof/cec/cecCorr.c` | 主循环挂接 lift 调用 (×2: classes 路径 + bmc 路径) | +20 |
| `src/proof/cec/module.make` | 注册 cecCexLift.c | +1 |
| `src/base/abci/abc.c` | `Abc_CommandAbc9Scorr` 加 `-L` `-K` 解析 | +15 |

总改动 < 300 行, 集中, 易 review.

---

## 10. 与方向 1 (PDR 引理注入) 的协同路径

CEX lifting 是方向 2 的独立工作, 但和方向 1 (PDR 风格的 invariant 注入) 在长期路线上互补:
- Lift 让单次 SAT 调用更有信息量 → 在归纳前期收敛更快
- PDR invariant 让 SAT 调用本身更容易 → 后期硬实例上突破

完成 cex_lifting 后, 方向 1 的脚手架 (proof-trace 提取) 可以复用本分支引入的 verbose 统计与 SRM-aware ternary sim 工具.

---

## 附录 A: 为什么不在 SAT 求解器内做 lifting?

可以, 但有两个理由暂不这么做:
1. ABC 有两条 SAT 路径 (`Cbs_ManSolveMiterNc`, `Cec_ManSatSolveMiter`), 改任一都要复制逻辑.
2. 在外部做的好处: 算法独立, 可关闭, 单测容易, 与 rIC3_sim 现有改动隔离.

未来若要在 solver 内做 (利用 implication graph 做 conflict-clause-based lifting), 可作为 M5 之后的工作.

## 附录 B: 与 IC3 generalize 的差别

IC3 的 `generalize` 在 SAT-based 检查的同时跑 ternary sim, 同时还做 induction-relative tightening (clause c 在 R_{i-1} 下是 inductive 的就保留). 我们这里只做"当前帧 ternary lift", 不做 induction-relative 的子句强化 — 那个属于方向 1 的范畴.
