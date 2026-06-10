# Failed-endpoint TFO `new2` 实验结果与原因分析

分支：`incre_sim_seed`

对比日志：

- `hard_scorr_logs_v_w_i`：启用 proof incremental `-i`，未启用 simulation incremental `-I`
- `hard_scorr_logs_v_w_i_I_new`：旧版 `-I`，local TFO 阈值为 20%
- `hard_scorr_logs_v_w_i_I_new2`：新版 `-I`，local TFO 阈值为 60%，并包含低风险实现优化

本文只分析四个 ILA case 的主 `&scorr` refinement loop。日志中的
`[prof ALL]` 不包含 BMC 和命令外围开销；`_summary.tsv` 的 `wall_s`
是完整命令时间。

## 1. 结论

`new2` 的性能收益成立，而且非常显著：

- 四个 case 的完整 wall time 从无 `-I` 的 `492.39 s` 降到
  `230.86 s`，下降约 `53.1%`。
- 相比旧 `new`，从 `396.73 s` 降到 `230.86 s`，下降约 `41.8%`。
- 主循环 simulation 时间相比无 `-I` 下降约 `69.4%`。
- 主循环 SAT 时间相比无 `-I` 下降约 `58.1%`。
- 相比旧 `new`，SAT 调用数下降约 `15.0%`，平均单次 solve 时间下降约
  `48.9%`。

但 `new2` 不只是把同一个 simulation kernel 写得更快。最重要的变化是
local/full 阈值从 20% 提高到 60%，它把大量原本走 full CEX replay 的
batch 改成了 failed-endpoint cut-point simulation。因此它改变了
equivalence class 的 refinement 路径，必然会影响：

- 后续 SRM 中有哪些 pairs；
- SAT 调用数量和每次调用难度；
- 总迭代轮数；
- 最终 class partition、representative 和 ring 顺序；
- 最终化简电路大小。

四个 case 的最终 `NEnd` 都不优于无 `-I` baseline，其中三个 case
增大约 `0.25%`。最可能的核心原因不是“少做 simulation”，而是当前
local path 使用了一个混合 pattern：

```text
本轮 SAT/SRM endpoint 值 + 持久化表中旧的 side-input 值
```

这个 pattern 不一定对应原始 AIG 的任何完整输入轨迹。它可能比合法 CEX
更容易拆 class，但也可能拆掉真实等价、原本可以保留用于化简的节点。
class split 是不可逆的，因此这种更激进的 refinement 可以同时造成：

- 前几轮 `dSimLits` 更多；
- 后续 SAT 更少或更容易；
- 迭代更早收敛；
- 最终电路反而更大。

## 2. 总体数据

四个 ILA case 汇总：

| 模式 | 完整 wall | 主循环 wall | Sim | SAT | SAT calls | 平均 solve | 末轮编号合计 | dSimLits | local/full batches | pending |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 无 `-I` | 492.39 s | 436.71 s | 152.77 s | 215.18 s | 7,591,719 | 27.69 us | 512 | 3,790,910 | - | - |
| `new` | 396.73 s | 344.96 s | 84.39 s | 204.70 s | 7,047,276 | 28.46 us | 418 | 3,745,233 | 477/151 | 458,054 |
| `new2` | 230.86 s | 181.26 s | 46.73 s | 90.10 s | 5,992,811 | 14.54 us | 362 | 3,791,760 | 509/4 | 3,150 |

这里的“平均 solve”使用 `[prof ALL]` 中的 `slv / n`，不包含 solver
setup。`dSimLits` 是 simulation 前后 `Gia_ManEquivCountLitsAll()` 的
差值，更接近“删除了多少 representative links”，不是所有无序 pair
组合的数量。

### `new` 到 `new2` 的逐 case 变化

| Case | 末轮编号 | SAT calls | 平均 solve | SAT 时间 | Sim 时间 | NEnd 变化 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| BGEU | 102 -> 84 | 1,947,454 -> 1,265,682 | 22.90 -> 14.53 us | 45.52 -> 19.00 s | 19.93 -> 11.46 s | +1,762 |
| BLT | 84 -> 96 | 1,700,233 -> 1,785,191 | 33.50 -> 12.78 us | 57.74 -> 23.55 s | 19.01 -> 12.13 s | +3,732 |
| SRAI | 123 -> 101 | 1,722,869 -> 1,722,681 | 22.51 -> 12.31 us | 39.91 -> 22.19 s | 23.42 -> 12.20 s | +2,057 |
| XORI | 109 -> 81 | 1,676,720 -> 1,219,257 | 35.94 -> 20.28 us | 61.53 -> 25.35 s | 22.03 -> 10.94 s | +1,567 |

这张表说明：

1. SAT calls 不是稳定地下降。BLT 增加约 5%，SRAI 几乎不变。
2. 稳定变化是平均单次 solve 明显变轻。
3. 迭代数也不是由 simulation 时间直接决定。BLT 相比旧 `new`
   反而多了 12 轮，但总时间仍大幅下降。

因此“SAT 变快”必须拆成两个原因：

- 一部分 case 确实减少了调用；
- 所有 case 的平均求解难度都明显下降。

## 3. SAT 返回 SAT 到底证明了什么

“solver 返回 SAT，所以一定存在一个输入”这句话本身正确，但要区分
三个对象：

1. 存在一个赋值 `alpha`，使当前构造的 speculative SRM output 为 1。
2. `vOutVals` 是 SRM 内部 `vOutLits` 在 `alpha` 下的值。
3. 原始未 speculative-reduce 的 AIG endpoint 在同一个 `alpha` 下，
   是否一定具有相同值。

代码严格保证 1 和 2，不自动保证 3。

### 3.1 endpoint literal 仍包含 transitive speculative reduction

`Gia_ManCorrSpecReduce()` 用 `Gia_ManCorrSpecReal()` 构造
`iPrevRaw/iObjRaw`，并把它们放入 `vOutLits`：

- `src/proof/cec/cecCorr.c:276-287`
- `src/proof/cec/cecCorr.c:319-330`

`Gia_ManCorrSpecReal()` 不直接用 representative 替换 endpoint 自身，
但它对 endpoint 的 fanins 调用了 `Gia_ManCorrSpecReduce_rec()`：

- `src/proof/cec/cecCorr.c:161-177`

而 `Gia_ManCorrSpecReduce_rec()` 会在 fanin 有 representative 时直接
替换：

- `src/proof/cec/cecCorr.c:197-202`

因此 `vOutVals` 是“SRM 中 endpoint copy”的值。该 copy 的 transitive
fanin 中仍可能包含 speculative representative substitution。

一个简单例子：

```text
原始 AIG： endpoint e = x & s
当前 speculative class 假设：x == r
SRM 中：   e_srm = r & s
```

SAT 找到的 `alpha` 可以严格满足 SRM，并给出 `e_srm(alpha)`。但如果
`x(alpha) != r(alpha)`，原始 AIG 中的 `e(alpha)` 就不一定等于
`e_srm(alpha)`。

这正是 speculative refinement 的正常语义：一个 SRM output SAT，
可能首先说明它的上游某个 speculative assumption 错了，不保证把同一个
CI assignment 回放到原始 AIG 后，当前 queried pair 会立刻拆开。

### 3.2 local path 没有使用该 SAT model 的完整 side inputs

这是当前实现中更直接的差异。

`Cec_ManLoadCounterExamplesMapped()` 会把 CEX literals 装入
`vSimInfo`，并记录 `(Out, bit)`：

- `src/proof/cec/cecCorr.c:643-676`

但是 local 成功时，`Cec_ManResimulateCounterExamples()` 在
`Cec_SeedSimTryBatch()` 后立即 `continue`：

- `src/proof/cec/cecCorr.c:809-818`

只有 fallback 才会执行：

- `Gia_ManCorrPerformRemapping()`
- `Cec_ManSeqResimulateSeed()`

见 `src/proof/cec/cecCorr.c:836-849`。

local path 实际只从 `vOutVals` 取两个 endpoint 值，写入持久化
`pVal`：

- `src/proof/cec/cecCorrIncrSim.c:187-210`

然后把这些 endpoint 标成 authoritative seed，跳过从原始 fanin
重新计算：

- `src/proof/cec/cecCorrIncrSim.c:251-265`

endpoint TFO 中每个 gate 的其他 fanin，则直接读取持久化 `pVal`：

- `src/proof/cec/cecCorrIncrSim.c:61-81`

所以某一 bit lane 的实际语义是：

```text
endpoint = 本轮 SRM model alpha 的值
side input = 持久化表中旧 pattern beta 的值
downstream = endpoint(alpha) 与 side(beta) 的组合
```

即使 endpoint 值本身能在原始 AIG 的某个输入下实现，也不能推出
`endpoint(alpha) + side(beta)` 这个组合能由同一个完整输入实现。

因此，用户前提中的“SAT 输入存在”是成立的，但当前 local simulation
并没有完整使用这个输入。它只取了 endpoint 值，并把它与旧 side
context 重新组合。

## 4. 为什么单轮 simulation 明显变快

### 4.1 60% 阈值改变了实际执行算法

四个 `new2` case 的：

```text
maxdirty / keys ~= 2.62M / 6.43M ~= 40.8%
```

旧 `new` 的阈值是 20%，所以这些约 41% 的 cone 会 fallback 到 full
simulation。`new2` 的阈值是 60%，所以它们改走 local simulation。

这解释了 batch 统计的巨大变化：

```text
new : local/full = 477/151
new2: local/full = 509/4
```

`new2` 的四次 full 全部是每个 case 第一次建立 persistent table 的
必要 full sweep。之后基本全部走 local。

因此主要收益是：

- full path：扫描全部 unrolled AIG；
- local path：只排序、计算和 refine dirty endpoint TFO；
- 当前最大 dirty cone 约占全图 41%，明显低于 full sweep。

### 4.2 低风险实现优化降低固定开销

除了阈值外，commit `56de9febc` 还包含：

- 复用 `vSimInfo`；
- local 成功时延迟 `Gia_ManCreateValueRefs()` 和 remapping；
- full fallback 在标准 sweep 中直接保存 persistent `pVal`，不再另做
  一次全图重算；
- TFO 超过阈值时提前终止 BFS；
- 删除未使用的 seed vector。

这些优化本身不应改变 class refinement 结果。它们主要解释：

```text
new2 四 case 的 sim remap 总时间约 0.094 s
无 -I baseline 的 sim remap 总时间约 2.398 s
```

但它们不能单独解释 SAT calls、迭代数和 `NEnd` 的明显变化。后面三者
主要来自 20% -> 60% 后大量 batch 从 full replay 切换成 local
endpoint-cut simulation。

## 5. 为什么 SAT 调用更轻

### 5.1 先看已确认的事实

相比旧 `new`：

```text
SAT calls:       7.047M -> 5.993M，下降 15.0%
平均 solve:      28.46 us -> 14.54 us，下降 48.9%
SAT 总时间:      204.70 s -> 90.10 s，下降 56.0%
real CEX:        3.374M -> 2.311M
dSimLits / CEX:  约 1.11 -> 约 1.64
```

`dSimLits / CEX` 不是严格的 pair 效率，但足以说明：`new2` 中每个 real
CEX 平均引起了更多 class-link refinement。

### 5.2 class 提前变化会反馈到 proof incremental

proof-side `-i` 每轮会：

1. 比较当前 class/representative 与上一轮 snapshot；
2. 把 representative 变化的节点作为 seeds；
3. 计算这些 seeds 的 TFO；
4. 只为 active TFO pairs 和新 ring edges 构造 SRM outputs。

对应代码：

- `src/proof/cec/cecCorrIncr.c:106-147`
- `src/proof/cec/cecCorrIncr.c:312-379`
- `src/proof/cec/cecCorrIncr.c:384-399`

所以 simulation 不是 SAT 之后的独立耗时模块。它改变 class 后，会直接
改变下一轮：

- active pairs 数量；
- ring edge 顺序；
- SRM outputs；
- 每个 SAT cone 的结构；
- 哪些困难候选还需要 solver。

`new2` 的 endpoint-cut pattern 在前期更激进地拆 class，后续 solver
面对的是另一条 refinement 轨迹。更早删除候选 links，尤其是删除原本
需要较深证明的 links，会同时减少一部分 calls 并显著降低平均 solve
难度。

这里“SRM 更小/更局部、更少困难 pairs”是根据日志和调度代码作出的
推断。当前 profile 没有记录每轮 SRM AND 数、cone size 和 solve
分位数，不能仅凭总时间进一步区分它们各自的贡献。

### 5.3 为什么 BLT calls 增加仍然更快

BLT 从旧 `new` 到 `new2`：

```text
calls:       1.700M -> 1.785M
平均 solve:  33.50 us -> 12.78 us
SAT 时间:    57.74 s -> 23.55 s
```

这说明真正稳定的收益是“调用变轻”，不是“调用一定变少”。BLT 的
class/ring 轨迹生成了更多 active proof requests，但每个 request
显著容易，因此总 SAT 时间仍下降约 59%。

## 6. 为什么迭代轮数减少

相比无 `-I`，四个 case 的末轮编号都减少：

| Case | 无 `-I` | `new2` |
| --- | ---: | ---: |
| BGEU | 127 | 84 |
| BLT | 129 | 96 |
| SRAI | 125 | 101 |
| XORI | 131 | 81 |

原因不是“单轮 simulation 运行得快，所以算法少跑几轮”。运行时间不会
改变停止条件。

真正原因是 simulation 的输出 class partition 变了：

1. endpoint-cut local sim 在前几轮一次拆掉更多 representative links；
2. 下一轮 proof incremental 看到更大的 class delta；
3. active TFO 和 ring edges 随之改变；
4. 大批候选更早离开后续 SRM；
5. 算法更早进入只剩少量 active pairs 的尾部阶段。

这是一条 algorithmic feedback loop：

```text
更激进的 local refinement
  -> 下一轮 class/ring/SRM 改变
  -> SAT requests 更容易或更少
  -> 新 CEX 集合改变
  -> 更早收敛
```

它也解释了为什么旧 `new` 到 `new2` 不是每个 case 都减少轮数。BLT
从 84 增加到 96，说明 class/ring 路径变化可以让收敛提前，也可以生成
更多中间 active edges；最终效果取决于具体网络。

## 7. 为什么前几轮 `dSimLits` 更多

BGEU 前六轮是最清楚的例子：

| Round | 无 `-I` dSim | `new2` dSim |
| --- | ---: | ---: |
| 1 | 2,206 | 2,206 |
| 2 | 691 | 1,409 |
| 3 | 1,061 | 24,833 |
| 4 | 51,285 | 42,776 |
| 5 | 31,799 | 287,957 |
| 6 | 245,964 | 254,150 |
| 前六轮累计 | 333,006 | 613,331 |

第一轮完全相同，因为 `new2` 必须先做一次 full sweep 初始化 persistent
table。从第二轮开始走 local，差异立即出现。到第六轮，`new2` 已经把
baseline 后续几轮的大量 refinement 提前完成。

### 7.1 不是尝试了更多 bit patterns

`new2` 没有增加 `nWords`，也没有增加 bit-lane 数量。CEX packing 逻辑
仍然是把多个 CEX 放入已有 simulation words：

- `src/proof/cec/cecCorr.c:597-629`
- `src/proof/cec/cecCorr.c:643-676`

endpoint 之后的 TFO 计算仍是普通位并行运算：一个机器字同时计算多个
lanes。它提高的是每个 lane 的针对性，不是 lane 数量。

### 7.2 它是更强、更激进的启发式

full replay 的一个 lane 表示一个合法的完整输入 completion，然后从
CIs 经过原始 AIG 传播。

local path 直接把 SAT 给出的 endpoint 值写入这个 lane，并跳过 endpoint
的原始 IFO。这样 queried failed pair 在该 lane 中更容易被强制表现为
不同，随后这个差异在 endpoint TFO 中位并行传播。一个 endpoint lane
可以同时触碰并拆分许多 downstream classes。

此外，它把 endpoint 的新值与 persistent side context 重新组合。这相当
于一种 internal cut-point perturbation，可能产生比合法 CEX replay
更有区分力的 pattern。

因此准确表述不是“尝试了更多可能”，而是：

> 使用同样数量的 bit lanes，但每个 lane 直接在 failed endpoint 注入
> 差异，并与旧 side context 组合，所以单位 lane 的 class-splitting
> 强度更高。

这可以称为更强的启发式，但不能直接称为更好的启发式，因为它同时带来
化简质量损失。

## 8. 为什么最终优化结果退化

### 8.1 数据

`new2` 相比无 `-I`：

| Case | baseline NEnd | `new2` NEnd | 增量 | 相对增量 |
| --- | ---: | ---: | ---: | ---: |
| BGEU | 1,402,615 | 1,406,047 | +3,432 | +0.245% |
| BLT | 1,406,690 | 1,407,027 | +337 | +0.024% |
| SRAI | 1,408,410 | 1,412,365 | +3,955 | +0.281% |
| XORI | 1,413,808 | 1,417,380 | +3,572 | +0.253% |

这属于 reduction quality 退化，不等于已经发现功能正确性错误。
simulation 把真实等价节点过早拆开，通常只会让最终电路更大，而不会把
不等价节点错误合并。

### 8.2 最可能的主因：hybrid pattern 造成 over-refinement

当前 local pattern 可能同时存在两层不一致：

1. endpoint 值来自 speculative SRM，不一定等于原始 AIG endpoint 在
   同一个 CI assignment 下的值；
2. downstream side inputs 来自 persistent old pattern，不是本轮 SAT
   assignment。

如果两个节点只在原始 AIG 的合法输入空间内等价，一个不可达的 internal
cut-point 组合仍可能让它们的 simulation signatures 不同。

`Cec_SeedSimRefineClass()` 一旦发现 signatures 不同，就立即重建 class：

- `src/proof/cec/cecCorrIncrSim.c:281-302`

后续流程只有 split，没有 merge。因此这类 over-refinement 不会被 SAT
“修回来”，而会直接减少最终可合并节点数。

### 8.3 `dSimLits` 更多不代表最终电路更好

四个 case 汇总：

```text
无 -I dSimLits: 3,790,910
new2 dSimLits:  3,791,760
```

总量只差 850，几乎相同，但 `NEnd` 仍稳定变大。这说明最终质量取决于：

- 拆的是哪些 links；
- 哪些 true equivalences 被保留；
- class representative 的选择；
- ring 的邻接顺序；
- 后续 proof incremental 走过的路径；
- 最终 reduction/hash 能利用多少结构共享。

所以不能用总 `dSimLits` 判断化简效果。更多 split 从 verification
refinement 角度可能更快收敛，但从 reduction 角度通常意味着保留的
等价关系更少。

### 8.4 更少 full replay 是次要影响

`new2` 只有第一次 full sweep，后续不再持续用完整 CEX/random completion
刷新所有节点。即使不考虑不可达 hybrid pattern，这也会改变 simulation
signature、class representative 和 ring path。

这不是本文解释性能收益的主因，但它会放大最终 `NEnd` 的路径依赖。

## 9. 如何理解 `pending`

`new2` 四个 case 的总 pending 为：

```text
806 + 784 + 756 + 804 = 3,150
```

这些全部出现在每个 case 的第一次 full sweep；后续 local rounds 的
pending 基本为 0。

这不能解释成“local 已证明 endpoint 值一定是原始 AIG 可实现的”。
local 直接把 `vOutVals` 写入 queried endpoints，并把这些 endpoints
标成 authoritative，因此 queried pair 在该 lane 被拆开是设计结果，
`pending=0` 接近构造性保证。

相反，第一次使用合法 full CEX replay 时仍有数百 pending，至少说明：

- SRM output SAT 不等于 queried original pair 必须在本轮 full replay
  中立即拆开；
- speculative refinement 可能先拆上游 assumption；
- endpoint direct injection 与 full replay 的语义确实不同。

## 10. 当前实现的准确定位

当前 `-I` 不是“对同一个完整 CEX 做等价的局部求值”，而是：

> 用 SAT/SRM endpoint model value 作为内部 cut-point mutation，在
> persistent side context 上只传播 failed-endpoint TFO，并据此做
> conservative class refinement。

它的优点：

- simulation 计算量小；
- failed pair 几乎不会 pending；
- 每个 CEX lane 的 downstream splitting 能力强；
- 能显著降低迭代数和 SAT 难度。

它的代价：

- local lane 不一定是原始 AIG 的合法完整 trace；
- 可能 over-refine true equivalences；
- 最终 reduction quality 可能下降；
- threshold 会成为性能与质量之间的算法参数，而不只是性能参数。

## 11. 建议增加的 profiling

为了把以上“最可能原因”变成可量化结论，后续实验应优先增加以下仅测试
模式，不进入正式 timing：

### 11.1 endpoint replay mismatch

对每个 SAT CEX：

1. 用保存的 CI assignment 回放原始 unrolled AIG；
2. 读取原始 endpoint values；
3. 与当前 `vOutVals` 比较；
4. 统计 pair-level 和 endpoint-level mismatch。

这个指标直接验证：

```text
SRM endpoint model value == original endpoint replay value ?
```

### 11.2 side-context mismatch

对 local batch 中每个 `(Out, bit)`：

1. 找出 endpoint TFO 的 boundary side fanins；
2. 比较 persistent `pVal` 与本轮完整 CEX replay 的值；
3. 统计有多少 dirty gates 使用了不同 assignment 的 side input。

这个指标验证当前 hybrid pattern 的实际比例。

### 11.3 local-only refinement

从同一份 class snapshot 分叉：

- 一份运行当前 local endpoint-cut simulation；
- 一份运行标准 full CEX replay；
- 比较 `local-only`、`full-only` 和共同 split links。

如果 `local-only` 很多且最终 `NEnd` 同步变大，就能直接确认 aggressive
over-refinement 与 reduction quality 的关系。

### 11.4 SAT hardness

每轮额外记录：

- SRM POs；
- SRM ANDs；
- active pairs；
- solve time 的 P50/P95/P99；
- timeout 数；
- 每个 CEX 后删除的 links 数。

这样可以区分 SAT 变轻究竟主要来自：

- SRM 规模更小；
- proof cone 更浅；
- 困难 pairs 被 simulation 提前删除；
- ring/path 改变。

## 12. 下一轮阈值实验应如何解读

建议比较：

```text
full baseline, 20%, 40%, 60%
```

每个阈值同时观察四组指标：

1. 性能：wall、Sim、SAT、平均 solve；
2. 收敛：迭代数、SAT calls、real CEX；
3. refinement：dSimLits、pending、local/full、local-only splits；
4. 质量：NEnd、REnd、gain。

如果阈值升高时出现：

```text
Sim/SAT/iterations 持续下降
NEnd 持续上升
endpoint/side mismatch 和 local-only splits 持续上升
```

就可以确认当前优化本质上是在用更激进的 internal cut-point heuristic
换取运行时间，而不是对 full CEX simulation 做结果等价的增量计算。

