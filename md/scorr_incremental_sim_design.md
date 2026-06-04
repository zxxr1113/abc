# &scorr 增量 Simulation 设计文档

## 0. 背景与目标

本文档讨论 `&scorr` 中 SAT 失败后 resimulation 的增量化设计。重点不是修改 SRM/SAT 主体，而是在保留当前 `skip failed-only simulation` 优化的基础上，设计一个真正的局部 guided simulation，避免每次都对完整原始 AIG 做全图模拟。

### 当前分支背景

当前工作分支相对 ABC `master` 已经做了两类相关改动：

- `-i` active SRM：只构造和求解受近期 class 变化影响的 SRM outputs。
- fail-only skip：如果 `vCexStore` 里只有 timeout/fail，没有真实 CEX pattern，则跳过失败后的 resimulation。

### 本文档目标

1. 明确 master 中原始 simulation 行为。
2. 明确当前 fail-only skip 的数学合理性。
3. 给出一个不走全图模拟的真正 incremental guided simulation 方案。
4. 给出数据结构、控制流、正确性边界和验证计划。

### 非目标

- 不设计动态可删改 SRM manager。
- 不设计跨 iteration 的 SAT solver 复用。
- 不追求完全复现 master 中随机 filler 带来的 opportunistic split。
- 不在第一版中重写 `Cec_ManSim_t` 的全部 memory manager。

## 1. 与 master 的行为对比

### 1.1 master 的主 loop 行为

ABC `master` 中，主 refinement loop 的逻辑是：

```c
vCexStore = Cbs_ManSolveMiterNc( pSrm, ... );

if ( Vec_IntSize(vCexStore) == 0 )
    break;

RetValue = Cec_ManResimulateCounterExamples( pSim, vCexStore, ... );
Gia_ManCheckRefinements( pAig, vStatus, vOutputs, pSim, ... );
```

也就是说，master 只判断 `vCexStore` 是否为空。只要不为空，就会调用 `Cec_ManResimulateCounterExamples()`。

这导致三种情况：

| SAT/SRM 结果 | `vCexStore` | master 是否 resim | resim 信息来源 |
| --- | --- | --- | --- |
| 全部 UNSAT | 空 | 否 | 无 |
| 存在 SAT CEX | 非空 | 是 | SAT CEX + 随机 filler |
| 只有 timeout/fail | 非空 | 是 | 只有随机 filler |

### 1.2 当前分支的 fail-only skip

当前分支新增了 `Cec_ManCexStoreHasPattern()`。它扫描 `vCexStore`，只有发现 `nSize >= 0` 的条目才认为存在可用于 guided simulation 的 pattern。

timeout/fail 在 `vCexStore` 中编码为：

```text
Out, -1
```

没有任何输入赋值。因此 timeout-only 情况下，master 的 resimulation 实际上不是 guided simulation，而是额外做了一轮全图随机 simulation。

当前分支改成：

```c
if ( Cec_ManCexStoreHasPattern(vCexStore) )
    Cec_ManResimulateCounterExamples(...);

Gia_ManCheckRefinements(...);
```

这是合理的第一层优化：没有 CEX pattern 时，不做没有新信息的全图模拟，但仍然保留 timeout pair 的保守处理。

## 2. 现有 Simulation 的操作原理

### 2.1 初始随机 simulation

初始 class refinement 使用 `Cec_ManSimClassesRefine()`。它反复调用：

```c
Cec_ManSimCreateInfo( p, p->vCiSimInfo, p->vCoSimInfo );
Cec_ManSimSimulateRound( p, p->vCiSimInfo, p->vCoSimInfo );
```

`Cec_ManSimCreateInfo()` 给 PI 填随机 word。如果已有 `pAig->vSimsPi`，则使用外部 set source 提供的 simulation information。

数学上，每个节点 `x` 得到一个 bit-vector signature：

```text
S(x) = x 在一批 packed patterns 下的取值
```

如果同一个 equivalence class 中两个节点 `a` 和 `b` 满足：

```text
S(a) != S(b)
```

则存在某个具体 pattern 使 `a != b`，因此该等价关系被 disproved，可以 sound 地 split class。

### 2.2 SAT CEX guided simulation

SRM 阶段的 SAT solver 对每个 SRM output 求解。对 SAT 的 output，solver 保存一个 CEX 到 `vCexStore`：

```text
Out, nLits, lit0, lit1, ..., lit(nLits-1)
```

其中：

- `Out` 是 SRM PO 编号，对应 `vOutputs[2*Out]` 和 `vOutputs[2*Out+1]` 中的一对原始 AIG endpoints。
- `nLits > 0` 表示真实 CEX。
- `nLits == 0` 表示 trivial SAT，例如 SRM PO 已经化成常 1。
- `nLits == -1` 表示 timeout/fail，没有 CEX。

真实 CEX 不是完整输入向量，而是 SRM output TFI 中相关 CI 的稀疏赋值。`Cec_ManLoadCounterExamples()` 将多个 CEX packed 到 `vSimInfo` 的不同 bit lanes 中。

然后 `Cec_ManSeqResimulate()` 在原始 `pAig` 上逐 frame 模拟。注意：这里模拟对象不是 SRM，而是原始 AIG。这样同一个 SAT CEX 不只可以打破产生它的 pair，也可能顺便打破同一原始 AIG 中其他 class。

### 2.3 timeout-only simulation 的数学意义

timeout-only store 中没有任何 CEX literal：

```text
Out0, -1, Out1, -1, ...
```

如果此时仍调用 `Cec_ManResimulateCounterExamples()`：

1. `Cec_ManStartSimInfo()` 会随机初始化 PI/timeframe slots。
2. `Cec_ManLoadCounterExamples()` 遇到 `nSize <= 0` 直接跳过。
3. 后续 `Cec_ManSeqResimulate()` 只是用随机 filler 全图模拟。

因此 timeout-only resim 不是 guided simulation。它只是额外随机搜索。对于已经经过初始随机模拟、且当前 iteration 只产生 timeout/fail 的情况，这个额外随机 pass 的边际价值通常很低。

## 3. 设计原则

### 3.1 保留 fail-only skip

第一条规则：

```text
如果本轮没有真实 CEX pattern，不做 resimulation。
```

仍然需要执行 `Gia_ManCheckRefinements()`，因为 timeout/fail pair 要保守地从 class 中移除，避免保留未证明的 equivalence。

### 3.2 guided CEX 是唯一增量 simulation 源

真正增量 simulation 只处理来自 SAT 的新增 CEX lanes。

不把未赋值 PI 随机填满，因为随机 filler 会让大量 PI 成为潜在变化源，局部 TFO 很容易退化成全图 TFO。第一版应采用确定性补全：

```text
未出现在 CEX 中的 SRM CI = 0
出现在 CEX 中的 SRM CI = SAT model 给出的值
```

这样 simulation 只反映 SAT CEX 提供的新信息。

### 3.3 simulation 对象仍然是原始 pAig

不要在小 SRM 上做 simulation。小 SRM 只包含本轮 active pair 的 proof outputs，无法复用 CEX 去 refine 原始 AIG 中其他可能被同一 pattern 打破的 classes。

正确对象是：

```text
SRM/SAT on active pSrm
CEX projected back to original pAig CIs
local/event-driven resimulation on original pAig
refine original pAig->pReprs/pNexts
```

## 4. 顶层算法

### 4.1 主循环替换点

当前主 loop 中这段：

```c
if ( Cec_ManCexStoreHasPattern(vCexStore) )
{
    RetValue = Cec_ManResimulateCounterExamples( pSim, vCexStore, ... );
}
Gia_ManCheckRefinements( pAig, vStatus, vOutputs, pSim, ... );
```

替换为：

```c
Cec_CexStoreClassify( vCexStore, &nRealCex, &nTrivCex, &nTimeout );

if ( nRealCex == 0 && nTrivCex == 0 )
{
    // fail-only: no guided information
    // skip resim
}
else if ( use_incremental_sim )
{
    Cec_ManIncrResimulateCounterExamples( pIncrSim, pSim, vCexStore, vOutputs, vStatus, nFrames );
}
else
{
    Cec_ManResimulateCounterExamples( pSim, vCexStore, nFrames );
}

Gia_ManCheckRefinements( pAig, vStatus, vOutputs, pSim, fRings );
```

### 4.2 CEX store 分类

新增 helper：

```c
typedef struct Cec_CexStoreStats_t_
{
    int nRealCex;    // nLits > 0
    int nTrivCex;    // nLits == 0
    int nTimeout;    // nLits == -1
} Cec_CexStoreStats_t;
```

扫描规则：

```text
for each entry:
    read Out
    read nLits
    if nLits > 0:  nRealCex++
    if nLits == 0: nTrivCex++
    if nLits == -1: nTimeout++
```

注意：`nLits == 0` 不能简单归入 timeout。它表示 trivial SAT，仍然是一个真实 disproval，但没有 CEX literals 可注入。它应该走 direct split 或全图 fallback，而不是被当成 fail-only 跳过。

## 5. 增量 Simulation Manager

### 5.1 数据结构

新增文件建议：

```text
src/proof/cec/cecCorrIncrSim.c
```

新增 manager：

```c
typedef struct Cec_IncrSim_t_ Cec_IncrSim_t;
struct Cec_IncrSim_t_
{
    Gia_Man_t * pAig;
    int         nObjs;
    int         nPis;
    int         nRegs;
    int         nFrames;
    int         nWords;

    // Sparse sim storage. Key = frame * nObjs + objId.
    int *       pSimOff;       // size nFrames * nObjs, -1 means default phase vector
    Vec_Int_t * vTouched;      // keys whose pSimOff was set
    Vec_Int_t * vSimData;      // stores nWords unsigned words per touched key

    // Event traversal.
    int *       pMark;         // timestamp mark for frame/object dirty
    int         nMark;
    Vec_Int_t * vQueue;
    Vec_Int_t * vDirtyObjs;    // keys in topological/frame order

    // Class refinement.
    int *       pRootMark;
    int         nRootMark;
    Vec_Int_t * vDirtyRoots;
    Vec_Int_t * vClassOld;
    Vec_Int_t * vClassNew;
    Vec_Int_t * vClassTemp;

    // Temporary words for default signatures.
    unsigned *  pTemp0;
    unsigned *  pTemp1;
};
```

第一版可以使用 sparse `pSimOff + vSimData`，避免 dense `nFrames * nObjs * nWords` 内存。`pSimOff` 是 dense int array，但只保存 offset；真实 simulation words 只为 touched nodes 分配。

### 5.2 frame/object key

```c
static inline int Cec_IncrSimKey( Cec_IncrSim_t * p, int f, int Obj )
{
    return f * p->nObjs + Obj;
}
```

假设 `nFrames * nObjs` fits in signed int。对于极大 case，可以改成 `Vec_Wrd_t` key，但 `&scorr` 默认 frame 数很小，第一版用 int 简单且符合 ABC 风格。

## 6. CEX 注入与 source 计算

### 6.1 SRM CI 到原始 AIG source 的映射

`Cec_ManResimulateCounterExamples()` 中 `vSimInfo` 的布局是：

```text
[initial ROs] [frame0 PIs] [frame1 PIs] ... [frameK PIs]
```

因此 CEX literal 的 variable 映射为：

```text
var < nRegs:
    frame = 0
    obj   = Gia_ManRo(pAig, var)

var >= nRegs:
    t     = var - nRegs
    frame = t / nPis
    pi    = t % nPis
    obj   = Gia_ManPi(pAig, pi)
```

literal 的值：

```text
value = !Abc_LitIsCompl(lit)
```

如果采用 all-zero deterministic completion，则只有 `value == 1` 的 source 与默认 0 pattern 不同，需要成为 event source。`value == 0` 的 literal 仍然是 CEX 的一部分，但它不产生从 0 baseline 出发的 value change。

### 6.2 bit lane 组织

保留 bit 0 作为 all-zero baseline pattern。真实 CEX 从 bit 1 开始 packed：

```text
bit 0: all-zero source
bit 1..M: SAT CEX lanes
```

如果一轮 CEX 数量超过 `32 * nWords - 1`，分 batch 处理。每个 batch 独立进行 local simulation 和 class refinement。

### 6.3 trivial SAT

`nLits == 0` 没有 source。它通常表示 SRM output 已经常 1。这种情况下局部 simulation 没有可传播事件，必须直接处理对应 pair：

```text
if status == SAT and nLits == 0:
    direct split corresponding vOutputs pair
```

如果不 direct split，会丢失这个真实 disproval。

## 7. 局部 TFO 事件传播

### 7.1 事件传播规则

对每个 source `(frame, obj, laneMask)`：

1. 写入该 source 的 local sim word。
2. 如果该 source vector 不同于默认 phase vector，则加入 queue。
3. 从 queue 中取 `(frame, obj)`。
4. 遍历 static fanouts：
   - fanout 是 AND：同 frame 重新计算。
   - fanout 是 RI：计算 RI 值；如果 frame + 1 < nFrames，将对应 RO 作为下一 frame source。
   - fanout 是 PO：可计算输出用于 bug check，但对 class refinement 通常不是 candidate。
5. 如果 fanout 新 value 与旧/default value 相同，不继续传播。
6. 如果不同，标记 fanout dirty 并入队。

### 7.2 为什么可以按 GIA ID 计算

GIA 对象 ID 是拓扑序。AND 的 fanin ID 小于当前节点 ID。因此对同一 frame 内 dirty AND，如果按 ID 升序处理，fanin 的 local sim 要么已经计算，要么使用 default phase vector。

事件队列实现上可以有两种方式：

1. 简单版：BFS 收集 dirty keys，最后按 `(frame, objId)` 排序后计算。
2. 直接版：queue 传播时即时计算 fanout。由于 fanout ID 大于当前 AND，组合部分自然拓扑；跨 frame 的 RO source 放入下一 frame。

建议第一版使用简单版：先 collect TFO，再 sort + evaluate，代码更容易验证。

### 7.3 RI/RO 跨帧

遇到 RI fanout 时：

```text
riValue(frame) -> roValue(frame + 1)
```

需要把对应 RO 在下一 frame 标记为 dirty source。这个逻辑与当前 `Cec_IncrMgrComputeTfo()` 的跨帧 TFO 思路一致。

## 8. 局部签名计算

### 8.1 默认签名

未 touched 的节点不分配 sim words。读取它的签名时返回 default phase vector：

```text
Gia_ObjPhase(obj) == 0: 000...000
Gia_ObjPhase(obj) == 1: 111...111
```

这是 all-zero baseline 下的节点值。当前 ABC 的比较逻辑也利用第一个 bit 表示相位，`Cec_ManSimCompareEqual()` 会根据 bit 0 自动处理正相/反相 signature。

### 8.2 AND 计算

对 dirty AND：

```text
S(node) = S(fanin0) op S(fanin1)
```

根据 `Gia_ObjFaninC0/C1` 处理反相：

```text
if c0 && c1: ~(S0 | S1)
if c0 && !c1: ~S0 & S1
if !c0 && c1: S0 & ~S1
if !c0 && !c1: S0 & S1
```

这与 `Cec_ManSimSimulateRound()` 中全图模拟内核一致。

### 8.3 RO/PI 计算

PI/RO 的 vector 来自 CEX injection：

- bit 0 恒为 0。
- CEX lane 如果 literal 赋值为 1，则对应 bit 置 1。
- 未赋值 lane 为 0。

RO remapping 需要保留原逻辑：如果 RO 有代表 RO，且该 pair 未 failed，则该 RO 的初始 sim 应从代表 RO 复制。局部版本可以在 source injection 之后做一轮 `Gia_ManCorrCreateRemapping()` 对 RO source vectors 的 remap；更好的方式是在读取 RO default/source 时查询 repr。

第一版建议简单处理：

1. 初始 RO source 按 CEX literal 写入。
2. 对当前 touched RO 执行 repr remap。
3. 如果 remap 改变某 RO vector，将该 RO 加入 frame 0 queue。

## 9. 局部 Class Refinement

### 9.1 dirty root 收集

每个 dirty candidate object 都可能让它所在 class 被 split。对每个 dirty object：

```text
if Gia_ObjIsConst(pAig, obj):
    dirty const class
else if Gia_ObjIsClass(pAig, obj):
    root = Gia_ObjIsHead(pAig, obj) ? obj : Gia_ObjRepr(pAig, obj)
    mark root
```

只 refine marked roots。

### 9.2 class split 规则

对每个 dirty root，遍历该 class 的成员。每个成员的 signature：

- 如果 `(frame, obj)` touched，读取 local sim words。
- 否则返回 default phase vector。

然后复用 ABC 原有比较语义：

```c
Cec_ManSimCompareEqual( pSimRoot, pSimMember, nWords )
```

如果不相等，说明存在当前 CEX lane 使二者取值不同，可以 split。

重建 class 可复用 `Cec_ManSimClassCreate()` 的逻辑：

```text
vClassOld: 与 root signature 相等的成员
vClassNew: 与 root signature 不等的成员
```

如果 `vClassNew` 大小大于 1，需要递归 refine `vClassNew`，因为同一个 root signature 只能把 class 分成两组，`vClassNew` 内部可能还可继续被当前 CEX lanes 分裂。

### 9.3 const class

对 candidate constant：

```text
if S(obj) != const0 signature:
    remove obj from const class
```

如果 `fConstCorr` 打开，需要与现有 `vRefinedC` / `Cec_ManSimProcessRefined()` 的语义保持一致。第一版可以不特殊优化 const class，遇到 const dirty 时 fallback 到 full resim 或 direct remove，避免错误处理 const refinement。

## 10. SAT pair 的保底处理

### 10.1 为什么需要保底

master 中 `status == 0` 的 pair 不直接 split，而是依赖 full resim 用 CEX pattern 打破它。如果我们用 deterministic CEX-only local sim 替代 full resim，可能出现以下情况：

- CEX 是 `nLits == 0` 的 trivial SAT。
- CEX 全部 source 都等于 0 baseline。
- 第一版局部实现漏了 RO remap 或 ring closing edge。
- bit packing 冲突导致该 CEX 没被成功放入当前 batch。

这些情况下，如果不做保底，SAT 已经发现的 disproval 可能不会反映到 `pReprs/pNexts`。

### 10.2 推荐策略

第一阶段验证模式：

```text
local incr sim 后，检查每个 status == 0 的 pair 是否已经不再 merged。
如果仍 merged，fallback 到 full Cec_ManResimulateCounterExamples()，并记录 counter。
```

稳定后生产模式：

```text
local incr sim 后，若 SAT pair 仍 merged，直接 split iObj。
```

direct split 是 sound 的，因为 SAT 已经给出该 SRM output 可满足，说明当前 speculative equivalence 对该 pair 不成立。它可能改变 master 的 refinement trajectory，但不会制造错误等价。

ring mode 下，closing edge `(tail, head)` 的 split 目标应选择 tail，避免把 class head 拆掉导致大范围 repr 变化。

## 11. timeout/fail 处理

### 11.1 timeout-only

如果本轮：

```text
nRealCex == 0 && nTrivCex == 0 && nTimeout > 0
```

则：

```text
skip simulation
Gia_ManCheckRefinements()
```

`Gia_ManCheckRefinements()` 对 `status == -1` 调用 `Cec_ManSimClassRemoveOne()`，把该 object 从 class 中移除。这是保守操作，不证明不等价，只是不再使用该 unproved merge。

### 11.2 mixed CEX + timeout

如果本轮同时有真实 CEX 和 timeout：

1. 对真实 CEX 做 local guided sim。
2. 对 timeout 仍由 `Gia_ManCheckRefinements()` 移除。
3. 不把 timeout 当成 simulation source。

## 12. 正确性分析

### 12.1 Soundness

local guided sim 只在发现具体 CEX lane 使两个节点 signature 不同时 split class。每个 lane 都对应一个具体输入轨迹，未赋值输入按 0 补全。因此：

```text
S(a) != S(b) => 存在具体输入轨迹使 a != b
```

所以 split 是 sound 的。

direct split fallback 也 sound，因为 SAT 已经证明对应 SRM output SAT，即存在输入轨迹使该 speculative pair 不成立。

### 12.2 Completeness 相对 master

local guided sim 不追求完全复现 master。原因是 master 在 CEX slots 之外还随机填充 PI/timeframe slots，可能顺便 split 一些与 SAT CEX 无关的 classes。

本文方案故意不保留这一点，因为它会破坏局部性。代价是：

```text
可能比 master 少做一些 opportunistic random split
```

但不会产生错误等价。后续 SAT/SRM iteration 仍会处理剩余 pairs。

### 12.3 终止性

每次 SAT CEX 至少通过 local sim 或 direct split 移除一个当前 disproved pair。timeout 通过 `Gia_ManCheckRefinements()` 保守移除对应 object。因此 refinement 仍单调减少候选关系，不会因为跳过 full sim 而卡住同一个 failed pair。

## 13. 性能预期

当前 profiling 显示：

- `-i` 已经显著减少 SRM/SAT proof 数。
- 主 loop simulation 在有 CEX 的场景仍走全图模拟。
- timeout-only skip 可以直接把无信息的 random full sim 降为 0。

增量 sim 的收益来自：

```text
O(N * nFrames * nWords)
    ->
O(|TFO(CEX sources)| * nWords + dirty class refine)
```

在后期 iteration 中，CEX 数量少、source 少、TFO 小时，收益最大。如果 CEX source fanout 覆盖大部分电路，则 fallback 到 full sim 更合适。

建议增加 fallback heuristic：

```text
if dirty object count > 0.7 * Gia_ManObjNum(pAig):
    use full resim
```

这个阈值与当前 active SRM 的 70% fallback 思路一致。

## 14. 实施计划

### Step 1: 抽取 CEX store 分类

新增：

```c
Cec_CexStoreStats_t Cec_ManCexStoreClassify( Vec_Int_t * vCexStore );
```

替换当前 boolean `Cec_ManCexStoreHasPattern()` 的调用点，但保持 fail-only skip 行为不变。

验证：

- timeout-only 日志中 `sim=0`。
- mixed CEX 日志中仍进入 resim。
- `nLits == 0` 不被误判为 timeout-only。

### Step 2: direct split for trivial SAT

对 `nLits == 0` 的 SAT output，直接 split 对应 pair。

验证：

- 构造或定位 SRM PO const1 case。
- 确认该 pair 不再 merged。
- 与 full resim 结果比较不产生错误等价。

### Step 3: local CEX injection + TFO collect

实现 `Cec_IncrSim_t`，支持：

- sparse source vector 写入；
- frame-aware TFO 收集；
- dirty object count 统计；
- 超过阈值 fallback full resim。

验证：

- 对每轮输出 `realCex/timeout/dirtyObjs/dirtyRoots/fallback`。
- 确认 dirty set 包含每个 SAT pair endpoint 的必要 fanout cone。

### Step 4: local signature evaluation

实现 dirty nodes 的 topological evaluation。

验证：

- debug mode 下，对同一 CEX batch 同时跑 full sim signature 和 local signature。
- 对所有 dirty nodes assert signature 一致。

### Step 5: local class refinement

实现 dirty roots 的 class split。

验证：

- dual mode：复制一份 `pReprs/pNexts` 跑 full resim，一份跑 local resim。
- 初期要求 local split 后每个 SAT pair 不再 merged。
- 进一步比较 local partition 是否为 full partition 的 coarser-or-equal 版本，即 local 可以少 split，但不能把 full 已经分开的 pair 重新合并。

### Step 6: 关闭 full fallback

在足够 case 通过后，生产模式改成：

```text
local sim
unmerged check
direct split if still merged
```

保留命令行 debug flag 用于 dual-run。

## 15. 风险与暗坑

### 15.1 随机 filler 语义变化

master 的失败后 resim 混入随机 filler，本文方案默认去掉。这会改变 refinement trajectory。预期结果是更局部、更快，但可能 iteration 数上升。需要用总时间而不是单轮 sim 时间判断收益。

### 15.2 RO remapping

原始 full resim 在每个 batch 中调用 `Gia_ManCorrPerformRemapping()`。local sim 必须等价处理 RO representative 的初始状态，否则 latch correspondence 场景会漏 split 或误 split。

### 15.3 ring mode

ring mode 的 closing edge 不是普通 `(repr, obj)` pair。direct split 和 unmerged check 都要使用 ring-aware 判定，不能简单调用 `Gia_ObjHasSameRepr()`。

### 15.4 pPhase/default signature

local sim 依赖 `Gia_ObjPhase()` 作为 all-zero default signature。必须在每轮 local sim 前确认 `Gia_ManSetPhase(pAig)` 已经对当前 AIG/class state 后的原始逻辑设置完毕。

### 15.5 const class

constant correspondence 的处理比普通 class 更容易出错。第一版建议对 dirty const candidate 直接 fallback full resim，等普通 class local sim 稳定后再优化。

### 15.6 CEX lane packing

如果多个 CEX packed 到同一个 lane 时 literal 冲突，当前 master 会换 lane。local sim 必须保留这个逻辑。不能简单把所有 CEX OR 到同一个 source vector。

## 16. 建议的命令行开关

建议不要复用 `-i` 承载所有实验。新增内部参数或 debug flag：

```text
-i          active SRM
-I          incremental guided resimulation
-D          dual-run debug: local sim + full sim compare
```

如果不想增加公开命令行，先用 compile-time macro：

```c
#define CEC_SCORR_INCR_SIM 1
#define CEC_SCORR_INCR_SIM_DUAL 0
```

## 17. 成功标准

第一阶段成功：

- timeout-only iteration 中 simulation 时间保持为 0。
- 有真实 CEX 的 iteration 中，local sim 不再调用 `Cec_ManSimSimulateRound()` 全图扫描。
- 每个 `status == 0` 的 SAT pair 在本轮结束后不再 merged。

第二阶段成功：

- dual-run 下 local sim 的 split 结果不产生 unsound merge。
- 代表性 benchmark 的 `NEnd/REnd` 与 baseline 接近或相同。
- 总时间优于当前 `skip-failed-resim`，而不是只优化单个 phase。

第三阶段成功：

- 在 CEX 稀疏、后期 iteration 多的 case 上，main-loop sim 降到接近 0。
- 在 CEX TFO 很大的 case 上，fallback 能避免局部算法变慢。

## 18. 推荐结论

保留当前 fail-only skip 是正确的：timeout-only 没有 guided 信息，master 的 resim 只是额外随机全图模拟。

真正的增量 simulation 不应在小 SRM 上做，而应把 SRM SAT 返回的 CEX 投影回原始 `pAig`，然后只沿 CEX sources 的 frame-aware TFO 做局部 simulation，并只 refine dirty classes。

第一版应牺牲 master 的随机 filler opportunism，采用 deterministic CEX-only semantics。这样局部性清晰、正确性容易证明、性能收益可控。对于 trivial SAT、all-zero CEX 或实现边界，使用 direct split 或 debug full fallback 保证进展。
