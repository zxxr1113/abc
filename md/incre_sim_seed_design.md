# incre_sim_seed:持久化 pattern + changed-repr TFO 的增量 Simulation 设计

分支:`incre_sim_seed`(基于 `incre_sim`,已含 `-s` skip-fail-resim 开关、且已删除 `-I` 的 force-split)。
作者记录,2026-06-05。

---

## 0. 背景与定位

`&scorr` 每轮 SAT 后要 resimulation 把 CEX 灌进类里做 refine。现有两条路:

- **baseline 全图 resim**:每轮对原始 AIG 全图 bit-parallel sweep。ILA 族这部分占 ~35% 时间。
- **`-I`(cecCorrIncrSim.c)**:CEX 驱动的局部 TFO sim,背景用 **constant phase 向量**(= 全零输入下的值),只算 CEX 脏锥。

`-I` 在 ILA 上 **净亏**(实测见下),根因有两条:

1. **CEX 驱动的脏锥恒宽**:`maxdirty/keys ≈ 75%`,即使一轮只有 2–3 个 CEX,锥也是全图 75%。因为 CEX 是一整份输入赋值,相对全零背景在下游处处不同。
2. **背景不持久 + 0-fill**:untouched 节点只能取 phase(常量),distinguishing power 弱,导致 SAT 已证伪的 pair resim 拆不开,曾被迫加 force-split → 扰动轨迹(真 CEX 0.94M→1.33M)→ 反而更慢更欠精化。force-split 已在本分支删除。

**本设计换掉脏锥的"触发源":从 CEX 改成 changed-repr,并把背景从 phase 常量换成持久化的真实 pattern。**

---

## 1. 核心数据发现(决定设计形态)

把脏锥触发源从 CEX 换成 **changed-repr** 后,sim 锥的分布完全不同。实测 BGEU(nObjs=2,142,874),逐轮 changed-repr 的 TFO 节点数:

| round | seed reprs | TFO 节点 | TFO 占 objs | active pairs |
|---|---|---|---|---|
| 11 | 16408 | 1,329,521 | 62% | 69.7% |
| 27 | 364 | 1,053,602 | 49% | 3.7% |
| 29 | 289 | 1,038,109 | 48% | 2.1% |
| 38 | 104 | 6,214 | **0.3%** | 0.4% |
| 83 | 118 | 2,016 | **0.1%** | 0.3% |
| 113 | 60 | 650 | **0.0%** | 0.1% |

**结论:changed-repr 的 sim 锥是双峰的**:

- 约一半的轮 ~**0.1%**(seed 都是局部低扇出节点)→ 持久化 + 局部 resim **大赢**。
- 约一半的轮 ~**50%**(seed 里只要混进一个高扇出 repr,TFO 就炸到半图)→ 必须 **fallback 全图 sweep**。

对照 `-I` 的 CEX 锥(恒 75%,低 CEX 轮也救不了):**changed-repr 触发源在"窄轮"上是真的窄**,这正是 incre_sim_seed 值得做的理由;但**不是全胜**,净收益 = 窄轮占总 sim 时间的比例。

> ⚠️ 注意区分两个量:`active pairs%`(候选等价对,SAT 侧,均值~2%)≠ `TFO 节点%`(sim 锥,本表)。早期把二者混为一谈过,sim 成本由后者决定。

---

## 2. 为什么必须持久化 pattern(read-set vs write-set)

记 seed = 上一轮 repr 变化的节点。

- **写集**(下一轮值会变的节点)= TFO(seed)。✅ 这是对的,就是脏锥。
- **但持久化解决的是读集**:要算 TFO(seed) 里某节点 n,需要 n 的所有 fanin 当前值;其中 TFO 外的 **side input** 值没变,但**必须能读到**。

"没变" ≠ "现成可用"。拿到 side input 只有两条路:

1. **持久化**:上一轮存着每个节点的仿真值 → O(1) 读;
2. **不持久化**:现场重算 side input → 递归回 PI → 整图 sweep。

所以"只重算 TFO(seed)"要成立,**前提是把每个节点的仿真值跨轮留着**。持久化不是为了正确(不持久也 sound),而是把每轮 **O(整图)** 降成 **O(脏锥)** 的唯一开关。要持久化的是**每节点的仿真值(冻结背景)**,不是 PI 激励(那是常量)。

`-I` 没做这件事(背景用 phase 常量),所以它根本没有"冻结背景"可读,只能靠 0-fill 假装背景是全零——这正是它 distinguishing power 弱的根。

---

## 3. 数据模型

```
Cec_SeedSim_t:
  // 持久化仿真值:key = frame*nObjs + objId,每 key nWords 个 word。
  // 稠密存储,跨轮存活(这是与 cecCorrIncrSim.c 的稀疏 per-batch 池的本质区别)。
  unsigned * pVal;            // size = (nFrames+1) * nObjs * nWords
  int        nFrames, nObjs, nWords, nPis, nRegs;

  // 标准 pattern bank(固定 32*nWords lane 的激励),持久。
  // 初始化时全图 sweep 一次填 pVal;之后只在脏锥内更新。

  // 复用 -i 的 changed-repr seed 机制:
  //   Cec_IncrMgrComputeSeeds → vSeeds(repr 变化的节点)
  //   TFO walk(frame-aware,跨 RI→RO)→ 脏 key 集合
  Vec_Int_t * vDirtyKeys;     // 本轮脏锥(排序后拓扑序求值)
  int *       pMark; int nMarkVersion;   // O(1) 版本号清脏标记
  // refine scratch(同 cecCorrIncrSim.c)
```

内存量级:BGEU `(nFrames+1=2) * 2.14M * 15 word * 4B ≈ 256 MB`。可接受,但需在 Free 时释放;后续可只存 RO+AND、或按需压 nWords。

---

## 4. 算法骨架

**初始化(一次,BMC 后):**
1. 选定 pattern bank(随机 + 已见 CEX 累积,填满 nWords 个 word)。
2. 全图 bit-parallel sweep,把每个 (frame,obj) 的值写进 `pVal`。
3. 在该 bank 下做一次完整 class refine(等同现状)。

**每轮 r:**
1. SAT 求 SRM → disproved pairs + CEX。
2. 用 CEX 直接拆掉 disproved pairs(CEX 是合法 witness,sound)。→ repr 变化。
3. `seeds = ComputeSeeds()`(本轮 repr 变化节点);`TFO(seeds)` → `vDirtyKeys`。
4. **cone gate**:`|dirtyKeys| > FRAC * nFrames*nObjs` → fallback 全图 sweep(并借机刷新整个 `pVal`);否则进 5。
5. **局部求值**:按拓扑序重算 `vDirtyKeys`,side input 从 `pVal` 读(持久背景),结果写回 `pVal`。
6. **局部 refine**:只 refine 含脏节点的类(同 `Cec_IncrSimRefineFrame`)。

关键点:第 5 步的"写回 `pVal`"使持久背景始终是最新真实值——这是与 `-I`(算完即弃)的本质差别。

---

## 5. 复用现有设施

| 需要的能力 | 直接复用 |
|---|---|
| changed-repr seed | `Cec_IncrMgrComputeSeeds`(cecCorrIncr.c)|
| frame-aware TFO walk | 仿 `Cec_IncrSimComputeTfo`(cecCorrIncrSim.c)|
| AND/RO 求值 kernel | 仿 `Cec_IncrSimEvaluate`(但 side input 读 `pVal` 而非 phase)|
| 局部 class refine | 仿 `Cec_IncrSimRefineFrame/RefineClass` |
| O(1) 脏标记清理 | 版本号 `nMarkVersion`(同 cecCorrIncrSim.c)|
| 全图 sweep / fallback | `Cec_ManSeqResimulate` |

新写的核心只有:稠密持久 `pVal` 的分配/初始化/读写,和把 evaluate 的 side-input 源从 phase 改成 `pVal`。

---

## 6. 待决策点(实现前需定)

1. **新 CEX 如何进 bank**:固定 bank 不加新 lane,则靠第 2 步直接拆 disproved pair 推进(repr 变化驱动 refine);还是周期性把新 CEX 灌成新 lane(只 sweep 新 word)。前者简单,先做前者。
2. **bank 是否增长**:先固定 nWords 不增长,避免无界 sweep;不够 distinguishing 再议。
3. **直接拆 disproved pair 会不会重蹈 force-split 的扰动**:第 2 步是带 witness 的拆分(不是无 witness 强拆),理论上 sound 且不应造成 token_ring 那种 regression,但**必须实测确认轨迹/时间**。
4. **内存**:256MB 可接受;若 OOM 风险,只存 RO+AND 或降 nWords。

---

## 7. 分阶段计划(每阶段可验证)

- **Phase 0(本次)**:分支 + 本设计文档 + 删除 force-split + `-s` 开关。✅
- **Phase 1 — 先量化,后建引擎**:加 instrumentation,逐轮输出 changed-repr 的 **TFO 节点数 / nObjs** 与该轮 sim 耗时,统计**窄轮(<FRAC)占总 sim 时间的比例**。
  - 验证标准:若窄轮占 sim 时间 ≥ ~40%,引擎值得建;若窄轮虽多但都是廉价轮(总时间占比小),则收益有限,需重新评估。
- **Phase 2 — 持久存储 + 局部求值**:`Cec_SeedSim_t` 的 `pVal` 分配/初始化(全图 sweep 填充)+ seeded TFO 局部求值(读写 `pVal`)+ cone gate fallback。先不接主循环,用单测对拍全图 sweep 验证数值一致。
- **Phase 3 — 局部 refine + 接主循环**:接到 `Cec_ManLSCorrespondenceClasses`,加 `-J`(暂定)开关,对拍 baseline 的 NEnd(必须 sound:不低于 baseline 化简量级)。
- **Phase 4 — benchmark + cec**:跑 ILA 全族,量 Sim/Sat/TOTAL,cec/dsec 验 sound。

---

## 8. 风险与回退

- **半图轮拖累**:~50% 的轮 fallback 全图,持久化在那些轮零收益还多付了 seed/TFO 开销。靠 cone gate 把额外开销压到 O(seed+TFO 计算),且这些轮本就要全图 sweep。
- **内存**:稠密 `pVal` 256MB+;Phase 2 先验证可行性。
- **直接拆 pair 的轨迹扰动**:见 §6.3,Phase 3 实测把关。
- **回退**:整套在新分支,默认开关关;任何阶段不达标就停在该阶段,不影响 `incre_sim`。
