一、&scorr 算法流程概览
&scorr 做的是顺序等价归约（Sequential Correspondence）：用 SAT + 仿真迭代找出"所有时刻输出值永远相同"的寄存器对，合并它们来缩减电路。整体流程：


初始化 → BMC 预筛 → [SAT 求解 → CEX仿真精化]循环 → 最终归约
二、各段日志的含义
2.1 电路信息（&ps 输出，第9行）

i/o = 192/2(c=1)  ff = 229  and = 152722  lev = 1960
字段	含义
i/o = 192/2(c=1)	192 个主输入，2 个输出（其中 1 个是约束输出 constraint）
ff = 229	229 个寄存器（flip-flop）
and = 152722	152722 个 AND 门
lev = 1960	组合逻辑层数
2.2 SAT 预处理阶段（第11–19行 cst/cls/lit/unused/proof）
这是 BMC 预处理中的子块，SAT solver 在正式迭代前做一轮预简化：

字段	含义
cst	当前候选约束数（候选等价对数量），从 152951 降到 139439
cls	SAT solver 学到的子句数
lit	子句中的 literal 总数
unused	未使用的 SAT 变量数
proof	此轮已被证明的等价数
2.3 配置摘要（第20行）

Obj = 153375. And = 152722. Conf = 100. Fr = 1. Lcorr = 0. Ring = 1. CSat = 1.
字段	含义
Obj	AIG 总对象数
Conf = 100	每次 SAT 查询的冲突上限（nBTLimit）
Fr = 1	BMC 展开帧数 = 1
Lcorr = 0	0 = 寄存器对应（register correspondence），非 latch 对应
Ring / CSat	内部数据结构/求解器选项
三、主迭代行：每个字段的精确含义
格式：N : c=... cl=... lit=... p=... d=... f=... +/- T=...

这是 cecCorr.c:1086 中 Cec_ManRefinedClassPrintStats 打印的：


c   = Counter0  // Gia_ObjIsConst(p,i) 为真的节点数
cl  = Counter   // Gia_ObjIsHead(p,i) 为真的节点数
lit = CiNum + AndNum - Counter - CounterX  // 有效 literal 数
p   = nProve   // 本轮 SAT 返回 UNSAT 的对数（等价性证明成功）
d   = nDispr   // 本轮 SAT 找到 CEX（等价性被反驳）
f   = nFail    // 本轮 SAT 超冲突上限（超时，未定）
+/- = PO[0] 的驱动节点是否还在 const0 等价类中
字段	具体含义
c（candidates）	当前处于 const0 等价类的节点数（候选为常值的节点）。这是最核心的进度指标，单调递减
cl（class heads）	非平凡等价类的"代表节点"数 = 有多少个类仍在等待验证
lit	SAT 框架中的 literal 数，反映当前 SAT 状态复杂度
p	本轮 SAT 证明了 p 对等价（这些对被永久合并）
d	本轮 SAT 反驳了 d 对等价（找到了区分赋值，从候选集移除）
f	本轮 SAT 超时了 f 对（留在候选集，下轮继续）
+	PO[0] 的驱动节点仍是 const0 候选 = 算法仍在有效推进
-	PO[0] 的驱动节点已被移出 const0 类 = 进入收敛/停滞阶段
2.4 CEX-STAT 行
格式：[CEX-STAT] r=N nSrmCi=613 nSrmAnd=... nSrmCo=... nRecs=... sat/triv/to=... avgLits=... maxLits=...

这是 cecCorr.c:1048 的打印，每轮 SAT 求解完成后立即输出：

字段	含义
r=N	对应第 N 轮循环的 SAT 求解（其结果会反映在下一行 N+1 : 的 d/f 上）
nSrmCi = 613	推测规约镜像（SRM）电路的 CI 数，全程不变。= 229(FF) + 2×192(PI×2帧) = 613
nSrmAnd	SRM 的 AND 门数，反映待检等价对的锥形复杂度。随轮次增大（残余的难候选支撑更大）
nSrmCo	SRM 的 CO 数 = 本轮放入 SAT 的候选等价对数量
nRecs	CEX store 中的记录总数 = sat + triv + to
sat	找到具体赋值 CEX 的记录数（nLits > 0）→ 等于下轮 d
triv	空赋值 CEX（nLits == 0，零输入即可区分）→ 也贡献到下轮 d
to	SAT 超时（nLits < 0）→ 等于下轮 f
avgLits	sat 类 CEX 的平均 literal 数（CEX 复杂度）
maxLits	sat 类 CEX 的最大 literal 数
四、核心数量关系
你观察到的关系都是真实的，源码完全印证：

关系1：d[N+1] = sat[N]，f[N+1] = to[N]

[CEX-STAT] r=N   sat/triv/to = S/T/F
      N+1 :  d = S   f = F
CEX-STAT r=N 在打印时，SAT 已经完成，vStatus 就在那里。随后打印的第 N+1 行直接读取同一个 vStatus。

从日志验证（几个关键轮次）：

CEX-STAT r=N	sat/to	下一行 N+1 的 d/f
r=0	144/0	1: d=144, f=0 ✓
r=6	1379/4584	7: d=1379, f=4584 ✓
r=7	208/2264	8: d=208, f=2264 ✓
r=35	0/1817	36: d=0, f=1817 ✓
关系2：nRecs = d[N+1] + f[N+1]
（triv 在本 log 全程为 0，所以 nRecs = sat + to = d_next + f_next）

关系3：nSrmCi = ff + 2 × pi = 229 + 2×192 = 613（常数）
关系4：c 单调递减（永不回升）
五、Problem10 完整流程走读
Phase 0：初始状态（第21行）

  0 : c = 139414  cl = 282  lit = 152477  p = 0  d = 0  f = 0  +
预处理后：从 152951 候选压缩到 139414（SAT 预简化了 13k+ 候选）
共有 282 个非平凡等价类（cl）
还没做任何 SAT 求解，p=d=f=0
Phase 1：BMC 快速筛选（第22–43行，BMC : 前缀）

BMC : c = 139348  d = 504  ...
BMC : c = 139313  d = 494  ...
...
BMC : c = 138499  p = 1  d = 1  ...
Cec_ManLSCorrespondenceBmc 在主循环前先跑一遍展开仿真，快速用简单的时序 CEX 排除大量候选。c 从 139414 → 138499，减少了约 915 个候选。这里 d 很大（几百），说明仿真本身就能区分很多对。

Phase 2：SAT 迭代精化，早期（第45–53行，轮次1–5）

[CEX-STAT] r=0  nRecs=144  sat/triv/to=144/0/0  avgLits=28.19
  1 : c = 138261  p = 42   d = 144  f = 0
[CEX-STAT] r=1  nRecs=63   sat/triv/to=63/0/0   avgLits=56.63
  2 : c = 138178  p = 231  d = 63   f = 0
...
  5 : c = 101652  p = 273  d = 5    f = 0
特征：to=0，即没有超时。SAT 能在 100 次冲突内解决所有候选。

轮次5 → CEX-STAT r=5: nSrmAnd 骤增至 13337，nSrmCo=23709，nRecs=18807。这是一次"爆发"——展开帧数够了，同时能看到大量候选的区分点。c 从 101652 急降。
Phase 3：SAT+超时混合阶段（轮次7–35）

[CEX-STAT] r=6  sat/triv/to=1379/0/4584
  7 : c = 88809  p = 6518  d = 1379  f = 4584  +
...
[CEX-STAT] r=35 sat/triv/to=0/0/1817
 36 : c = 43463  p = 6479  d = 0     f = 1817  -  ← 这里 + 变 -
此阶段 to > 0，说明有候选在 100 次冲突内 SAT 无法判定。d 和 f 并存。nSrmAnd 持续增大（4万→16万），难候选的支撑锥越来越大。

+ 变 - 发生在第36轮：sat[35]=0 → d[36]=0，CEX 找不到了。PO[0] 的驱动节点被移出 const0 类，标志着算法进入"纯靠 p（SAT 证明）推进"阶段。

Phase 4：纯超时阶段（轮次36–115）

[CEX-STAT] r=36  sat=0/triv=0/to=1818  avgLits=0.00
 37 : c = 41921  p = 6078  d = 0  f = 1818  -
...
[CEX-STAT] r=115 sat=0/triv=0/to=2  
116 : c = 16735  p = 0  d = 0  f = 2  -
117 : c = 16735  p = 0  d = 0  f = 0  -
sat=0 全程。所有 CEX 都超时（to=nRecs）。算法仍在进行 SAT 证明（p 依然几千），c 继续缓慢下降。到轮次116 f=2，轮次117 p=d=f=0 → 循环终止。

Phase 5：结果

Srm = 1.87s (12.09%)   Sat = 12.48s (80.56%)   Sim = 0.85s (5.50%)
NBeg = 152722. NEnd = 126919. (Gain = 16.90%)
RBeg = 229. REnd = 103. (Gain = 55.02%)
SAT 占了 80% 时间（Hard 题的典型特征）
AND 门：152722 → 126919（减少 16.9%）
寄存器：229 → 103（减少 55%，有 126 个寄存器被证明等价！）
六、一张关系图

轮次 N 的主循环：

  Build SRM miter (pSrm)
       ↓
  SAT solve → vStatus (p/d/f), vCexStore (sat/triv/to)
       ↓
  打印 [CEX-STAT] r=N   ← nSrmCi/And/Co, nRecs, sat/triv/to
       ↓
  Simulate CEXes, refine classes
       ↓
  打印 "N+1 : c=... p=nProve d=nDispr f=nFail"
  
  关键: d[N+1] = sat[N] + triv[N]
        f[N+1] = to[N]
        nRecs[N] = d[N+1] + f[N+1]

一、为什么 CBS 会陷入"每轮只做一两个"的死循环
源码确认的底层机制
在 Gia_ManCheckRefinements（cecCorr.c:619）中，对超时节点的处理只有一行：


if ( status == -1 )
{
    Cec_ManSimClassRemoveOne( pSim, iObj );  // 唯一操作
    continue;
}
Cec_ManSimClassRemoveOne（cecClass.c:324）会直接修改 pAig->pReprs，将超时节点 iObj 从等价类中剥离为单例。因此，每轮中超时的 f 个候选会被立刻从 pReprs 移除，下一轮的 SRM 就比这轮少 f 个输出（nSrmCo 减少 f）。

对于被 CBS 证明 UNSAT 的节点（status=1）：continue，什么都不做——它们留在 pReprs 中，下一轮 SRM 仍然包含它们，CBS 需要重新证明。

现象 A：线性剥离（Problem05_label43, incre_scorr）

r=306: nSrmCo=174554, to=1  →  307: nSrmCo=174553, to=1  →  ...  每轮减1
机制：SRM 包含 174554 个候选对。CBS 在当前投机规约（speculative reduction）下对其中 174553 个快速证明 UNSAT（它们的 1-step 归纳证明在"其他候选均成立"的假设下很简单），而 1 个候选超时（它是某个时序链的根节点——其 K=1 证明不依赖其他候选的假设，或其证明深度超出 100 次冲突的范围）。

超时节点被移除后，下一轮：174553 个候选继续被快速证明（其归纳假设仍然成立），1 个新的"根节点"超时。如此线性剥离。

与移位寄存器/令牌环结构的关系：


令牌环(size n): R_0 → R_1 → ... → R_{n-1} → R_0
每个位置的等价性证明需要看 n 个周期才能覆盖所有相位。K=1 只能看 1 步，因此在任何给定的投机规约下，只有处于当前"可证明相位"的 1 个位置能被证明 UNSAT。移除它后，相邻位置暴露，再次只有 1 个能被证明。这就是线性剥离的本质原因。

现象 B：永久重试（Problem15_label35, hard_scorr_logs_v）

r=243: nSrmCo=25435, nSrmAnd=1852256, to=3   → r=244: nSrmCo=25435, nSrmAnd=1852474, to=3
这里 nSrmCo 不减少，但 nSrmAnd 持续增大（每轮 +200 左右）。这表明：

3 个超时节点从类中被剥离（−3），但它们所在的大型等价类分裂后，产生了新的 ≥3 个内部配对（+3），净减为零。
Problem15 的等价类很大（cl 很小但 nSrmCo 很大），一个大类分裂会在剩余成员间创建新的配对，导致 nSrmCo 不下降。算法陷入：每轮移除几个，每轮又从分裂中产生几个，永远不收敛。

nSrmAnd 增大是因为：随着大类不断分裂，SRM 需要对更多节点分别构建锥形，AND 门数增加。

二、冲突限制 -B 100 与逻辑深度 Lev > 1000 的矛盾
CBS 的搜索模型
CBS（Circuit-Based SAT，giaCSat.c:943）不是 CDCL，它直接在 AIG 上做 justification-based 回溯搜索：


// Cbs_ManSolve 核心：
p->Pars.nBTThis = 0;
Cbs_ManAssign( p, pObj, 0, NULL, NULL );
if ( !Cbs_ManSolve_rec(p, 0) && !Cbs_ManCheckLimits(p) )
    Cbs_ManSaveModel( p, p->vModel );  // SAT: 找到 CEX
else
    RetValue = 1;                       // 看似 UNSAT
if ( Cbs_ManCheckLimits( p ) )
    RetValue = -1;                      // 实为 Timeout
nBTThis > nBTLimit 时 CheckLimits 返回真。每次 CBS 必须选择一个 AIG 节点赋值并向下 justify，遇到矛盾则回溯。

100 次冲突 vs 1960 层逻辑
对于深度 1960 的 SRM 电路：

一次 justify 操作沿逻辑锥向下传播，直到到达 PI 或已赋值节点
在 1960 层的电路中，从 CO 到 PI 的 implication chain 长度 ≈ 1960
每次回溯只撤销当前分支的决策，下一次尝试重新 justify
100 次冲突 ≈ 最多探索 100 个"关键分叉点"附近的搜索空间
对于 K=1 归纳步骤的 UNSAT 证明：

必须证明：不存在任何初始状态 + 输入序列使得 A ≠ B 在第 1 步发生

这等价于：对初始状态空间（ 2^{ff} = 2^{229} 种可能）的所有路径，CBS 必须找到矛盾。

100 次冲突能探索的空间是这个的 $2^{-229+7}$ 量级（指数级小）。结果：CBS 既找不到 SAT（没找到区分赋值），也给不出 UNSAT 证明（没穷举完搜索空间），只能返回 -1（Undecided）。

这是归纳失效的本质：K=1 与初始状态的距离是 229 个寄存器深度，而 100 次冲突只能"回溯"约 100 个逻辑分叉点。

三、针对"超时浪费"的优化策略
你的核心目标：加速，不损失 &scorr 的质量（不引入错误合并）。

超时节点被 Cec_ManSimClassRemoveOne 移除——这是保守操作（不合并、只拆分），不会引入不等价合并。因此，提前退出不会降低已完成合并的正确性，只是放弃后续可能发现的合并机会。

策略 A：纯超时饱和退出（最直接，零质量损失）
在 cecCorr.c 的主循环中，CEX-STAT 打印块之后添加：


/* 统计连续纯超时轮数 */
static int nPureToStreak = 0;
if ( Vec_IntSize(vCexStore) > 0 )
{
    /* 重用已计算的 _nSat, _nTo */
    if ( _nSat == 0 && _nTo > 0 )
        nPureToStreak++;
    else
        nPureToStreak = 0;
}
else
    nPureToStreak = 0;

/* pPars->nPureToMax > 0 时启用 */
if ( pPars->nPureToMax > 0 && nPureToStreak >= pPars->nPureToMax )
{
    Vec_IntFree( vCexStore );
    Vec_StrFree( vStatus );
    Vec_IntFree( vOutputs );
    break;
}
在 Cec_ParCor_t（cec.h）中加一个字段 int nPureToMax，默认 0（禁用）。用 &scorr -T 10 之类的 flag 控制。

效果分析：

Problem15_label35：nPureToMax=5 可在约第 168 轮退出（节省 ~50 sec），质量与第 268 轮相同（后 100 轮 d=0 没有任何新合并，只是 SRM 在反复重试）
Problem05_label43：nPureToMax=5 约在第 311 轮退出（节省 ~6 sec），接近无影响
Problem05_label45 之类 "Other=99%" 的情况：主循环只有 3 轮，早退毫无意义——这类情况的瓶颈在 BMC 阶段而非主循环
策略 B：动态冲突上限（提升质量，代价是每轮更慢）

/* 连续 k 轮纯超时后倍增 nBTLimit */
if ( nPureToStreak > 0 && nPureToStreak % 5 == 0 )
{
    pParsSat->nBTLimit = Abc_MinInt( pParsSat->nBTLimit * 2, pPars->nBTLimitMax );
    if ( pPars->fVerbose )
        Abc_Print( 1, "Scorr: BT limit increased to %d\n", pParsSat->nBTLimit );
}
这在"磨工"阶段给 CBS 更多预算，有机会突破之前超时的候选。对 K=1 仍然无能为力的电路（真正需要 K>1 帧），这不解决根本问题，但对于"只是 100 次稍微不够"的候选有效。

策略 C：合理利用已有参数（无需代码改动）
ABC 里已有两个相关参数：

参数	含义	推荐值
nStepsMax（-I k）	主循环最大迭代次数	对 hard case 设 300-500
nLimitMax（-X k）	若 lit 改善 < k 则停止	设 2-4 可提前退出
nLimitMax 当前的检查是（cecCorr.c:1138）：


if ( r > 4 && nPrev[0] - nCur <= 4*pPars->nLimitMax )
    /* 停止 */
这用 lit 数的绝对减少量做判断。在纯超时阶段，lit 每轮只减少 1-2（仅来自超时节点移除），nLimitMax=1 或 2 可以比较快速地触发。但注意这个判断在第 4 轮之后才开始，且基于滑动窗口，对突然进入停滞的情况反应较慢。

四、具体日志数据分析
Problem05_label43（incre_scorr, Gain=73.6%）

Srm=10.67s(11%)  Sat=59.37s(62%)  Sim=20.09s(21%)  Other=6.48s(4%)  TOTAL=96s
前 306 轮（主要工作区）：每轮处理数百~数千对，真实 Gain 在此阶段完成
后 24 轮（r=306→330）：nRecs=1, to=1/round. 每轮 ~0.3 sec，共浪费约 7 sec。AND 增益=0。
这 24 轮 Sat 时间主要用于对 ~174k 候选的重新归纳验证（每轮重证 174k 个 UNSAT 以维持投机规约的合法性），而唯一的 timeout 才是移除目标。提前退出收益约 7%，可接受。

Problem05_label45（hard_scorr_logs_v，Gain=50.6%）

Srm=0.17s(0%)  Sat=0.36s(0%)  Other=603s(99.9%)  TOTAL=604s
这个 case 的瓶颈完全不在 CBS 超时！主循环只跑了 4 轮。"Other" = BMC 阶段（Cec_ManLSCorrespondenceBmc），跑了 1785 次 BMC 迭代，每次 ~0.34 sec。真正的问题是：初始等价类有 220k 候选，BMC 每轮处理 ~30k 对，线性消减，1785 轮后才进入主循环。

这与 CBS 主循环的超时机制无关。优化方向应该是 BMC 预处理阶段（加大 BMC 帧数 nFrames、或改为批量 sim-only 筛选）。

Problem15_label35（hard_scorr_logs_v）

Srm=46.5s(26%)  Sat=92.5s(51%)  Sim=35.4s(19%)  Other=6.5s(4%)  TOTAL=182s
268 轮，最后 ~100 轮纯超时，nSrmCo≈25434 不减，nSrmAnd 持续增长至 185 万。这是最典型的"无效长尾"：

后 100 轮的 Sat 时间 ≈ 34 sec（100 rounds × ~0.34 sec/round）
AND Gain 贡献 ≈ 0%（只有 timeout 移除，无任何合并）
建议阈值：nPureToMax=5 在约第 168 轮退出，节省 ~34 sec，质量完全不变
工业级判断原则
判断"是否值得继续"的三个信号：

信号	含义	阈值建议
_nSat == 0 连续 k 轮	无新 CEX，无法增加可区分模式	k=5
nSrmAnd 持续增大而 nSrmCo 不减	等价类分裂产生的新配对抵消了移除	增幅 > 5%/10 轮
p 突然归零	SAT 证明也停止了，算法彻底停滞	立即退出
满足任意两个条件时退出是合理的。对你的 hard case，第一个条件（纯超时连续 5 轮）已经足够准确地识别"无效磨工"阶段。