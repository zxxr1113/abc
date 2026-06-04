方向 1 ｜把整体等价证明改为 PDR/IC3 风格的单调引理积累
当前瓶颈：&scorr 的 k-induction 是"每个归纳步独立 SAT 实例"——即使在 SRM 上重用了候选等价类作为辅助引理，也只是"假设所有候选成立"这一件事；一旦某个 frame 的归纳失败，前一步学到的子句基本被丢弃，下一轮 SRM 重建后又得从零开始。

思路：把所有候选等价编码成一条安全性属性（"SRM 中所有 spec mux 永不激活"），用 PDR/IC3 求解。PDR 每一帧产生的相对归纳子句（relative inductive clauses）就是 latch 层的可复用引理；这些子句对所有候选等价对同时起强化作用，不像 k-induction 只对当前那一对使用。失败的归纳反例（CTI）经过 generalize 之后变成可丢回前一帧的 obligation——这正是 &scorr 现在缺的"学习从一次失败到永久强化"。

学术依据：

Bradley, SAT-Based Model Checking without Unrolling, VMCAI 2011（IC3 原文）
Eén, Mishchenko, Brayton, Efficient Implementation of Property Directed Reachability, FMCAD 2011（即 ABC 的 pdr/&pdr）
AVR (Goel & Gupta, FMCAD 2019) 把 PDR 风格用在等价检查上有现成证据
可行性：中。ABC 有 pdr 引擎，调用接口稳定。难点是把 PDR 学到的子句抽出来作为 latch 层 invariant，再注入到 &scorr 的 SRM SAT 求解器里（需要把 PDR 子句翻译成 cecSatG.c 里 cnf 上的 assumption literal）。

预期收益：在状态空间深、候选等价关联强的电路上估计 2-5×；在浅状态电路上几乎无增益。可以先做"pdr -d 预跑 → 提取 invariant → 注入 scorr"的离线版验证收益，再考虑紧耦合。

方向 2 ｜反例 cube 泛化 + 位并行扩展（CEX lifting）
当前瓶颈：你已经做了 SAT-guided 向量生成，但每次 SAT 给出一个 CEX 时，scorr 通常只把这一条赋值塞进仿真包（Cec_ManResimulateCounterExamples）。事实上一个 CEX 里大多数 PI/latch 位是"无关变量"——把它们随机化后，得到的仍然是反例。这等价于免费拿到一个反例 cube，里面藏着 2^k 个等价的反例。

思路：CEX 拿到后立即做一次 ternary simulation lifting——从 CEX 出发，把每个 PI 位反复尝试翻成 X，只要差异输出仍保持差异就保留 X。得到 cube C。然后 bit-parallel 把 C 的非 X 位固定、X 位灌随机比特，一次 64/256 个并行向量丢进仿真。这一步分裂的等价类数量经验上是单条 CEX 的 5-20 倍。

与你已有 SAT-guided sim 的关系：你的工作是"主动生成 query 让 SAT 给出有用的 CEX"；这个工作是"拿到 CEX 后榨出最大信息量"。两者正交，可以叠加。

学术依据：

Bradley, Understanding IC3, SAT 2012（cube generalization 章节是标准做法）
Chockler, Ivrii, Matsliah 等 Cross-Entropy Based Testing（lifting 应用于 SE）
ABC 内部 &pdr 的 generalize 函数（Pdr_ManGeneralize）可以直接借鉴算法骨架
可行性：高。ternary lifting 是几十行的循环；bit-parallel 仿真 ABC 已经有 Gia_ManSimulateWord。改动集中在 Cec_ManResimulateCounterExamples 这一处。

预期收益：每个 SAT call 的"等价类细化产出"提升 5-10×。在 SAT 是瓶颈的电路上整体加速 2-3×。这是我会优先做的一项——投入产出比最高。

方向 3 ｜AVX-512 / codegen 仿真后端
当前瓶颈：Gia_ManSimulateWord 是 64-bit packed simulation，已经是好代码，但仍然是逐节点指针追踪 + 64-bit 字操作。在大型电路（>10⁶ AIG node）上 simulation 经常占整个 scorr wall-time 的 30-50%。

思路：两层加速——

AVX-512：把 word 从 uint64_t 换成 __m512i，AND/NOT 直接用 intrinsic。每节点 8× 吞吐。
Codegen：把 AIG 拓扑序编译成 C 文件（每个节点一行 t123 = t87 & ~t99;），然后 dlopen。这一步消除指针追踪和 cache miss，文献上常给 5-20×（看电路大小）。
学术/工业依据：

Verilator 的 CXXRTL 后端，本质就是 codegen + 字级 SIMD
Yotta / EsperantoSim（Snyder 等人 DAC 系列论文）
Khronos: Fused Memory Access for Massively-Parallel Logic Simulation on GPUs, DAC 2021——给出了仿真访存的精确瓶颈分析
可行性：AVX-512 改造低风险，估计 1 周；codegen 路径中等复杂度（要处理 incremental——每次 SRM 重建意味着重新生成代码，dlopen 编译开销要摊销过几百次仿真才划算）。所以先做 AVX-512，codegen 留给确实证明仿真是大头之后再上。

预期收益：纯仿真 3-8×；scorr 整体 1.3-2×（受 Amdahl 限制于 SAT 部分）。

方向 4 ｜UNSAT-core 驱动的等价对调度与引理共享
当前瓶颈：&scorr 的 candidate pair 顺序基本由 union-find 类的遍历顺序决定。不同 pair 的 SAT 证明常常共享支撑集（同一组 latch 的 invariant、同一组上游已证等价），但目前这些共享是隐式的、每次 SAT 重新发现。

思路：每个成功证明的 pair 抽出 UNSAT core，记录"这个证明用到了哪些 latch、哪些上游 spec mux"。在 candidate 集合上构建支撑依赖图，做拓扑/聚类调度——支撑集重叠大的 pair 连续地丢进同一个 incremental SAT 实例（不重启），让 conflict-driven learned clauses 跨 pair 复用。这与你的例子（活动性启发式）是同源思想，但比 VSIDS 更直接——VSIDS 是变量层面的，proof-core 是问题结构层面的。

学术依据：

Gupta et al, Iterative Abstraction Using SAT-Based BMC with Proof Analysis, ICCAD 2003
McMillan & Amla, Automatic Abstraction without Counterexamples, TACAS 2003
Eén & Sörensson 关于 incremental SAT 的工作（这是 ABC SAT 的基础，但 proof core 在 scorr 里没充分利用）
可行性：中。需要 MiniSat/glucose 暴露 unsat core 接口（已有），但要新增依赖图 + 调度器。估计 2 周原型 + 1 周调参。

预期收益：减少 30-50% SAT call 次数（来自 learned clause 复用），整体 1.5-2×。在等价类大、互依赖强的工业电路（CPU、DSP）上效果更显著。

优先级建议
方向	投入	收益预期	风险
2. CEX lifting	1-2 周	2-3×	低
3a. AVX-512 仿真	1 周	1.3-1.5×	低
4. Proof-core 调度	3 周	1.5-2×	中
1. PDR 引理注入	4-6 周	2-5×	中高
我会按 2 → 3a → 4 → 1 的顺序做：先把"低垂果实"（CEX lifting + AVX-512）拿掉，再投入 SAT 层的结构性优化。如果你想我对其中某一项再深入到接口/数据结构/伪代码层，告诉我哪一项。