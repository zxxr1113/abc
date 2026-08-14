# `&stran -P root` 实现真值文档

本文描述当前代码，而不是未来设计。`root` 是 `&stran` 的默认且唯一在开发的 proof scope；`window` 和 `output/po-ri` 明确冻结，只保留兼容路径，不做算法、QoR 或性能开发。SODC 不属于本算法，`&stran -o` 会被拒绝。

## 1. 正确性边界与状态

一次 root 运行从输入复制出一份 GIA。simulation、candidate discovery、CBS、shared scorr、虚拟选择和 repair 全部引用这份不可变 snapshot；直到最后才执行一次 bundle duplication 和 cleanup。

候选状态严格分为：

- `CANDIDATE`：signature/care 匹配，只是待证明关系；
- `PROVED_COMB`：CBS 在所有自由 PI/RO 状态上证明；
- `PROVED_SEQ`：shared scorr 的 base 与 induction 都完整、无 UNKNOWN/冲突提前停止，并且 fixed point 后 root/candidate 仍在同一类；
- `SELECTED`：proved relation 仍结构合法、动态 marginal gain 为正，并被 root-major 虚拟串行选择。

“加入 fixed point”不等于 proved。scorr 最终分类是：

- `PROVED`：完整 oracle 后仍同类；
- `UNPROVED(split)`：完整 oracle 后已拆类；
- `UNKNOWN`：base/induction obligation 为 UNKNOWN、达到 step/iteration/总冲突限制，或其他提前停止。oracle 不完整时不把当前拆类误报为 split。

`Free/Covered/Used` 只描述虚拟串行 commit：

- `Covered` 是已选 candidate 的动态 MFFC kill-set；
- `Used` 是已选 recipe 的外部 support；
- 它们不修改 snapshot，但会改变后续 root 的合法性和 marginal MFFC。

## 2. 端到端流程

1. 从 reset 初态做多帧 bit-parallel simulation，建立完整 signature index，并收集全部 AND roots。
2. COMB 阶段按当前动态 MFFC 潜力降序处理 root。每个 root 内固定顺序为 constant、existing、build；build 先按 gate 数升序，再按 exact template、coverage/residual 次序、CI support overlap、route/locality 和稳定 canonical key 排序。
3. 对一个 root 的 candidates 串行做 CBS。找到第一个 CBS proof 后立即尝试虚拟 `SELECTED`，更新 `Covered/Used`，停止该 root；CBS SAT/UNKNOWN 的关系保留给 sequential，但已经由 CBS 解决的 root 不进入 scorr。
4. COMB barrier 重新计算动态 MFFC/优先级，删除已 free root，校验 candidate support 与 marginal gain；过期关系分类为 root-free、candidate-support-freed 或 root-MFFC-changed。
5. SEQ 有两个模式：默认 top-1 每个 unresolved root 只 seed 排序第一项；`-t` all-candidate seed 该 root 的全部语义合法、canonical candidates。没有 layer、wave 或人工 top-q 截断。
6. 所有 seed relations 进入一次 shared SRM/closure 并运行到真正 fixed point；之后逐关系分类 `PROVED/UNPROVED/UNKNOWN`。
7. fixed point 后按动态 MFFC root-major 消费 proved relations。每个 root 选择启发式顺序中第一个仍合法且 marginal gain 大于零的 candidate，更新虚拟 `Covered/Used`。
8. dirty root 若没有仍合法的旧 proved relation但仍有正潜力，只发现 `Known` 集合之外的新 candidates。新 candidate 先走 CBS；未解决项才进入一个小 shared repair scorr epoch。已有且仍合法的 proved relation不重复证明。
9. 对 `SELECTED` 列表做一次 topological bundle duplication、combinational cleanup/normalize 和 exact-gain audit。最终 cleanup 保留原 register boundary，不做 sequential latch cleanup；正常选择保证 kill-set 不重叠且每步 marginal gain 大于零，exact AND gain 仅作 assertion/防御检查。`-f` 可额外启用 whole-network shadow audit。

## 3. Proof-only proxy 隔离

shared scorr 不直接 union physical endpoints。proof graph 为每个 root 建一个未结构哈希的 `root & 1` proxy，为每个非恒定 candidate 建独立 `candidate & 1` proxy；constant candidate 使用等价的 `0 & root-anchor` 独立节点（constant-1 取其反相），避免 GIA 禁止两个相同 physical fanin 的断言：

- 不同 roots 永远不会因共享同一 physical divisor 发生传递合类；
- 同一 root 的 all-candidates 共享 root proxy，因此可形成 `{root,c1,c2,...}` 大类并在同一 fixed point 中分别拆分；
- CBS 始终使用真实 physical root/replacement endpoints，proof proxy 只服务 correspondence class。

## 4. Candidate 与 resub 语义

### 4.1 Direct 与 build 分工

constant 和 existing 只由 direct generator 产生。build-only resub 顶层禁止返回 zero-gate existing，以免与 direct 重复；exact literals 仍保留为递归构造叶子。

divisor reservoir 保留 TFI/BFS、MFFC boundary、local、global 和 mixed routes。每条 route 初始化一个 stateful iterator，并调用 `Next` 直到有限候选空间耗尽；exact-template 游标不会为第 q 个 recipe 重新扫描前 q-1 个 recipe。带极性 coverage 排序后，exact pair frontier 保持 B-wide，因此 gate-gate 最多在两个 B-wide pair 列表上枚举，不会退化成物理 divisor pair 的 `O(B^4)` Cartesian search。greedy choice 每次从不可变 OFF/ON 和清空后的 pair scratch 重建，经 recipe 去重后同样保持 B-wide；iterator 另有 `iGreedy < B` 的结构性终止不变量。这是有限候选宇宙的定义，不是 wall-clock/q 超时。

iterator 热路径只检查 recipe shape。recipe 映射到 root candidate 并 canonicalize 后，用不可变 OFF/ON truth tables 做一次完整语义审计；若 canonical recipe 意外改变函数，则恢复 raw recipe 并审计 raw relation。结构错误或两个版本都不满足 relation 的 recipe 会被计数并跳过，而不是触发 assertion。verifier 明确接受并仿真 `x&x`、`x&!x` 这类待 canonicalize 的退化 AND，不会因相同 physical fanin 终止 ABC。所谓 q unlimited 只表示没有人工 top-q 截断，候选宇宙仍受 `B/K/N`、合法 include、有限模板、canonicalization 和有限 greedy diversity 约束，不枚举所有 AIG。

### 4.2 带极性的 include/template 筛选

在 care 内令 `T1` 为 root ON-set、`T0` 为 root OFF-set，literal 的 ON-set 为 `L`：

- OR implicant：`L subset T1`，等价于 `L intersect T0` 为空；
- AND factor：`T1 subset L`，等价于 `complement(L) subset T0`；
- 对 `d` 与 `!d` 都检查；
- binate physical divisor 不按单 literal containment 在外层删除；两 divisor 的四种极性 pair 仅在 pair 与 OFF 不相交且覆盖非空 ON 时进入 cover。

因此例如 `T=1101, d=1000` 时，`d` 是 OR implicant而不是直接 AND factor；AIG 用 complemented AND 构造 OR，不能删除该极性。binate variables 在 pair/template 枚举前重新启用 ranking。

### 4.3 Canonicalization 与排序

recipe canonicalization 包括：交换律 fanin 排序、常量折叠、重复/互补输入、明显 absorption、相同结构 gate 合并、dead gate 删除和同 recipe 去重。simulation dominance 只可影响排序/有限多样性，不作为 formal 完备剪枝。

root 和 divisor 都预计算 CI support。CI overlap 位于 coverage/residual 之后作为安全排序 tie-break，不是硬过滤。

## 5. CLI

常用 root 选项：

- `-P root`：显式选择默认 root scope；
- `-t`：top-1 与 all-candidate sequential 模式切换，默认 top-1；
- `-F/-C/-S`：scorr depth、每 obligation 冲突限和 refinement step 限；
- `-N`：单 recipe 最大 gate 数；
- `-B/-K`：divisor pool 宽度与 TFI 深度；
- `-b`：CBS 每 cube 冲突限；
- `-l/-x`：关闭 existing/build generator；
- `-p`：打印 root-only profile；
- `-f`：启用最终 shadow audit。

旧 `-q/-w/-L/-z/-i/-u/-s` 在 root scope 中只解析以兼容旧脚本，明确打印 deprecated/ignored，并且不能改变 root 主线语义。`window/output` 会打印 frozen 提示。

若输入 GIA 已无 register（例如前置 `scorr` 已完成全部 latch cleanup），`&stran` 打印 combinational no-op 并返回成功；这不是 proof failure，也不会修改网络。

## 6. Profiling 与一致性

`-p` 输出互不重叠的顶层时间桶：

- simulation/signature index；
- root/MFFC/dirty refresh；
- direct constant/existing generation；
- divisor reservoir/CI ranking；
- resub initialization 与 enumeration/canonicalization；
- CBS graph/build、screen 与 solve；
- shared scorr graph/SRM、BMC/base、induction/SAT、resimulation/refinement、fixed-point other；
- post-fixed-point selection/dirty repair；
- final bundle duplication、cleanup、exact-gain audit 和可选 shadow audit。

效果按 `COMB/SEQ × CONSTANT/EXISTING/BUILD` 六格打印 generated、submitted、proved、selected、selected marginal AND/Reg gain。root-only 最终 commit 保留 register boundary，因此当前六格 marginal Reg gain 与最终 exact Reg gain 均为零；字段保留用于 schema 明确性。随后打印 selected roots、总 marginal gain和 cleanup exact gain。

运行时 assertions 校验：

- 六格 selected 之和等于 bundle 大小；
- 六格 marginal gain 之和不大于 cleanup exact gain；
- cleanup exact gain 等于最终 AND 数差；
- sequential `seeded == proved + split + unknown`；
- stateful resub `initialized == exhausted`。

all-candidate 强度/规模指标包括 seeded/proved/split/unknown relations、roots、最大/平均 class size、fixed-point rounds 和 repair epochs。另打印 iterator initialized/next/exhausted/invalid 与三类 dirty 计数。标准回归要求 `invalid=0`；生产输入即使触发防御审计也会跳过坏 recipe，而不是中止整个运行。

## 7. 回归与验证

构建：

```sh
make -j4
```

root-only 回归：

```sh
test/run_stran_regression.sh
```

覆盖样例：

- `stran_comb.blif`：COMB existing/build discovery 与 exact gain；
- `stran_seq.blif`、`stran_seq_only.blif`：代表性 sequential、top-1/all-candidate、完整 fixed point；
- `stran_proxy_roots.blif`：两个 roots 共享 physical endpoint 但 class-max 必须为 2；
- `stran_polarity.blif`：关闭 existing 后必须由 complemented-AND BUILD 实现 OR；
- `&stran_resub_test`：直接断言 `T=1101,d=1000` 的 literal 极性、binate pair 的 OFF/ON 条件、`x&x`/`x&!x` verifier 安全性、public iterator 的 B-wide 有限 exhaustion，以及常量/重复/absorption canonicalization；
- `stran_dirty.blif`：virtual selection 后的 root-free/MFFC dirty；
- `stran_constant.blif`：sequential constant candidate 的 proof proxy、选择、AND cleanup 与 register-boundary 保持；
- `stran_combinational_noop.blif`：无 register 输入返回成功 no-op；
- `-S 0`：incomplete oracle 必须输出 UNKNOWN，不能 selected；
- deprecated 参数组合：结果语义不变并打印 ignored；
- profile parser：六格、sequential 分类、exact gain 与 iterator exhaustion 一致。

每个回归在变换前后写 AIG，并用 `dsec` 检查 sequential equivalence。

真实 benchmark smoke 使用与批处理脚本一致的链路：原始 AIG 写为 base，执行 `&scorr -C 100`，再执行 `&stran -C 100 -b 100 -P root -N 10 -B 64 -K 8 -r`，最后对 base/final 运行 `dsec`。当前验证结果：

- `loopv3.aig`：scorr 后 1298 AND roots；iterator `initialized=22075`、`exhausted=22075`、`next=1038229`、`invalid=0`，约 49 秒完成，最终 `dsec` 等价；
- `simple_alu.aig`：83 roots，正常完成并通过 `dsec`；
- `fib_05.aig`：649 roots，正常完成并通过 `dsec`；
- `gen26.aig`：170 roots，约 7.5 秒完成并通过 `dsec`。

## 8. 明确保留的风险

- all-candidate 仍可能在大型 signature class 上产生很宽的 proof batch；这是算法语义，不是 q 截断遗漏。
- discovery 依赖 reset-reachable samples 只影响候选召回/排序，不影响 correctness；所有 selected 都必须有 CBS 或完整 scorr proof。
- repair 可以产生多个小 scorr epochs，但主 sequential frontier只有一次 shared fixed point；repair 仅处理 virtual commit 后出现的新 candidates。
- q unlimited 在 B=64 的真实设计上仍可能产生百万级 `Next` 调用；现在保证有限耗尽和正确性，但 resub enumeration 仍可能是主要运行时间。
- `window/output` 是冻结兼容代码，不能用本文的 root-only保证推断其性能或 profile 语义。
