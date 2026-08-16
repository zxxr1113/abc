# `&stran -P root` 实现真值文档

本文描述当前代码，而不是未来设计。`root` 是 `&stran` 的默认且唯一在开发的 proof scope；`window` 和 `output/po-ri` 明确冻结，只保留兼容路径，不做算法、QoR 或性能开发。SODC 不属于本算法，`&stran -o` 会被拒绝。

## 1. 正确性边界与状态

一次 root 运行从输入复制出一份 GIA。simulation、candidate discovery、CBS、shared scorr、虚拟选择和 repair 全部引用这份不可变 snapshot；直到最后才执行一次 bundle duplication 和 cleanup。

候选状态严格分为：

- `CANDIDATE`：signature/care 匹配，只是待证明关系；
- `STALE`：root/support 已释放或 marginal gain 已非正；保留 canonical key 去重，但不再占 `q` 或进入证明；
- `TRIED_SEQ`：候选已从发现 frontier 转移到累计 proof portfolio；它不再占用后续 wave 的 `q` 槽位，但 top-1 后续累计前缀会继续把它作为 hypothesis/obligation 重证；
- `PROVED_COMB`：CBS 在所有自由 PI/RO 状态上证明；
- `PROVED_SEQ`：shared scorr 没有全局提前停止，并且标准 BMC/refinement/induction fixed point 后 root/candidate 仍在同一类；单个无关 obligation 的 UNKNOWN 不会污染该关系；
- `SELECTED`：proved relation 仍结构合法、动态 marginal gain 为正，并被 root-major 虚拟串行选择。

“加入 fixed point”不等于 proved。scorr 最终分类是：

- `PROVED`：完整 oracle 后仍同类；
- `UNPROVED(split)`：完整 oracle 后已拆类；
- `UNKNOWN`：整个 correspondence 调用达到 step/iteration/总冲突限制或其他全局提前停止；ordinary per-output UNKNOWN 按标准 scorr 语义只移除对应 output 的 candidate，不升级成全 batch UNKNOWN。

`Free/Covered/Used` 只描述所有 proof wave 完成后的虚拟串行选择：

- `Covered` 是已选 candidate 的动态 MFFC kill-set；
- `Used` 是已选 recipe 的外部 support；
- 它们不修改 snapshot，但会改变后续 root 的合法性和 marginal MFFC。

## 2. 端到端流程

1. 从 reset 初态做多帧 bit-parallel simulation，建立 signature index，并收集全部 AND roots。整个发现/证明阶段使用同一不可变 GIA snapshot。
2. 每个 discovery wave 按动态 MFFC 潜力处理 root，生成新的 constant、existing、Build candidates。root 内排序固定为 constant、existing、Build；Build 再按 gate 数、exact template、coverage/residual、CI overlap 和稳定 canonical key 排序。
3. `q>0` 只限制当前未转移的 Build frontier；转入 proof portfolio 后立即释放槽位，后续 wave 从确定性 iterator 中跳过 `Known` recipe 并继续补充。`q=0` 在 wave 1 穷尽 iterator，后续 wave 只消费已保留的有序 frontier，不重复扫描。
4. 默认 top-1 每 wave、每 root 只把下一个启发式候选加入累计 portfolio，并对当前整个排序前缀执行一次 combined CBS+scorr proof。各前缀的 proved relations 取并集，因此增加 wave 不会丢失较小前缀已经建立的证明。
5. `-t` all-candidate 每 wave 把当前全部合法 frontier 加入 portfolio，发现结束后只对完整集合执行一次 combined proof。`q=0` 的超宽 class 在有限预算下另保留 primary q=1 portfolio 作为 QoR fallback，再与完整集合的 proved relations 取并集。
6. 每次 combined proof 先用 CBS 分类组合恒真关系；未由 CBS 解决的关系进入标准 scorr BMC/refinement/induction。CBS-proved relations 仍作为 induction helpers 留在同一个 speculative hypothesis 中，但不计作 sequential obligations。
7. correspondence 必须约束真实 physical root 和 candidate endpoints，使关系连接真实 next-state fanout。只有 free PI endpoint 使用功能等价的 proof proxy；不能对内部 root/candidate 使用无 fanout 的 `x&1` 隔离节点。
8. 所有 prefix/full proof 完成后，对 proved 并集按正确的动态 marginal MFFC 做一次 root-major 虚拟选择。动态 MFFC 使用临时 deref/ref，正确处理 reconvergence，并把已 `Covered` 节点移除的 fanin 引用计入后续 kill-set；candidate support、`Used` 和显式 boundary 是停止点。
9. 对最终 `SELECTED` 列表执行一次 topological bundle duplication、combinational cleanup/normalize 和 exact-gain audit。cleanup 保留 register boundary；`exact-gain` 必须严格等于最终 AND before/after 差值。`-f` 可额外启用 whole-network shadow audit。

## 3. Correspondence endpoint 语义

内部 AND/RO candidate 与 root 必须直接使用 physical endpoint。把二者包装成无 fanout 的 `x&1` 虽然组合等价，却切断了它们与 next-state logic 的连接，使 shared invariant 无法跨 frame 传播。

free PI 没有 frame-to-frame definition，仍使用一个功能等价的普通 AND proxy 作为 class node；常量由 GIA constant endpoint直接处理。多个 candidate 属于同一 root 时共享 physical root class，CBS-proved relations也保留在该 class 中作为 induction helpers。

## 4. Candidate 与 resub 语义

### 4.1 Direct 与 build 分工

constant 和 existing 只由 direct generator 产生。direct 先检查两个常量，再在当前 TFI divisor pool 中检查 exact literal 的两个极性。build-only resub 顶层禁止返回 zero-gate existing，以免与 direct 重复；exact literals 仍保留为递归构造叶子。

当前 root 主线只有一条 divisor route：从 root 按 TFI 距离做 BFS。用于路由的 exclusion mask 只沿初始 `ref==1` exclusive tree 前进，它不是 MFFC 计算；reconvergent 的较早内部节点仍是合法 divisor，因为 replacement support 会把它保活，随后 exact dynamic MFFC 会以该 support 为 boundary 重算真实 gain。`K` 是 BFS 深度，`B` 是物理 divisor 数；正反两个 literal 不重复占 B。TFI 拓扑关系排除了 root TFO。旧 boundary/local/global/mixed helper 留在冻结兼容代码中，当前 root discovery 不调用。

每次 root discovery 使用有限 stateful iterator。论文式顺序为：constant、exact TFI literal、1-gate unate cover、小型 2/3-gate exact template、recursive unate/binate greedy decomposition。unate literal 和 pair 都按 ON coverage/residual reduction 降序；binate ranking 已启用。`Known` 对 canonical recipe 做跨 wave 去重；只有尚未送入 SEQ 的有效 Build 才占 q slot，`TRIED_SEQ`、proved 或结构失效的候选都会释放槽位。达到 q 后本 wave 停止，下一 wave 从确定性顺序中跳过 Known recipe，补入不同的新候选。

带极性 coverage 排序后，exact pair frontier 保持 B-wide，因此 gate-gate 最多在两个 B-wide pair 列表上枚举，不会退化成物理 divisor pair 的 `O(B^4)` Cartesian search。greedy choice 每次从不可变 OFF/ON 和清空后的 pair scratch 重建，经 recipe 去重后同样保持 B-wide；iterator 另有 `iGreedy < B` 的结构性终止不变量。`q` 是返回 frontier 限制，不是 wall-clock 超时。`q=0` 运行有限 iterator 直到 exhaustion；`q>0` 达到 frontier 宽度后记录 `capped`，由后续 wave 继续分页。

iterator 热路径只检查 recipe shape。recipe 映射到 root candidate 并 canonicalize 后，用不可变 OFF/ON truth tables 做一次完整语义审计；若 canonical recipe 意外改变函数，则恢复 raw recipe 并审计 raw relation。结构错误或两个版本都不满足 relation 的 recipe 会被计数并跳过，而不是触发 assertion。verifier 明确接受并仿真 `x&x`、`x&!x` 这类待 canonicalize 的退化 AND，不会因相同 physical fanin 终止 ABC。候选宇宙受 `B/K/N/q`、合法 include、有限模板、canonicalization 和有限 greedy diversity共同约束，不枚举所有 AIG。

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
- `-t`：切换为 all-candidate；默认 top-1 按 wave 扩展并证明累计排序前缀；
- `-F/-C/-S`：scorr depth、每 obligation 冲突限和 refinement step 限；
- `-N`：单 recipe 最大 gate 数；
- `-B/-K`：TFI divisor pool 的物理节点宽度与 BFS 深度，默认 `B=16, K=8`；
- `-q`：每个 root 当前保留的 canonical Build candidates；`0` = unlimited/exhaust iterator，`1..64` = 有限 frontier，默认 8；
- `-w`：同一 immutable snapshot 上的有序 candidate waves，范围 1..64；top-1 每 wave 扩展并重证累计前缀，all-candidate 用它为有限 q 分页；
- `-b`：CBS 每 cube 冲突限；
- `-l/-x`：关闭 existing/build generator；
- `-p`：打印 root-only profile；
- `-f`：启用最终 shadow audit。

旧 `-L/-z/-i/-u/-s` 在 root scope 中只解析以兼容旧脚本，明确打印 deprecated/ignored。`-q/-w` 是有效 root 参数；`window/output` 会打印 frozen 提示。

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

同一批数据另以稳定的 `stran-root experiment-*-profile: schema=3` 行输出。`scripts/stran_profile.py` 和 `scripts/bench_scorr_then_stran.py` 同时解析旧 direct schema 与 root-only schema=3；CSV 保留粗粒度兼容列，并新增 root refresh、divisor、resub、CBS、scorr、selection、bundle/cleanup/audit 的独立秒数以及六格 generated/submitted/proved/selected/gain。解析回归要求所有 `profile_*` 字段为数值，不能在 `-p` 成功时退化为 `N/A`。

运行时 assertions 校验：

- 六格 selected 之和等于 bundle 大小；
- 六格 marginal gain 之和不大于 cleanup exact gain；
- cleanup exact gain 等于最终 AND 数差；
- sequential proof-event `candidates == proved + split + unknown`；
- `seeded == candidates + comb-helper-seeds`；
- stateful resub `initialized == exhausted + capped`。

top-1 会在多个累计前缀中重复提交早期 relation，因此 `candidates/seeded/proved/split/unknown/roots` 是 proof-event 计数，而不是 unique relation 数；all-candidate 的完整 proof 通常每个 relation 一次，`q=0` primary fallback 会额外产生一组 proof events。独立的 `cumulative portfolio` 行报告 `unique-candidates/unique-proved/proof-calls`。另打印 iterator initialized/next/exhausted/capped/invalid 与三类 dirty 计数。标准回归要求 `invalid=0`。

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
- `stran_proxy_roots.blif`：两个 roots 的 PI endpoint proxy 与 physical-root correspondence；
- `stran_polarity.blif`：关闭 existing 后必须由 complemented-AND BUILD 实现 OR；
- `-q 1`：iterator 必须出现 `capped>0`；`-q 0` 必须接受并以 `capped=0` exhaustion；两者都满足 `initialized == exhausted + capped`；
- `&stran_resub_test`：除 iterator、极性、canonicalization 外，还检查 reconvergent deref/ref MFFC、candidate boundary、Covered 引用扣除和 Used cutpoint；
- `stran_dirty.blif`：virtual selection 后的 root-free/MFFC dirty；
- `stran_constant.blif`：sequential constant endpoint、选择、AND cleanup 与 register-boundary 保持；
- `stran_combinational_noop.blif`：无 register 输入返回成功 no-op；
- `-S 0`：全局提前停止必须输出 UNKNOWN，不能 selected；`-w 2` 必须加入不同 relation，并在第二次 proof 中重证累计前缀；`gen26 -C 1` 必须在内部存在 UNKNOWN obligation 时仍逐类产出 proved/split，并通过 `dsec`；
- deprecated 参数组合：`-L/-z/-i/-u/-s` 结果语义不变并打印 ignored，同时 `-q/-w` 仍改变 Build frontier/wave；
- profile parser：schema=3 的时间桶、六格、sequential 分类、exact gain 与 iterator accounting 一致。

每个回归在变换前后写 AIG，并用 `dsec` 检查 sequential equivalence。

当前 `loopv3.aig` reference 使用 `-C 500 -b 500 -P root -p -V 0 -N 10 -B 64`。`-t -q 0 -w 1` 穷尽 1397 个 root iterator（`capped=0`），完整 portfolio 加 primary fallback 后得到 `1397 -> 862`、`exact-gain=535`；有限 `-t -q 64 -w 1` 与 top-1 `-q 8 -w 5` 同样得到 `1397 -> 862`。三种配置都以 `&read` 后写出的 canonical baseline 执行 `dsec -n`。

修正 deref/ref MFFC 后，所选 68 个 root 的 marginal AND gain 之和也是 535，与 cleanup exact gain 一致；最终统计仍以 `exact-gain == AND-before - AND-after` 为准。

## 8. 明确保留的风险

- all-candidate 仍可能形成很宽的 speculative class；`q=0` 会穷尽 iterator，并用 primary q=1 proof 保护有限预算下的 QoR，但完整 batch 的内存和 fixed-point 成本仍可能较高。
- discovery 依赖 reset-reachable samples 只影响候选召回/排序，不影响 correctness；所有 selected 都必须有 CBS 或完整 scorr proof。
- top-1 每个 wave 重证累计前缀并对 proved relation 取并集；这是结果单调性保护，也意味着早期 relation 会产生重复 proof events。有限 q 的新 wave 会重新初始化 iterator 并跳过 Known recipe，深 wave 仍有确定性前缀重扫开销。
- exact dynamic MFFC 当前为每次查询复制 reference snapshot，再执行带 Covered/Used/boundary 的 deref/ref；它优先保证正确性，在更大设计上可能成为后续可优化的时间/内存热点。
- `B` 限制进入构造器的物理 divisor，不等于实际可形成的 literal/pair 数；include/coverage 会显著缩小合法集合，但没有正 marginal-gain candidate 的 root 仍可能走到 iterator exhaustion。即使有 q，resub enumeration 仍可能是主要运行时间，应同时观察 `next/exhausted/capped` 与时间桶。
- `window/output` 是冻结兼容代码，不能用本文的 root-only保证推断其性能或 profile 语义。
