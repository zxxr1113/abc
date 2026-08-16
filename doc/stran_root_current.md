# `&stran -P root` 实现真值文档

本文描述当前代码，而不是未来设计。`root` 是 `&stran` 的默认且唯一在开发的 proof scope；`window` 和 `output/po-ri` 明确冻结，只保留兼容路径，不做算法、QoR 或性能开发。SODC 不属于本算法，`&stran -o` 会被拒绝。

## 1. 正确性边界与状态

一次 root 运行由若干 rebuild/commit round 组成。每个 phase 从当前网络复制一份不可变 GIA snapshot；simulation、candidate discovery、CBS、可选 shared scorr 和虚拟选择只引用该 snapshot。phase 末尾立即 bundle duplication、cleanup 和 commit，随后丢弃全部 object-indexed 状态。下一 phase/round 在 commit 后的新 GIA 上重新建 simulation、root/MFFC、divisor、candidate 和 proof graph。

候选状态严格分为：

- `CANDIDATE`：signature/care 匹配，只是待证明关系；
- `STALE`：同一 phase 内 root/support 已释放或 marginal gain 已非正；不进入证明或选择；
- `TRIED_SEQ`：候选已从当前有界 frontier 转移到本 phase 的 proof batch；phase 结束后不持久化；
- `PROVED_COMB`：CBS 在所有自由 PI/RO 状态上证明；
- `PROVED_SEQ`：shared scorr 没有全局提前停止，并且标准 BMC/refinement/induction fixed point 后 root/candidate 仍在同一类；单个无关 obligation 的 UNKNOWN 不会污染该关系；
- `SELECTED`：proved relation 仍结构合法、动态 marginal gain 为正，并被全局 max-gain greedy 虚拟串行选择。

“加入 fixed point”不等于 proved。scorr 最终分类是：

- `PROVED`：完整 oracle 后仍同类；
- `UNPROVED(split)`：完整 oracle 后已拆类；
- `UNKNOWN`：整个 correspondence 调用达到 step/iteration/总冲突限制或其他全局提前停止；ordinary per-output UNKNOWN 按标准 scorr 语义只移除对应 output 的 candidate，不升级成全 batch UNKNOWN。

`Free/Covered/Used` 只描述当前 phase proof 完成后的虚拟串行选择：

- `Covered` 是已选 candidate 的动态 MFFC kill-set；
- `Used` 是已选 recipe 的外部 support；
- 它们不修改 snapshot，但会改变后续 root 的合法性和 marginal MFFC。

## 2. 端到端流程

1. round 开始于上一次 commit 后的 GIA。先进入 COMB closure；每个 COMB pass 都重新建立 simulation/signature、root/MFFC、divisor pool 和 candidate frontier。
2. 每个 root 一次性生成最多 `q` 个 canonical Build candidates；`q=0` 穷尽该 root 的有限 iterator。默认同时生成 constant/existing；`-y` 完全跳过 direct generator，只研究 Build。
3. 当前有界 frontier 全部进入 CBS batch。CBS 在任意 PI/RO 状态上证明组合恒真的 relation；按动态 max-gain greedy 选择所有仍合法的正 gain relation，并立即 commit/cleanup。
4. 只要 COMB commit 使 AND 数下降，就在新 GIA 上重建并再跑一个 COMB pass；无下降时 COMB closure 到达 fixed point。
5. 随后在 COMB-closed GIA 上重新发现同样的有界 frontier并再次 CBS screen。未由 CBS 证明的 relation 一次性进入 shared scorr BMC/refinement/induction；CBS-proved relation 仍可作为 induction helper，但不计作 sequential obligation。
6. COMB/SEQ proved relation 的提交都使用同一个全局 max-gain greedy：每步重算所有剩余 candidate 的动态 marginal gain，选择最大者，局部更新 live references 和 `Covered/Used`，直到没有正 gain candidate。gain 相同时依次用动态 MFFC、reverse topology 和稳定 candidate heuristic 打破平局。
7. SEQ phase 末尾立即 bundle duplication、cleanup、exact-gain audit 和 commit。若 AND 数下降，下一 round 从新图重新开始 COMB closure；若无下降，同一图再次发现只会得到相同有界 frontier，因此提前终止。
8. correspondence 必须约束真实 physical root 和 candidate endpoints，使关系连接真实 next-state fanout。只有 free PI endpoint 使用功能等价的 proof proxy；不能对内部 root/candidate 使用无 fanout 的 `x&1` 隔离节点。
9. 每次 commit 的 cleanup 保留 register boundary，且 `exact-gain` 必须严格等于该 phase 的 AND before/after 差值。`-f` 可额外启用 whole-network shadow audit。

## 3. Correspondence endpoint 语义

内部 AND/RO candidate 与 root 必须直接使用 physical endpoint。把二者包装成无 fanout 的 `x&1` 虽然组合等价，却切断了它们与 next-state logic 的连接，使 shared invariant 无法跨 frame 传播。

free PI 没有 frame-to-frame definition，仍使用一个功能等价的普通 AND proxy 作为 class node；常量由 GIA constant endpoint直接处理。多个 candidate 属于同一 root 时共享 physical root class，CBS-proved relations也保留在该 class 中作为 induction helpers。

## 4. Candidate 与 resub 语义

### 4.1 Direct 与 build 分工

constant 和 existing 只由 direct generator 产生。direct 先检查两个常量，再在当前 TFI divisor pool 中检查 exact literal 的两个极性。build-only resub 顶层禁止返回 zero-gate existing，以免与 direct 重复；exact literals 仍保留为递归构造叶子。

当前 root 主线只有一条 divisor route：从 root 按 TFI 距离做 BFS。用于路由的 exclusion mask 只沿初始 `ref==1` exclusive tree 前进，它不是 MFFC 计算；reconvergent 的较早内部节点仍是合法 divisor，因为 replacement support 会把它保活，随后 exact dynamic MFFC 会以该 support 为 boundary 重算真实 gain。`K` 是 BFS 深度，`B` 是物理 divisor 数；正反两个 literal 不重复占 B。TFI 拓扑关系排除了 root TFO。旧 boundary/local/global/mixed helper 留在冻结兼容代码中，当前 root discovery 不调用。

每次 root discovery 使用有限 stateful iterator。论文式顺序为：constant、exact TFI literal、1-gate unate cover、小型 2/3-gate exact template、recursive unate/binate greedy decomposition。unate literal 和 pair 都按 ON coverage/residual reduction 降序；binate ranking 已启用。`Known` 只在当前 phase 内对 canonical recipe 去重。达到 `q` 后本 phase 停止；发生 commit 时不保留 iterator、canonical key、object ID 或 helper，下一 phase 在新图上从头发现。

带极性 coverage 排序后，exact pair frontier 保持 B-wide，因此 gate-gate 最多在两个 B-wide pair 列表上枚举，不会退化成物理 divisor pair 的 `O(B^4)` Cartesian search。greedy choice 每次从不可变 OFF/ON 和清空后的 pair scratch 重建，经 recipe 去重后同样保持 B-wide；iterator 另有 `iGreedy < B` 的结构性终止不变量。`q` 是每个 phase、每个 root 的返回 frontier 限制，不是 wall-clock 超时。`q=0` 运行有限 iterator 直到 exhaustion；`q>0` 达到 frontier 宽度后记录 `capped`。下一 round 会在 commit 后的新图上重新枚举，而不是继续旧 iterator 分页。

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
- `-t`：兼容开关；round 模式始终证明当前有界 `q` frontier，因此该开关不再改变算法并会打印提示；
- `-F/-C/-S`：scorr depth、每 obligation 冲突限和 refinement step 限；
- `-N`：单 recipe 最大 gate 数；
- `-B/-K`：TFI divisor pool 的物理节点宽度与 BFS 深度，默认 `B=16, K=8`；
- `-q`：每个 root 当前保留的 canonical Build candidates；`0` = unlimited/exhaust iterator，`1..64` = 有限 frontier，默认 8；
- `-w`：最大 rebuild/commit rounds，范围 1..64；SEQ 没有产生 commit 时会提前终止；
- `-y`：Build-only discovery，禁止 constant/existing direct candidates；COMB Build 与 SEQ Build 仍分别统计；
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
- post-fixed-point dynamic max-gain selection/dirty repair；
- final bundle duplication、cleanup、exact-gain audit 和可选 shadow audit。

每个 phase 都按 `COMB/SEQ × CONSTANT/EXISTING/BUILD` 六格打印 generated、submitted、proved、selected、selected marginal AND/Reg gain。COMB-only closure 中未通过 CBS 的候选不会误计为 SEQ submitted。root-only commit 保留 register boundary，因此当前六格 marginal Reg gain 与最终 exact Reg gain 均为零；字段保留用于 schema 明确性。随后打印该 phase 的 selected roots、总 marginal gain和 cleanup exact gain，命令末尾另打印跨 round 的 AND 总结。

同一批数据另以稳定的 `stran-root experiment-*-profile: schema=3` 行输出。`scripts/stran_profile.py` 和 `scripts/bench_scorr_then_stran.py` 会累加同一命令中的所有 COMB pass、SEQ phase 和 round；旧 CSV 兼容列也必须累加，不能由最后一个空 phase 覆盖先前已提交的 Build 贡献。CSV 另含 root refresh、divisor、resub、CBS、scorr、selection、bundle/cleanup/audit 的独立秒数以及六格 generated/submitted/proved/selected/gain。

运行时 assertions 校验：

- 六格 selected 之和等于 bundle 大小；
- 六格 marginal gain 之和不大于 cleanup exact gain；
- cleanup exact gain 等于最终 AND 数差；
- sequential proof-event `candidates == proved + split + unknown`；
- `seeded == candidates + comb-helper-seeds`；
- stateful resub `initialized == exhausted + capped`。

每个 phase 的 `candidates/seeded/proved/split/unknown/roots` 是该次 proof-event 计数；跨 round 可能在不同图上重新发现功能相似的 relation，profile parser 只做事件/贡献求和，不把 object ID 当成跨图 identity。独立的 `bounded portfolio` 行报告本 phase 的 `unique-candidates/unique-proved/proof-calls`。另打印 iterator initialized/next/exhausted/capped/invalid 与三类 dirty 计数。标准回归要求 `invalid=0`。

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
- `stran_seq.blif`、`stran_seq_only.blif`：有界 frontier、完整 fixed point、SEQ commit 和 round stop；
- `stran_proxy_roots.blif`：两个 roots 的 PI endpoint proxy 与 physical-root correspondence；
- `stran_polarity.blif`：关闭 existing 后必须由 complemented-AND BUILD 实现 OR；`-y` 下 direct 六格全零而 Build 仍可提交；
- `-q 1`：iterator 必须出现 `capped>0`；`-q 0` 必须接受并以 `capped=0` exhaustion；两者都满足 `initialized == exhausted + capped`；
- `&stran_resub_test`：除 iterator、极性、canonicalization 外，还检查 reconvergent deref/ref MFFC、candidate boundary、Covered 引用扣除和 Used cutpoint；
- `stran_dirty.blif`：virtual selection 后的 root-free/MFFC dirty；
- `stran_constant.blif`：sequential constant endpoint、选择、AND cleanup 与 register-boundary 保持；
- `stran_combinational_noop.blif`：无 register 输入返回成功 no-op；
- `-S 0`：全局提前停止必须输出 UNKNOWN，不能 selected；`-w 2` 在无 commit 时必须只完成一轮；`gen26 -C 1` 必须在内部存在 UNKNOWN obligation 时仍逐类产出 proved/split，并通过 `dsec`；
- profile parser：schema=3 的时间桶、六格、sequential 分类、exact gain 与 iterator accounting 一致，并累加多个 phase。

每个回归在变换前后写 AIG，并用 `dsec` 检查 sequential equivalence。

旧 cumulative-wave 的 `loopv3` 数字不能作为新 round controller 的 reference。新实验应同时记录 `q/w/C/b/-y`、末尾 `rounds summary`、每个 phase 的 scorr obligations，并以 `&read` 后写出的 canonical baseline 执行 `dsec -n`。最终结构收益以跨 round 的初始/最终 AND 数为准；每个 phase 仍要求 `exact-gain == AND-before - AND-after`。

## 8. 明确保留的风险

- 当前有界 frontier 会一次性进入同一个 speculative batch；`q=0` 仍可能形成很宽的 class，增加 temporary GIA/SRM、冲突和 fixed-point 成本。round commit 会缩小下一张图，但不能降低当前超宽 batch 的成本。
- discovery 依赖 reset-reachable samples 只影响候选召回/排序，不影响 correctness；所有 selected 都必须有 CBS 或完整 scorr proof。
- 有限 `q` 可能在某一 snapshot 上截断较深 recipe；只有发生 commit 才会启动下一 round，因此不会把 `w` 当成无结构变化时的 iterator 分页。要提高召回应直接增大 `q`，再用适中的 `w` 捕获 commit 后出现的新机会。
- discovery/dirty refresh 的 exact dynamic MFFC 仍为每次查询复制 reference snapshot；post-proof selection 已改为一份 live refs 加局部 fanin-ref 更新，不复制或重建 GIA。大 proved pool 上剩余热点是每轮扫描所有候选并执行可逆 deref/ref，而不是 reference snapshot 的全图复制。
- `B` 限制进入构造器的物理 divisor，不等于实际可形成的 literal/pair 数；include/coverage 会显著缩小合法集合，但没有正 marginal-gain candidate 的 root 仍可能走到 iterator exhaustion。即使有 q，resub enumeration 仍可能是主要运行时间，应同时观察 `next/exhausted/capped` 与时间桶。
- `window/output` 是冻结兼容代码，不能用本文的 root-only保证推断其性能或 profile 语义。
