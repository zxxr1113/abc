# `&stran -P root` 当前算法

本文是当前实现的真值文档。算法目标是“小 batch、多 page、多 wave、多 commit”：
commit 改变永久电路，跨 commit 的正式 proved relation 作为 induction helper 增强后续
证明。

## 1. 正确性边界

每个 proof pass 使用一张 immutable GIA snapshot。simulation、signature index、root
MFFC、divisor pool、resub iterator、candidate object ID 与临时 proof graph 都只属于该
snapshot。

未 commit helper 只允许存在于两处：

- retained history 的轻量 certificate metadata；
- 当前 batch 的临时 H/O proof graph 与 SRM。

它们不能向永久 GIA 添加节点。只有动态 gain 为正并被 `SELECTED` 的 recipe 才进入
bundle duplication；cleanup 后立即做 exact AND-gain audit。发生 commit 后，所有
object-indexed iterator/cache 被销毁，在新图上 remap certificate 并重新 discovery。

Simulation 仅用于 candidate 筛选和排序。最终证明由组合 CBS 或 shared scorr 完成；
helper cap 只会降低 induction strength，不会把未证明关系变成已证明关系。

## 2. 三条独立 candidate lane

### Constant

只检查并生成 `root = const0` 和 `root = const1`。该 lane 不使用 TFI divisor pool，
也不受 `q` 限制。

### Existing

启动 snapshot 时构造全局 simulation-signature index。对每个 root 查找 signature bucket
中的所有双极性 literal，并要求：

- endpoint 是合法 CI/RO/AND candidate；
- object 严格拓扑早于 root；
- 完整 simulation signature 与 root 相同。

命中只是 proof obligation，随后仍走 CBS/scorr。Existing 不受局部 TFI pool、`B`、
`K` 或 `q` 限制，也绝不把全局节点偷渡进 Build pool。

### Build

Build 只从 root 的 TFI 收集 divisor。若 `B>0`，先收集
`max(4B, B+32)` 的较大 reservoir（同时受 `K`/结构合法性限制），计算 simulation
separation 与 CI-overlap rank，按确定性顺序取 top-B，再把这个实际向量交给 stateful
resub iterator。`B=0` 保留完整允许 TFI。

Iterator 产生 canonical recipe；结构与 simulation audit 失败的 recipe 被安全丢弃。
`q` 是每 root、每 page 的 Build yield 数，不限制 Constant/Existing。

## 3. Stateful page controller

对一张 snapshot，每个 root 有独立且持久的状态：direct cursor、ranked divisor pool、
resub iterator、yield/page 序号与 exhaustion 标志。

1. round 先运行 COMB closure；随后运行 SEQ。每个 pass 都从当前图建立 snapshot。
2. scheduler 以 round-robin root 顺序拉取最多 `A` 个新 obligations。每个 root 本页
   最多产生 `q` 个 Build，direct candidates 先行且不占 Build q。
3. 若本页没有 commit，snapshot 不变，下一页继续同一 iterator；不重新初始化、不重复
   已见 candidate。
4. 一旦正式 proved pool 中出现 positive dynamic-gain relation，立即运行全局
   max-marginal-gain greedy，形成 bundle 并 commit。所有 live iterator 记为
   `snapshot-discarded`。
5. 新图重新建立 COMB closure；SEQ commit 后进入下一 round。没有 commit 且 iterator
   全部 exhaustion，或达到 `U` page limit，则该 pass 结束。

没有 UNKNOWN/hard-candidate retry queue。UNKNOWN 只按现有 batch proof 语义分类；一个
hard obligation 不会创建第七条调度 lane，也不会触发专门高预算重试。

## 4. Helper admission、H/O 与跨 commit history

Candidate 的即时 gain 不再决定它能否成为证明义务或 helper。正式 proved relation 即使
当前 `gain <= 0`，也可进入 retained history；commit 前始终重新计算真实 dynamic gain，
只选择 `gain > 0`。

Retained history 保存所有仍可 remap、拓扑合法、结构有效且非 trivial 的正式证书。
已物理 commit/selected、失效、无法 remap 的关系删除。每次新 snapshot 都重新验证和
remap；没有保存旧图 iterator 或 cache。

Shared SRM 输入显式拆为：

- H：已正式证明的 active helper hypotheses；
- O：当前 page 的新 obligations。

临时 correspondence classes seed `H ∪ O`，但 query PO、返回 status 和
`proved/split/unknown` 只针对 O。H 不重复证明。Profile 中
`seeded = candidates + comb-helper-seeds`，其中 `candidates` 就是 O。

## 5. 两层 helper manager

Retained history 不按关系数量粗暴截断。每个 batch 从 retained metadata 选择 active
basis：

1. canonical candidate dedup；
2. direct signed-equivalence relation 用 union-find 压缩为 spanning forest，删除传递冗余；
3. 依据当前 O 的 TFI/support 相关性、class leverage、direct edge 偏好与 recipe gate
   cost 做确定性排序；
4. 同时约束 H+O relation 数、unique endpoints、helper recipe gates、class width 与
   estimated SRM nodes。

小历史在 cap 内全部激活。未选中的 relation 记为 dormant，证书仍保留；后续 obligation
cone 改变时可重新激活。Dormant helper 不物化 endpoint proxy 或 recipe gate。

## 6. Proof 与 commit

COMB pass 对 O 运行 CBS。所有 free PI/RO 状态上成立的 relation 标为
`PROVED_COMB`。SEQ pass 先 CBS screen，再将未解决 O 与 active H 送入 shared scorr；
fixed point 后仍同类的 O 标为 `PROVED_SEQ`。

Greedy commit manager 对全部 retained/new proved relation 反复重算 MFFC/support 下的
真实 marginal gain，每步选择最大正 gain，并虚拟更新 `Covered/Used/live refs`。该动态
逻辑没有改成静态排序。最终只 commit selected bundle，cleanup 后要求 profile 的
`cleanup-exact-AND` 与实际 `AND-before - AND-after` 一致，并可用 `-f` 做 whole-miter
shadow audit。

## 7. Profile 口径

主要机器可读/可审计行：

- `experiment-time profile`：各 phase 时间桶；
- `effect matrix`：`COMB/SEQ × CONSTANT/EXISTING/BUILD` 的 generated、submitted、
  proved、selected 与 marginal gain；
- `paged portfolio`：pages、same-snapshot continuations、new-proved、
  history-proved-selected、proof calls 与 exhaustion；
- `helper batch/history`：retained、active、dormant、dedup、invalidated、classes、
  endpoints、materialized gates、H+O batch width、SRM nodes；
- `resub iterator`：initialized、next、exhausted、q-page-stops、snapshot-discarded、invalid。

`q-page-stops` 是非终态，一个 iterator 可以多次 page-stop。终态不变量是
`initialized == exhausted + snapshot-discarded`。

`new-proved` 只计当前 snapshot 新证明的 O；`history-proved-selected` 计本 phase 从已有
证书中直接选中的 relation。因此 phase-local selected 可以大于 new-proved，这不是统计
错误。Active/dormant 是 materialization event 口径，retained 是 metadata 水位；不可用
`active-events + dormant-events == retained` 推断单个 batch。

## 8. 验证

```sh
make -j4
./abc -q '&stran_resub_test'
ABC_BIN=./abc test/run_stran_regression.sh
```

可复现的小 batch sequential 例子：

```sh
./abc -q 'read_blif test/stran_seq_only.blif; strash; \
  write_aiger /tmp/stran-before.aig; &get; \
  &stran -P root -p -q 1 -A 1 -L 4 -w 2; \
  &write /tmp/stran-after.aig; \
  dsec /tmp/stran-before.aig /tmp/stran-after.aig'
```

该 fixture 会显示无 commit 时 `continuations>0`，后续 SEQ batch 的
`retained=1 active=1`、`candidates=1 seeded=2`，发生 SEQ commit 后在新图重建，并由
`dsec` 验证 sequential equivalence。

Dormant 物化边界可用 `-E 1` 复现：helper 行应为
`retained=1 active=0 dormant=1 materialized-gates=0`，最终仍只由 selected commit 改变
永久 AND。

若仓库另有 `benchmark/gen26.aig`，可运行：

```sh
./abc -q '&read benchmark/gen26.aig; &write /tmp/gen26-before.aig; \
  &stran -P root -p -q 1 -A 4 -L 16 -U 2 -w 2; \
  &write /tmp/gen26-after.aig; dsec /tmp/gen26-before.aig /tmp/gen26-after.aig'
```

当前 checkout 不保证携带该 benchmark；标准回归会在缺失时明确 SKIP，并使用仓库内的
sequential fixtures 完成等价性、分页与 helper 测试。

## 9. 已知算法局限

- Simulation 签名可能漏召回 candidate，但不能造成错误 commit。
- Helper active basis 是确定性的相关性启发式，不保证找到最强 induction basis；cap 越小，
  可能证明的 O 越少。
- `B=0`、`q=0` 与宽 `A/L` 组合仍可能使有限搜索和临时 SRM 很大。
- Retained certificate 只在结构/topology remap 仍有效时复用；trivial、selected 或失效
  relation 会删除。
- UNKNOWN 不做专门重试。只有真实 commit 后新图上的自然 rediscovery 可能再次遇到功能
  相关的 relation。
