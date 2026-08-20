# `&stran` 当前 root-only 算法

## Candidate 三条 lane

每个 root 独立维护 candidate discovery state。

1. **Constant**：只生成 `root=0` 和 `root=1` 两个关系，并用 simulation/CBS 筛选。
2. **Existing**：使用全局 signature index 搜索所有拓扑更早、endpoint 合法的 CI、RO、
   AND literal，包含双极性。Simulation 只负责筛选，最终仍由 CBS/scorr formal proof。
3. **Build**：只使用 root 的 TFI divisor pool。先收集大于最终 B 的 reservoir，按
   simulation separation、CI overlap 等排序，再将 top-B 交给 stateful resub iterator。

Global Existing 永远不会进入 Build divisor pool。`q` 只约束 Build：每个 root、每个
wave 拉取 q 个新 Build candidate；`q=0` 耗尽 iterator。

## All-current-candidate wave

一个 wave 遍历所有 live roots。对每个 root：

```text
O_r = 本 snapshot 尚未提交的全部 Constant/Existing
      + Build iterator 接下来的 q 个唯一 candidate
```

全局 obligation 集合 `O=∪O_r`。`O` 中每个 candidate 都进入 shared proof，不做 top-1、
obligation cap 或 relation cap。已在同一 snapshot 尝试过的 direct relation不会重复；
无 commit 时下一 wave 只继续各 root 的 Build iterator。

## Proof history 与 helper

所有正式 proved relation 都以轻量 metadata 保留，即使当前动态 gain 为 0。commit 前
始终重新计算真实 gain，只有 `gain>0` 才能 selected。

Helper 开关只控制历史证明是否进入下一次 induction：

```text
helper on : H = 全部仍合法、未 selected、exact-dedup 的 retained proofs
helper off: H = ∅
```

两种模式都保留相同 history，因而 helper-off 不会改变历史 relation 未来成为正增益
commit candidate 的机会。没有 relevance selector、spanning forest，也没有 relation、
endpoint、gate、class width 或 SRM node 截断。

临时 proof graph materialize `H∪O`，SRM seed `H∪O`，但只给 `O` 创建 query/output并
返回新的 proof status；`H` 不重复证明。发生 commit 时，selected/trivial/失效 relation
删除，其余证书拓扑 remap 到新图。未 commit helper 绝不写入永久 GIA。

## COM 与 SEQ controller

算法只有一个初始 COM wave：

```text
initial snapshot
    discover Constant + Existing + q Build for every root
    combinational proof of all current candidates
    dynamic greedy positive-gain bundle commit
```

此后不再运行 arbitrary-state COM proof。后续全部是 SEQ wave，但三条 candidate lane
仍然全开；因此 sequential rewrite 后新出现的 Constant/Existing 会在 SEQ 中证明和
统计，不会重新归因给 COM。

SEQ controller：

```text
build immutable snapshot and per-root iterators
repeat:
    every root contributes all direct + next q Build
    prove all O with optional all-retained H
    retain every new formal proof
    recompute dynamic gain
    if any positive relation:
        greedy bundle commit
        discard all object-indexed iterator/cache
        rebuild on the new graph
    else:
        continue the same per-root iterators
until iterator exhaustion or -w termination after commits
```

UNKNOWN 不进入专门 retry 队列。它不会触发 commit；同一 snapshot 继续其他尚未生成的
Build candidates。图被正式 commit 改变后，UNKNOWN relation 可以被自然重新发现。

## Soundness 与精确 gain

- Simulation signature 仅用于筛选，不能产生 proof status。
- COM proved relation 来自 arbitrary-state CBS；SEQ proved relation来自完整 scorr fixed point。
- History remap 失败、结构失效或拓扑不合法时删除。
- commit 前重新计算 bundle interaction 下的 dynamic gain。
- cleanup 后断言真实 `AND-before - AND-after` 与 exact gain 一致。
- DSEC regression 覆盖每个 fixture，helper 只影响 proof strength，不影响等价性边界。

## 观察 helper 和多 commit

```bash
./abc -q 'read_blif test/stran_helper_remap.blif; strash; write_aiger /tmp/before.aig; &get; &stran -P root -p -q 1 -w 2; &write /tmp/after.aig; dsec /tmp/before.aig /tmp/after.aig'
```

应重点查看：

- `initial commit: phase=comb` 只出现一次；
- 后续 `round commit` 只有 `phase=seq`；
- `helper batch: enabled=yes retained>0 active=retained inactive=0`；
- `seeded = candidates + helper-seeds`；
- `wave portfolio: continuations>0` 表示无 commit 时复用同一 iterator；
- `snapshot-discarded>0` 表示 commit 后旧 iterator 被丢弃；
- 最后 `Networks are equivalent`。
