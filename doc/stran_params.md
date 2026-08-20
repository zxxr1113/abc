# `&stran` 参数与实验语义

`&stran` 是 sequential root resubstitution 实验命令。推荐从下面的配置开始：

```abc
&stran -P root -p -q 1 -w 8
```

## Wave 与 candidate

`q` 的作用域是 **每个 root、每个 wave 的 Build lane**，不是全局 batch 大小。
对 root `r`，当前 wave 的新 obligations 是：

```text
O_r = 全部新 Constant + 全部新 Existing + iterator 接下来的 q 个 Build
```

所有 root 的 `O_r` 合并成一个 shared proof batch。命令始终提交当前 wave 的全部
候选，不做 top-1、全局 relation cap 或二次截断。`q=0` 会在一个 wave 内耗尽每个
root 的有限 Build iterator。Constant/Existing 不计入 q。

| 参数 | 默认 | 含义 |
|---|---:|---|
| `-q n` | `1` | 每 root/wave 拉取的 Build candidate 数；`0` 表示耗尽 iterator。 |
| `-w n` | `8` | 初始 COM 后允许的 SEQ rebuild/commit 轮数；`0` 表示运行到无正增益 commit。 |
| `-K n` | `8` | Build divisor 的 TFI 深度；`0` 表示完整 TFI。 |
| `-B n` | `16` | 排序后传入 Build iterator 的物理 divisor 数；`0` 表示完整合法 TFI。 |
| `-N n` | `20` | 单个 dependency recipe 的最大 AIG gate 数。 |
| `-M` | 开 | 切换是否允许 exact-MFFC 内部节点进入 Build divisor pool。 |
| `-y` | 关 | Build-only 调试模式；关闭 Constant/Existing。 |
| `-l` | 开 | 切换 global topologically-earlier Existing 搜索。 |

`-t` 作为历史拼写继续被接受，但不改变行为：all-current-candidate 始终开启。

## Helper 开关

| 参数 | 默认 | 含义 |
|---|---:|---|
| `-u` | helper 开 | 切换 retained-proof induction helper；带 `-u` 时关闭。 |

Helper-on 时，所有仍合法、未 selected、canonical 去重后的正式 proved relations 都
作为 `H` 注入下一次 sequential SRM。Helper-off 时 `H=∅`。两种模式都保留相同的
proof metadata 和未来 commit 资格，因此 A/B 对照只改变 induction hypotheses。

没有 helper 数量、endpoint、recipe gate、class width、临时 SRM node 或 batch relation
截断。profile 会报告实际注入规模，但不会据此选择或丢弃 helper。

## Proof 预算

| 参数 | 默认 | 含义 |
|---|---:|---|
| `-F n` | `1` | BMC/induction depth。 |
| `-C n` | `100` | scorr 每个 obligation 的 SAT conflict limit。 |
| `-S n` | `-1` | induction refinement round limit；`-1` 不限制。 |
| `-b n` | `100` | root CBS 每个 cube 的 conflict limit。 |
| `-Q n` | `4` | 每个 reachable simulation frame 的 64-bit word 数。 |
| `-W n` | `8` | reset-reachable random simulation frame 数。 |
| `-a n` | `2` | independent PI/RO simulation word 数。 |
| `-e n` | `64` | 每批保留的 free-state CBS counterexample 数。 |

UNKNOWN 没有专门 retry 队列。无 commit 时 Build iterator 在同一 immutable snapshot
继续下一组 q；发生 commit 后旧 iterator/cache 全部丢弃，在新图自然重新发现。

## Controller

1. 在初始图运行且只运行一个 COM wave，三条 lane 全开。
2. COM proof 后立即 greedy 选择所有当前动态 `gain>0` 的 proved relations，并 commit
   一个 bundle。
3. 后续只运行 SEQ wave，但仍继续生成 Constant、Existing、Build。
4. SEQ proof 使用 `H∪O` seed，只返回新 obligations `O` 的 status。
5. 有正增益 proved relation时立即 commit、cleanup、重建；无 commit 时保持 snapshot，
   每个 root 从原 iterator 继续下一组 q。
6. 只有 selected recipe 能修改永久 GIA。Helper 只存在于 metadata 或临时 proof graph。

## Profile

`-p` 输出 schema 4。关键行包括：

- `wave portfolio`：waves、same-snapshot continuations、new-proved、history-selected；
- `helper batch`：enabled、retained、active/inactive、实际 materialized gates 和 relation total；
- `sequential relations`：candidates、seeded、helper-seeds、proved/split/unknown；
- `resub iterator`：initialized、next、exhausted、q-wave-stops、snapshot-discarded；
- `initial commit`、`round commit`、`rounds summary`：真实多 commit 与 AND 变化；
- `effect matrix`：Constant/Existing/Build 的 submitted/proved/selected/exact gain。

Helper A/B 示例：

```bash
# helper on
./abc -q 'read_blif test/stran_helper_remap.blif; strash; &get; &stran -P root -p -q 1 -w 2'

# helper off；其他算法参数完全相同
./abc -q 'read_blif test/stran_helper_remap.blif; strash; &get; &stran -P root -p -q 1 -w 2 -u'
```
