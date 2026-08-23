# `&stran` 参数与实验语义

`&stran` 是 sequential root resubstitution 实验命令。推荐从下面的配置开始：

```abc
&stran -P root -p -q 1 -w 8
```

## Wave 与 candidate

COM 和 SEQ 使用不同的 candidate frontier：

- COM 固定为每个 root 最多 4 个 Build candidate，只运行一个 shared proof batch，
  proof 结束后立即 selection/commit；COM 不读取命令行的 `-q` 或 `-j`。
- SEQ 默认（`-j 0`）保持旧语义：`q` 是每个 root、每个 wave 的 Build 数量，
  proof 结束后立即 selection/commit。

默认 SEQ 中，对 root `r`，当前 wave 的新 obligations 是：

```text
O_r = 全部新 Constant + 全部新 Existing + iterator 接下来的 q 个 Build
```

所有 root 的 `O_r` 合并成一个 shared proof batch。这里的 obligation 是需要 proof
返回 status 的新 candidate relation；helper 是额外注入的已证明假设，不属于 obligation。
实现只限制每个 root 的 Build 数量，不限制合并后的全局 obligation 数量，也不做
top-1、global relation cap 或二次截断。`q=0` 会在一个 wave 内耗尽每个 root 的有限
Build iterator。Constant/Existing 不计入 q。

| 参数 | 默认 | 含义 |
|---|---:|---|
| `-q n` | `1` | SEQ 每 root/wave 的 Build 数；配合 `-j` 时为 commit 前每 root 的累计 Build horizon；`0` 表示耗尽 iterator。 |
| `-j n` | `0` | SEQ 每 root/proof micro-batch 的 Build 数；`0` 保持原来的 q-wave 后立即选择/commit。 |
| `-w n` | `8` | 初始 COM 后允许的 SEQ rebuild/commit 轮数；`0` 表示运行到无正增益 commit。 |
| `-K n` | `8` | Build divisor 的 TFI 深度；`0` 表示完整 TFI。 |
| `-B n` | `16` | 排序后传入 Build iterator 的物理 divisor 数；`0` 表示完整合法 TFI。 |
| `-N n` | `20` | 单个 dependency recipe 的最大 AIG gate 数。 |
| `-M` | 开 | 切换是否允许 exact-MFFC 内部节点进入 Build divisor pool。 |
| `-y` | 关 | Build-only 调试模式；关闭 Constant/Existing。 |
| `-l` | 开 | 切换 global topologically-earlier Existing 搜索。 |

`-t` 作为历史拼写继续被接受，但不改变行为：all-current-candidate 始终开启。

### Proof micro-batch（opt-in）

设置 `-j n`（`n>0`）后，`q` 的作用域改成当前 immutable snapshot 中每个 root
在第一次 selection/commit 前累计允许消费的 Build candidate 数，`j` 则控制每次
shared proof call 中每个 root 最多新增多少个 Build obligation。例如：

```abc
&stran -P root -p -q 100 -j 5
```

此时第一个 proof batch 对每个 live root 传入全部新 Constant、全部新 Existing 和最多
5 个 Build obligation；后续 batch 对该 root 只继续最多 5 个 Build obligation。所有
root 的本批 obligations 仍合并成一个 shared proof batch，因此全局 batch 大小可能远大于
5，并且没有 global proof-obligation cap。proof 完成立即把已尝试 candidate 标为 tried；CBS 的
free-state CEGIS 和 scorr 的 class-refinement CEGAR 均在该 batch 内正常运行。新 proved
relation 写入 `HistoryLive`，所以下一 micro-batch 的 SEQ proof 会将它作为 helper `H`
重新物化，但不会在此时修改永久电路。每个 root 累计达到 100 个 Build candidate，
或其有限 iterator 提前耗尽后，才第一次运行 root-loss GWMIN selection，并执行一次
bundle commit。最后一个 micro-batch 会自动缩小，例如已消费 97 个时只再取 3 个。

同一 q horizon 内永久图和 virtual covered/used 集合均不变化，因此第一次 micro-batch
完成完整 root/MFFC refresh 后，后续 batch 复用该结果，并只对本批新增 `Page` 做
frontier validation；已标成 proved/tried 的累计 `Known` 不再重复扫描。commit 后 pass
在新图上重建，旧 refresh 状态不会跨 snapshot 复用。该 fast path 只减少重复工作，
不改变 candidate 顺序、proof obligations 或 selection/commit 结果。

`-q 0 -j 5` 表示每次 proof 每 root 最多 5 个 Build obligation，但 selection/commit
要等所有相关 iterator 耗尽。Constant/Existing 仍不计入 `q` 或 `j`，且只在第一个
micro-batch 枚举；这是因为 commit 前 snapshot 不变，后续重复枚举只会被 Known 去重。
`-j 0` 完全保留旧 SEQ 控制流和旧 q 语义，便于做严格 A/B。

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

1. 在初始图运行且只运行一个 COM epoch，三条 lane 全开，固定每 root 最多 4 个 Build，
   只做一个 shared proof batch；命令行 `-q/-j` 不影响 COM。
2. COM proof 后立即选择当前动态 `gain>0` 的 proved relations，commit 一个 bundle，
   再复用剩余 proved relations 完成无冲突 commit closure。
3. 后续只运行 SEQ wave，但仍继续生成 Constant、Existing、Build。
4. SEQ proof 使用 `H∪O` seed，只返回新 obligations `O` 的 status。
5. SEQ 默认有正增益 proved relation时立即 commit、cleanup、重建；`-j n` 下 proved pool
   在同一 snapshot 累积并作为后续 helper，只在 q horizon/iterator end 后选择一次。
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
