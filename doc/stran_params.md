# `&stran` 参数语义

本文只描述当前 root-only 实现。参数结构在 `src/proof/cec/cec.h`，默认值在
`Cec_ManTranSetDefaultParams()`，CLI 解析与帮助在
`Abc_CommandAbc9Stran()`。

典型的小 batch 配置：

```sh
&stran -P root -p -q 1 -A 4 -L 16 -w 8
```

## 调度、分页与 helper

| 选项 | 默认 | 当前语义 |
|---|---:|---|
| `-q n` | `1` | 每个 root、每页最多拉取的 **Build** candidate 数；`0` 表示把该 root 的有限 iterator 拉到 exhaustion。Constant/Existing 不受 `q` 限制。 |
| `-A n` | `8` | 每个 proof page 的新 obligations（O）上限。必须 `A <= L`。 |
| `-L n` | `32` | 单个临时 proof batch 中 active helpers（H）与 O 的关系总数上限。 |
| `-U n` | `0` | 每个 immutable snapshot 的 proof page 上限；`0` 表示运行到 iterator exhaustion 或发生 commit。 |
| `-w n` | `8` | 最大 rebuild/commit round；`0` 表示运行到 fixed point。一个 round 内 COMB 可以多次 commit/rebuild，然后运行 SEQ。 |
| `-E n` | `64` | active helper basis 的 unique endpoint 上限；`0` 不限制。 |
| `-R n` | `64` | active helper recipe 的临时物化 gate 总数上限；`0` 不限制。 |
| `-H n` | `8` | 同一 helper class/root 的 active edge 上限；`0` 不限制。 |
| `-I n` | `2000000` | 临时 proof/SRM node 估计上限；`0` 不限制。 |
| `-t` | 关闭 | 已废弃的 all-candidate 兼容拼写。仍被接受，但不改变 stateful page scheduler。 |

`q` 只控制 Build lane，不是总候选数，也不是全局 proof budget。若本页没有
commit，controller 在同一 snapshot 上继续原 iterator，不重新初始化。只要本页产生
positive-gain proved candidate，就立即 greedy bundle commit，并丢弃全部 object-indexed
iterator/cache，在新图上重建。

Helper cap 只影响 induction strength，不影响 soundness。未激活关系仍以 retained
certificate metadata 保存，后续 page/commit 后可以重新成为 active helper。

## Candidate discovery

| 选项 | 默认 | 当前语义 |
|---|---:|---|
| `-K n` | `8` | Build lane 的 TFI 收集深度；`0` 为完整允许的 TFI。 |
| `-B n` | `16` | 排序后真正传入 Build iterator 的物理 divisor 数；`0` 为完整允许的 TFI。实现先收集更大的 reservoir，再按 simulation separation/CI overlap 排序并取 top-B。 |
| `-N n` | `20` | 单个 dependency recipe 的最大 AIG gate 数，范围 `1..100`。 |
| `-G n` | `1` | 已废弃的 local-gain 兼容值；当前 scheduler 不用它阻止 relation 进入 proof/helper history。 |
| `-l` | 开 | 切换全局 Existing lane。开启时通过全局 signature index 查找所有拓扑更早、结构合法的 CI/RO/AND literal，含双极性。 |
| `-x` | 开 | 切换 Build dependency-resub lane。 |
| `-M` | 开 | 切换是否允许 exact-MFFC 内部节点进入 Build 的 TFI pool。 |
| `-y` | 关 | 切换 Build-only；开启后禁止 Constant/Existing。 |
| `-r` | 关 | 已废弃的 exhaustive-discovery 兼容拼写；仍被接受并清零 `G`，但 scheduler 始终分页。 |

三个 lane 相互独立：

1. Constant 只产生 `const0` 与 `const1` 两个关系；
2. Existing 使用全局 signature index，不受本地 TFI pool、`B` 或 `q` 限制；
3. Build 只能使用当前 root 的 ranked TFI divisor pool，不能借用全局 Existing 节点。

Simulation/signature 只做筛选。所有可 commit relation 最终仍由 CBS 或 shared
scorr 正式证明。

## Proof、simulation 与审计

| 选项 | 默认 | 当前语义 |
|---|---:|---|
| `-F n` | `1` | shared scorr 的 BMC/induction depth。 |
| `-C n` | `100` | scorr 每个 proof obligation 的 conflict limit。 |
| `-S n` | `-1` | induction refinement round limit；`-1` 不限制。 |
| `-b n` | `100` | 组合 CBS 每个 cube 的 conflict limit；`0` 只 propagation。 |
| `-Q n` | `4` | 每个随机模拟 frame 的 64-bit word 数。 |
| `-W n` | `8` | reset-reachable 随机模拟 frame 数。 |
| `-a n` | `2` | free PI/RO screening 的 64-bit word 数；`0` 只用 learned CEX。 |
| `-e n` | `64` | 每 batch 保留的 free-state CBS CEX 数；`0` 只用随机样本。 |
| `-g` | 开 | 切换 independent PI/RO signature screening 与 CBS CEGIS。 |
| `-c` | 开 | 切换 CBS direct multi-literal cubes；关闭时构造 XOR query。 |
| `-f` | 关 | 切换 whole-miter shadow audit。 |
| `-Z n` | `1000000` | shadow audit 总 conflict cap；`0` 不限制。 |

`UNKNOWN` 沿用现有 proof 语义，本实现没有 hard-candidate retry queue 或高预算重试
策略。commit 后在新图上的重新发现属于自然 rediscovery。

## 通用选项

| 选项 | 默认 | 当前语义 |
|---|---:|---|
| `-P root` | `root` | `root` 与兼容拼写 `gate` 均选择当前唯一维护的 root-only scope。 |
| `-p` | 关 | 输出 phase、candidate、proof、iterator、helper 与 exact-gain profile。 |
| `-h` | — | 打印命令帮助。 |

输入无 register 时命令成功返回并打印 combinational no-op；包含 box 的输入被拒绝。

## 参数组合注意事项

- 小 batch 建议从 `-q 1 -A 4 -L 16` 开始。`A` 是 O 上限，剩余 `L-A`
  才可能用于 active H。
- `-E/-R/-H/-I` 是相互独立的 helper 膨胀约束；manager 还会做 canonical
  dedup、signed equivalence forest 压缩和 obligation-cone relevance 排序。
- `-B 0` 与 `-q 0` 含义不同：前者保留完整允许 TFI divisor，后者拉完有限 Build
  iterator。二者同时为 0 可能显著增大搜索。
- `-U` 是显式 snapshot resource bound。达到它但没有 commit 时 controller 停止该
  snapshot；不会为 UNKNOWN 添加专门 retry。
- commit admission 与 helper admission 分离：正式 proved 的 zero/negative current-gain
  relation可以保留为 helper；只有重新计算后 `dynamic gain > 0` 的关系能进入永久 commit。
