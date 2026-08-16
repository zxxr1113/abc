# `&stran` 参数文档

本文整理当前 `&stran`（root-only Direct resubstitution）实现的全部参数：结构体字段、CLI 标志、默认值，以及每个默认值的含义。代码位置：

- 结构体定义：`Cec_ParTran_t` — `src/proof/cec/cec.h:334`
- 默认值初始化：`Cec_ManTranSetDefaultParams` — `src/proof/cec/cecTrans.c:69`
- CLI 解析与 usage：`Abc_CommandAbc9Stran` — `src/base/abci/abc.c:42237`

命令用法：

```
&stran [-FCSTNDGQWKBMPAERIJUHLVOXYZmwbae num] [-cdxlrzsgiftpuvh]
```

标志串里 `h` 没有对应 case，落到 default 分支打印 usage（等价于 `-h`）。`-q/-w` 是有效的 root 调度参数；`-o` 直接报错拒绝（本分支只实现 Direct）。

---

## 1. 证明 / 预算（scorr oracle）

| 标志 | 字段 | 默认 | 含义 |
|---|---:|---:|---|
| `-F` | `nFrames` | `1` | scorr oracle 的 BMC/induction 深度。`1` 表示只做单步（base + 1 步 induction），是最保守、最便宜的时序证明深度。 |
| `-C` | `nBTLimit` | `100` | 每个 proof obligation 的冲突上限（scorr / high-context 共用）。`100` 是低预算，能快速筛掉假 candidate，代价是复杂义务会 UNKNOWN。 |
| `-S` | `nStepsMax` | `-1` | scorr induction 的 refinement 轮数上限。`-1` 表示不限制，让 oracle 自己跑到底。 |
| `-T` | `nCandMax` | `0` | contextual proof 的 obligation 上限。`0` = 不限制；root scope 不使用此字段。 |
| `-b` | `nCombBTLimit` | `100` | 组合 CBS 每个 cube 的冲突上限。`0` = 只做 propagation 不调 SAT。默认与 `-C` 相同，让组合证明与 scorr oracle 用同一档预算。 |

## 2. 候选发现 / 构建

| 标志 | 字段 | 默认 | 含义 |
|---|---:|---:|---|
| `-N` | `nDepNodesMax` | `20` | 单个 dependency recipe 的最大 AIG 节点数（1..100）。`20` 限制构造出的 candidate 规模，避免 recipe 过大。 |
| `-D` | `nDivsMax` | `16` | 每个 victim 保留的 local existing divisor 数。root scope 保留全部 earlier exact 匹配，此字段对 root 无效。 |
| `-K` | `nConstrMax` | `8` | 收集 local divisor 的 TFI 深度。`0` = 完整 TFI。`8` 是折中：够深到覆盖局部逻辑，又不至于把整个锥都拉进来。 |
| `-B` | `nConstrBaseMax` | `16` | local divisor pool 的物理节点数。`0` = 全部。`16` 限制 pool 规模以控制候选数量。 |
| `-q` | `nRootConstrTop` | `8` | 每个 root 同时保留的 Build frontier。`0` = iterator 穷尽，不限制候选数；`1..64` = 有限 frontier。 |
| `-w` | `nRootWaves` | `1` | 候选前缀 wave 数（1..64）。top-1 每 wave 为每个 root 增加一个有序候选并重证累计前缀；all-candidate 用有限 `q` 时每 wave 继续补充 frontier。 |
| `-m` | `nHardMffc` | `1024` | 用 MFFC 大小选择 root 准入 / context high 预算的门槛。`1024` 只给大 MFFC 的 root 开高预算（见 `-V`/`-Z`）。 |

## 3. 增益 / 准入门

| 标志 | 字段 | 默认 | 含义 |
|---|---:|---:|---|
| `-G` | `nGainMin` | `1` | 非穷举模式下，local 结构增益的准入门（AND+register 增益 >= 此值才证明）。`1` = 只要有任何正增益就证。 |
| `-V` | `nHardGain` | `256` | exact gain 达到此值的 candidate 才升级到 high-context 高预算。`256` 刻意保守：更低的门槛会把几乎所有大根 candidate 都升级（包括 level_48 里大量不会赢的 obligation），只增加 care/candidate 开销而不减少证明调用。 |
| `-O` | `nRootGainMin` | `0` | root scope 的 local MFFC 增益门槛（与 `-m` 是 OR 关系）。`0` = 关闭此门。 |
| `-r` | `fRootExhaustive` | `0` | 穷举 root 发现开关。置 `1` 时强制关闭 `-L`/`-G`/`-O`/`-m` 四道准入门（见 abc.c:42492 的联动逻辑），证所有候选。 |

## 4. 模拟 / 签名

| 标志 | 字段 | 默认 | 含义 |
|---|---:|---:|---|
| `-Q` | `nSimWords` | `4` | 每个可达模拟帧用多少个 64-bit word（签名宽度 = 4×64 = 256 bit）。`4` 在碰撞率和速度之间取平衡。 |
| `-W` | `nSimFrames` | `8` | 每个签名批次做多少帧 reset-可达随机模拟。`8` 帧足以覆盖多数浅层时序行为。 |
| `-g` | `fUseFreeSim` | `1` | 独立 PI/RO 签名筛选与 CBS CEGIS 开关。`1` = 用独立随机输入/输出签名先筛一轮，再用 CEX 引导。 |

## 5. 反例 / CEX 采集

| 标志 | 字段 | 默认 | 含义 |
|---|---:|---:|---|
| `-E` | `nCexFrames` | `4` | 采集被拒 candidate 见证的 BMC 深度。`4` 帧足以定位大多数被拒原因。`0` = 关闭。 |
| `-R` | `nCexMax` | `64` | 每个模拟批次注入的持久 CEX 迹数量。`64` 条反例让签名区分度显著提升。`0` = 关闭。 |
| `-H` | `nCexBatch` | `1` | 累积多少条 CEX 才追加一个签名块（1..64）。`1` = 每条 CEX 立刻生效。 |

## 6. 自由状态（free-state）组合筛选

| 标志 | 字段 | 默认 | 含义 |
|---|---:|---:|---|
| `-a` | `nFreeWords` | `2` | 自由状态组合筛选用多少个 64-bit 独立 PI/RO word。`0` = 只用学到的 CEX。`2` = 少量随机 + 学到的 CEX 混合。 |
| `-e` | `nFreeCexMax` | `64` | 每个证明批次保留的自由状态 CBS 反例数。`0` = 只用随机。`64` 与 `-R` 对齐，反例是主要筛选信号。 |

## 7. 调度 / cooldown / 上下文预算

| 标志 | 字段 | 默认 | 含义 |
|---|---:|---:|---|
| `-J` | `nLowUnknownMax` | `8` | 低价值 contextual root/lane 连续 UNKNOWN 达到此值即冷却。`8` 是保守默认：太小的值（如 2）只会把 scheduler 推到更多低价值 root 直到 `-T` 打满，增加 care/candidate 开销却不减少证明调用。 |
| `-U` | `nUnknownMax` | `8` | root / high-context 连续 UNKNOWN 达到此值即冷却。`0` = 关闭 cooldown。 |
| `-X` | `nScoutBTLimit` | `100` | low contextual 每个 obligation 的冲突上限。与 `-C` 同档。 |
| `-Y` | `nScoutConfTotal` | `20000` | low contextual 每次调用的总冲突上限。`0` = 不限制。 |
| `-Z` | `nHardConfTotal` | `1000000` | high contextual 每次调用的总冲突上限。`0` = 不限制。`1000000` 给 high 预算足够的纵深。 |

## 8. 模式开关（布尔）

| 标志 | 字段 | 默认 | 含义 |
|---|---|---:|---|
| `-d` | `fUseDirect` | `1` | Direct root 替换开关。默认开，本分支只有 Direct。 |
| `-x` | `fUseConstr` | `1` | 依赖函数 resub recipe 开关。默认开，允许构造式 candidate。 |
| `-c` | `fUseCbsMultiLit` | `1` | root CBS 用 direct 多字面量 cube；关掉则构造 XOR 查询。 |
| `-l` | `fUseExisting` | `1` | root TFI divisor pool 中 existing-literal 查找开关。默认开（即 constant/existing direct lane）。 |
| `-t` | `fSeqAllCands` | `0` | 候选组合模式。默认 top-1：每 wave、每 root 扩展一个排序候选并证明累计前缀；开启后为 all-candidate：累计全部已发现候选，最后统一证明。`q=0` 时还证明 primary q=1 fallback，并与完整集合的 proved relations 取并集。 |
| `-f` | `fShadow` | `0` | whole-miter shadow 审计开关。默认关（审计有额外开销）。 |
| `-p` | `fProfile` | `0` | 打印 phase 与 target-gate profile。默认关。 |
| `-v` | `fVerbose` | `0` | 打印候选统计。默认关。 |

## 9. Proof scope 与兼容路径

| 标志 | 字段 | 默认 | 含义 |
|---|---:|---:|---|
| `-P` | `nProofScope` | `root` | proof scope。`root`/`gate` 指向 `CEC_TRAN_PROOF_ROOT`；`window` 与 `output`/`po-ri` 是冻结兼容路径，不做算法开发。 |
| `-A` | `nProofWindow` | `0` | `-P window` 所需的 TFO 深度（必须为正）。root scope 不用。 |
| `-I` | `nStrictPct` | `25` | 兼容选项，当前被忽略。 |
| `-M` | `nVictimsMax` | `1` | legacy SODC leaf-set 参数，Direct 忽略。 |

## 10. 已废弃 / 忽略的字段（root-only 流水线）

这些字段保留结构体位置以兼容旧接口，但 root-only 流水线不使用，改动它们无效果；使用对应标志会打印 deprecated 警告（abc.c:42478）。

| 标志 | 字段 | 默认 | 说明 |
|---|---:|---:|---|
| `-L` | `nRootBatch` | `0` | deprecated；root 流水线已删除 batch 调度。 |
| `-z` | `fUseResubZero` | `0` | deprecated；zero-gate recipe 由 direct constant/existing generator 负责。 |
| `-i` | `fRootStopLegacy` | `0` | deprecated；root 流水线已删除分层调度。 |
| `-u` | `fRootStopProved` | `1` | deprecated；当前 root pipeline 不做 per-root first-proof early stop，proof portfolio 由 `-t/-q/-w` 定义。 |
| `-s` | `fRootSplitStages` | `0` | deprecated；当前每次 portfolio proof 固定在同一 batch 内先跑 CBS，再把未解决关系连同 CBS helpers 交给 shared scorr。 |
| `-o` | `fUseSodc` | `0` | legacy 选择器，本分支必须保持 0，传 `-o` 直接报错。 |
| — | `nProfileTop` | `20` | legacy SODC target-profile 上限，无 CLI 标志。 |
| — | `nChangesMax` | `0` | 接受的 transaction 数（0=不限制），Direct 无 CLI cap。 |
| — | `fRootProgressive` | `0` | deprecated，无 CLI 标志。 |
| — | `nRootStage` | `0` | 冻结兼容路径，无 CLI 标志。 |

## 11. 默认值的联动与注意点

1. **`-r` 会联动清空准入门**：`-P root` 且 `-r` 时，代码强制 `nRootBatch=0`、`nGainMin=0`、`nRootGainMin=0`、`nHardMffc=0`（abc.c:42492），等价于"证所有候选、不设门槛"。

2. **组合与 scorr 预算默认同档**：`-b` 与 `-C` 默认都是 `100`，但可独立调（`-b` 管组合 CBS，`-C` 管 scorr oracle）。

3. **`fShadow` 不在 `Cec_ManTranSetDefaultParams` 里显式赋值**：它只靠 `memset(...,0)` 得到默认 `0`，唯一赋值点是 `-f` 置 `1`。

4. **`-t`、`-q`、`-w` 联合定义候选 portfolio**：默认 top-1 按 constant、existing、Build 顺序每 wave 扩展一个候选，且每个累计前缀单独证明，最终取所有前缀证明结果的并集；`-t` 累计全部已发现候选后统一证明。有限 `q` 是分页 frontier，`q=0` 则在第一 wave 穷尽 iterator，并额外保留 primary q=1 proof 保护有限预算下的 QoR，因此完整 all-candidate reference 配置是 `-t -q 0 -w 1`。

5. **`q=0` 不是无限 Boolean 搜索**：它只是不截断当前 `B/K/N` 和有限 dependency iterator 所定义的候选空间。大设计上可能显著增加候选和 proof class，应按需要使用。

6. **`-P window` 与 `-P output` 冻结**：非 `root` scope 会打印警告；`-P window` 要求 `-A` 为正否则报错。
