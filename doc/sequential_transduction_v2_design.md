# Target-removal-driven sequential transduction

## 1. 目标

本设计不再随机选择一个 connectable signal，添加后再观察 redundancy removal 能删除什么。算法先
选择一个希望删除的 victim wire，反向计算新增输入必须满足的部分布尔函数，再从已有节点中匹配或
构造满足要求的 divisor。

核心问题是：

> 给定 target gate `i` 和 victim fanin `k -> i`，能否找到低成本信号 `h(D)`，使 `h` 接入 `i`
> 时保持时序行为不变，同时使 `k -> i` 在所有可达行为上变得冗余，并且最终删除成本大于新增成本？

该问题与普通 `&scorr` 不同。`&scorr` 从原网络中寻找全局 sequential correspondence；本算法主动
改变网络的局部函数，重新分配 ODC，再使用 `&scorr` 的 BMC、归纳细化、增量 TFO 和反例基础设施
证明变换。

第一版限定为：

- target 是可展开的 AND supergate；
- 添加一条正相或反相 divisor wire；
- 删除同一 supergate 的一个 victim fanin；
- divisor 为已有 literal，或已有节点上的一门小 AIG；
- 每次只提交一个已证明且净面积收益为正的 transaction；
- 不支持 box、多时钟、未建模约束和任意 state recoding。

## 2. 与旧设计的差别

旧设计直接提出：

$$
t=A\land k
\quad\longrightarrow\quad
t'=A\land h(D)
$$

然后证明原电路与最终电路等价。这是 care-constrained constructed resubstitution，能够形成安全基线，
但没有显式利用 redundancy addition 改变 ODC 的过程。

新设计使用严格的 add-then-remove 语义：

$$
t=A\land k
\xrightarrow{\text{add }h}
t^+=A\land k\land h
\xrightarrow{\text{remove }k}
t'=A\land h
$$

算法在选择 `h` 之前，同时推导：

1. `h` 在哪些行为上必须为 1，才能保证加线不改变结果；
2. `h` 在哪些行为上必须为 0，才能保证删除 `k` 后结果不变。

这使 candidate generation 从随机或语法驱动，变成 deletion-directed function matching/synthesis。

## 3. 组合条件

设 AND supergate 为：

$$
i=k\land P
$$

其中 `k` 是 victim，`P` 是其他 fanins 的 conjunction。设 `g_i=1` 表示 `i` 的输出当前不可观察，
则节点的 care condition 为：

$$
C_i=\neg g_i
$$

### 3.1 加线保持条件

添加 `h` 后：

$$
i^+=k\land P\land h
$$

只有在原输出为 1、输出可观察、而 `h=0` 时，新增 AND 输入才会改变结果。因此：

$$
M_1=C_i\land k\land P
$$

必须满足：

$$
M_1\Rightarrow h=1
$$

这等价于 ASPDAC connectable condition：

$$
f_h\lor\neg f_i\lor g_i\equiv1
$$

### 3.2 victim 删除条件

删除 `k` 后：

$$
i'=P\land h
$$

在 `P=1`、`k=0` 且输出可观察时，删除 `k` 会把原来的 0 变成 1，除非 `h=0`。因此：

$$
M_0=C_i\land\neg k\land P
$$

必须满足：

$$
M_0\Rightarrow h=0
$$

### 3.3 新增 divisor 的允许函数

`h` 的规格是一个 incompletely-specified function：

$$
h(u)=
\begin{cases}
1,&u\in M_1\\
0,&u\in M_0\\
X,&\text{otherwise}
\end{cases}
$$

用函数区间表示：

$$
M_1\le h\le\neg M_0
$$

若：

$$
M_1\land M_0\ne0
$$

则规格自身冲突，当前 victim/添加位置不可行。对于最简单的同一 AND supergate 单加单删，`M1`
与 `M0` 由 `k` 和 `!k` 区分，通常不会直接重叠；真正的冲突常出现在受限 divisor support 上，或者
multi-wire/multi-victim 联合约束中。

## 4. 时序提升

组合 pattern `u` 在时序电路中变为一个从 reset 可达的 trace/time point：

$$
u=(x_0,\ldots,x_t,s_t)
$$

时序要求只作用于可达行为：

$$
M_1^{seq}=Reach(s_t)\land C_i^{seq}(s_t,x_t)\land k\land P
$$

$$
M_0^{seq}=Reach(s_t)\land C_i^{seq}(s_t,x_t)\land\neg k\land P
$$

`C_i^{seq}` 不能只描述当前周期 PO observability。若差异到达 RI，它会改变下一状态并可能在未来到达
PO。因此时序 TFO 的传播规则是：

```text
modified gate @ frame t
    -> combinational TFO
    -> PO: observable boundary
    -> RI: cross to the corresponding RO @ frame t+1
    -> continue until proof depth/inductive boundary
```

最终语义只要求从 reset 出发的 PO traces 相同，不要求内部 RO 逐位相同。RO 是内部状态编码，强制其
相等会禁止合法的寄存器合并和删除。但局部有限窗口不能忽略 RI：它必须把 RI 当作保守 boundary，
或者像 `&scorr -i` 一样跨寄存器继续传播。

## 5. 总体算法

```text
run baseline scorr and retain simulation/CEX information

for each optimization round:
    rank target supergates and victim fanins
    for each selected victim k -> i:
        estimate removable MFFC and structural gain
        build sequential TFO/window metadata
        derive sampled M1/M0 masks
        reject if sampled constraints conflict

        match existing literals against M1/M0
        if none is profitable:
            synthesize bounded h(D) from existing divisor signatures

        for each candidate h in increasing implementation cost:
            build speculative C_add = C + h -> i
            reject by structural cycle/level/gain filters
            prove retention: C == C_add

            build C_final = C_add - k -> i
            cleanup and compute exact gain
            prove removal: C_add == C_final
            optionally audit C == C_final

            SAT: add the real counterexample trace to M1/M0 and resynthesize
            UNKNOWN: do not commit
            UNSAT for all required obligations:
                commit C_final
                invalidate only affected TFO caches
                restart from the updated network
```

## 6. Victim 选择

每个候选是 `(target supergate i, victim edge k -> i)`。优先级结合：

- 删除 `k -> i` 后真正悬空的 exclusive MFFC；
- target 的时序 TFO 大小和跨寄存器次数；
- victim 在 reachable simulation 中的 0/1 平衡；
- 附近 divisor 对 `M1/M0` 的可分性；
- level slack 和预计新增逻辑成本。

建议使用：

$$
Score=\frac{Gain_{MFFC}\cdot Separability}{1+TFOCost+ProofHistory}
$$

第一版只要求排序可解释，不需要训练概率模型。

## 7. Must1/Must0 的表示

### 7.1 小组合窗口

若 window 输入很少，可以使用精确 truth table 或 BDD。对所有 pattern 一次性得到：

```text
must1: h 必须为 1
must0: h 必须为 0
dc:    h 可以任意取值
```

### 7.2 时序仿真签名

大电路使用 reset-reachable random/guided traces 和 `&scorr` counterexamples。每个信号保存 bit-parallel
signature：

$$
\sigma(d)=[d(u_0),d(u_1),\ldots,d(u_{N-1})]
$$

候选 `h` 通过样本过滤，当且仅当：

$$
M_1\land\neg\sigma(h)=0
$$

$$
M_0\land\sigma(h)=0
$$

simulation 只用于搜索和剪枝，不能替代 formal proof。

## 8. Divisor matching 与构造

### 8.1 Divisor pool

只收集不在 target TFO 中、不会产生组合环的节点。优先来源：

- target 的局部 TFI/cut；
- 与 target 拓扑接近但不在 TFO 的节点；
- `&scorr` 曾放入相同候选类但被反例拆开的节点；
- simulation signature 能较好区分 `M1/M0` 的节点；
- 满足 level slack 的 PI、RO 和 AND literals。

### 8.2 Level 0：已有 literal

依次检查 `d` 和 `!d`。bitset 检查为常数时间机器字操作。existing literal 不增加 AIG 节点，应优先于
constructed divisor。

### 8.3 Level 1：一门函数

在 divisor literals 上构造：

$$
d_a\land d_b,
\quad d_a\lor d_b,
\quad d_a\land\neg d_b
$$

用 signature hash 去掉语义重复，只保留同一 signature 的最低 AIG 成本实现。XOR/MUX 成本更高，
第一版可以关闭。

### 8.4 一组 base divisors 是否足够

若希望构造任意小函数 `h(D)`，可用两个 pattern copy 检查：

$$
M_1(u)\land M_0(v)\land D(u)=D(v)
$$

该公式 SAT 表示相同 divisor valuation 同时被要求输出 1 和 0，因此任何仅依赖 `D` 的 `h` 都不存在；
UNSAT 表示存在某个满足规格的 dependency function。

## 9. CEGIS

初始 `M1/M0` 来自 simulation，只覆盖有限 reachable traces。每个 formal counterexample 应重新模拟
原电路、加线电路和删除电路，并分类为：

- retention 反例：形成新的 `h=1` 约束；
- removal 反例：形成新的 `h=0` 约束；
- window boundary 假反例：扩大 window，不直接加入硬约束；
- proof UNKNOWN：不产生逻辑约束，只降低候选优先级。

对每个 victim 限制 CEGIS 轮数。一个反例应同时筛掉所有违反该 trace 的 existing/constructed candidates，
而不是只拒绝当前 candidate。

## 10. 分层证明

### 10.1 Retention obligation

证明：

$$
C\equiv C_{add}
$$

这确认 added wire 是 sequentially redundant，允许随后使用新增 ODC。

### 10.2 Removal obligation

证明：

$$
C_{add}\equiv C_{final}
$$

这确认 victim 在加线后的网络中可删除。

### 10.3 Final audit

理论上前两步传递地推出 `C == C_final`。实现调试和实验输出仍建议进行独立 whole-design audit：

$$
C\equiv C_{final}
$$

最终审计只比较 PO traces；局部快速证明必须追踪 RI 跨帧影响或使用 sound boundary。

所有 proof 返回 `SAT / UNSAT / UNKNOWN`。只有 `UNSAT` 可以提交；conflict limit、time limit 和未完成
归纳都属于 `UNKNOWN`。

## 11. 复用 `&scorr -i`

现有 `-i` 已有以下可复用机制：

- 从变化 seed 计算有限帧时序 TFO；
- 沿组合 fanout 传播；
- 遇到 RI 后跳转到下一帧 RO；
- 只发射 TFO 内受影响的 correspondence pairs；
- active pair 比例过高时 fallback 到 full SRM；
- skipped-pair oracle；
- persistent CEX 的局部 resimulation、rollback 和 coverage fallback。

不能直接复用的部分是 seed 定义和结构缓存。当前 `Cec_IncrMgr` 比较 `pReprs/pNexts` snapshot；
transduction 修改 fanin graph，需要新增 structural-edit seed 或 candidate overlay，并保证 fanout map、RI/RO
映射和 alias edges 与 speculative network 一致。

建议新增 `Cec_TranIncr_t`，复用 TFO BFS/active-mask 思路，但不把结构修改伪装成 equivalence-class 变化。
第一版可先在每个 accepted transaction 后重建 fanout/TFO metadata，确认正确后再实现局部失效。

## 12. 成本与提交规则

候选按实际 speculative cleanup 后的成本判断：

$$
Gain=(AND_{old}+w_r Reg_{old})-(AND_{new}+w_r Reg_{new})
$$

第一版规则：

- `Gain > 0`；
- register 数不增加；
- 不增加最大 PO/RI level；
- divisor 不在 target TFO；
- added network 和 final network 均可被独立销毁/rollback；
- 每次只提交一个 transaction；
- commit 后所有旧候选提交前必须重新验证。

## 13. 建议参数

保留现有 `-F/-C/-S/-T/-N/-D/-G/-v`，重新解释或增加：

- `-F`：时序 TFO 和 base/induction 深度；
- `-C`：每个 local obligation 的 conflict limit；
- `-S`：归纳 refinement 上限；
- `-T`：正式 proof 次数上限；
- `-N`：accepted transactions 上限；
- `-D`：divisor pool 上限；
- `-G`：最小净 gain；
- `-K`：每个 victim 保留的构造候选数；
- `-R`：每个 victim 的 CEGIS 反例轮数；
- `-W`：初始/最大 window 大小；
- `-L`：constructed divisor 最大 AIG gate 数；
- `-a`：要求严格 retention + removal 两步证明；
- `-f`：对 accepted candidate 强制 whole-miter audit。

## 14. 实现阶段

### Phase A：结构和事务语义

1. AND supergate flattening；
2. victim edge 与 exclusive MFFC 计算；
3. 真正的 `add wire` speculative network；
4. 删除指定 victim；
5. 独立 rollback 和 exact gain。

### Phase B：组合/仿真约束

1. 生成 `M1/M0` bitsets；
2. existing literal 一次性匹配；
3. signature hash；
4. 一门 constructed divisor；
5. small combinational benchmark 上与 full truth table 对照。

### Phase C：保守时序 baseline

1. retention whole-miter proof；
2. removal whole-miter proof；
3. final whole-miter audit；
4. CEX 分类和有限 CEGIS。

### Phase D：增量时序 TFO

1. structural edit seeds；
2. 复用 `-i` 的 RI-to-RO 跨帧 BFS；
3. active obligation emission；
4. active-ratio fallback；
5. local/full oracle 对照。

### Phase E：性能和实验

1. persistent signature/CEX store；
2. candidate priority 和预算；
3. batch benchmark 脚本；
4. 与 `&scorr`、旧 `&stran`、randomized transduction baseline 对比；
5. 独立 `dsec/PDR` 审计。

## 15. 当前代码状态

当前分支已有一个 V1 reference implementation：

| 模块 | 当前状态 | V2 是否可直接复用 |
|---|---|---|
| `&stran` 命令、参数、统计 | 已完成 | 可复用，需增加 V2 参数 |
| speculative GIA duplicate | 已完成单 fanin replacement | 部分复用，需加入真正 add/remove supergate transaction |
| existing literal 枚举 | 已有按 GIA 编号邻近枚举 | 需改为 `M1/M0` 匹配和正规 divisor pool |
| constructed divisor | 已有盲枚举 `d0 & d1` | 只能复用 AIG 构造函数，搜索策略需重写 |
| structural hash/cleanup | 已完成 | 可直接复用 |
| exact `AND+Reg` gain | 已完成 | 可复用并扩展 level/MFFC cost |
| final sequential miter | 已完成 | 可作为 final audit 和 Phase C 基线 |
| proof result | 当前只有 proved/reject 两类，UNKNOWN 被安全拒绝 | 需增加 SAT/UNSAT/UNKNOWN 分类和 CEX 输出 |
| 分步 retention/removal proof | 未实现 | 新增 |
| AND supergate wire addition | 未实现 | 新增 |
| victim-first MFFC ranking | 未实现 | 新增 |
| `M1/M0` 计算 | 未实现 | 核心新增 |
| reachable simulation signatures | 未实现于 `&stran` | 可借用 `&scorr` simulation/CEX 基础设施 |
| CEGIS | 未实现 | 核心新增 |
| local/window proof | 未实现，当前为 whole miter | 核心新增 |
| `-i` structural-edit integration | 未实现 | 核心新增，但 TFO/active-list 机制已有参考 |
| 回归和服务器脚本 | 已有 V1 | 需增加 V2 定向测试和统计 |

现有实现完成了命令外壳、speculative rewrite、gain、whole-miter proof、commit/rollback 和回归，约等于
V2 的安全执行框架。V2 真正具有研究新意的部分——约束反推、divisor matching/synthesis、分步证明、
结构修改的增量时序 TFO——尚未实现。

若以完整 V2 研究原型为 100%，当前可复用工程约占 25%--30%；剩余 70%--75% 包含几乎全部核心
算法和性能优化。最先应完成 Phase A+B，因为它们能在组合 truth-table 小电路上验证“反推 divisor”
是否确实比 randomized addition 提高机会密度。只有机会普查为正，才值得投入 Phase D 的复杂增量
证明实现。

## 16. 成功判据

第一阶段不预设平均 QoR 提升，而回答四个问题：

1. 对一个高收益 victim，`M1/M0` 是否能显著减少 connectable divisor 尝试数；
2. existing divisor 不满足时，一门 constructed divisor 增加多少合法机会；
3. deletion-directed search 在相同 proof budget 下是否比 randomized addition 接受更多正收益事务；
4. 基于修改点时序 TFO 的 proof 是否与 whole-miter oracle 一致，同时明显减少 SAT obligations。

只有同时证明候选机会密度和增量证明收益，才扩展 multi-wire、multi-victim 和两门以上构造。
