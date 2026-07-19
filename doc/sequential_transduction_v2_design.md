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
- 删除同一 supergate 的一个 victim fanin；实验性 `-M 2` 也可由一个 divisor 同时替代两个 fanin；
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

### 3.4 两个 victim 的同门推广

对同一 positive AND supergate 选择集合 `V={k_0,k_1}`，令 `K=k_0\land k_1`，`P` 为其余 leaf 的合取。
交易仍是先加 `h`，再把两个 leaf 一起删除，因而只需将单 victim 公式中的 `k` 替换为 `K`：

$$
M_1=C_i\land K\land P,\qquad M_0=C_i\land\neg K\land P.
$$

实现中的 `-M 2` 只枚举这一种大小为二的集合（默认 `-M 1` 只枚举单 leaf），随后分别证明
`C\rightarrow C_{add}` 与更强的 `C\rightarrow C_{final}`；二者由传递性推出 `C_{add}\rightarrow C_{final}`。
它不是任意 multi-wire transaction：尚不共享多个
新增 divisor，也不跨 target 合并；候选数会从每个 supergate 的 $O(d)$ victim 集合增至 $O(d^2)$。

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

### 4.1 `&scorr` 的时序证明语义

`&scorr` 不是只检查一个状态或前 `F` 个 frame 的组合等价。`F` 是 base/induction proof 使用的展开
深度：base case 从 reset 检查可达前缀，inductive case 检查 correspondence relation 能否跨时间保持。
当 base 和 inductive obligations 都完成且目标 difference 被证明为 0 时，结论是：

$$
\forall t\ge0,\ \forall(x_0,\ldots,x_t),\quad
PO_C(t)=PO_{C'}(t)
$$

也就是所有未来时间、所有输入序列上的时序行为不变，而不是只保证前 `F` 帧。

必须区分以下情况：

- 完成 base + induction 并得到 UNSAT/proved：可作为无限时序证明；
- SAT：存在真实反例 trace；
- conflict/time/refinement limit 耗尽：UNKNOWN，不能提交；
- `nStepsMax=0` 只停在 BMC：只能排除已展开深度内的反例，不能当作无限证明。

因此新命令复用的是 `&scorr` 的完整时序证明基础设施。有限 `F` 决定 induction strength 和 TFO
展开范围，但不把最终正确性限制为有限 horizon。

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

            build uncleaned C_final = C_add - k -> i
            build a cleaned preview and compute exact gain
            prove final removal network against source: C == C_final

            SAT: add the real counterexample trace to M1/M0 and resynthesize
            UNKNOWN: do not commit
            UNSAT for all required obligations:
                commit the cleaned C_final preview
                first complete version rebuilds affected metadata conservatively
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

当前局部 miter 实现不直接复制 `C_add` 的编辑 TFO；它改为证明更强的：

$$
C\equiv C_{final}.
$$

与 10.1 的 $C\equiv C_{add}$ 合用即可由等价传递性得到目标式。开启 `-f` 时还会额外运行直接的
whole miter `C_add\equiv C_final` 作为影子审计。因此当前实现没有依赖“只检查 final 却未证明 add”的
不安全假设；只是尚未实现更小的 direct-add local miter。

### 10.3 完整时序 TFO 已经足够

前两步传递地推出：

$$
C\equiv C_{final}
$$

如果 local proof 使用修改点在原网络和候选网络中的完整时序 TFO，并覆盖所有 PO、RI-to-RO 跨帧
传播和归纳边界，那么它就是 whole miter 的精确 cone-of-influence reduction。TFO 外的逻辑不可能依赖
修改，删除它们不会改变 SAT/UNSAT。因此正式算法不需要为每个 candidate 再运行 whole-miter。

完整受影响区域必须使用：

$$
TFO_{affected}=TFO_C(i)\cup TFO_{C_{add}}(i)\cup TFO_{C_{final}}(i)
$$

不能只遍历原网络。新边、删除边、结构哈希产生的映射和跨帧 RI/RO 路径都必须被覆盖。若 TFO 或
boundary 无法被确定为完整，候选应 fallback 到完整 SRM，而不是在截断窗口上接受。

### 10.4 Whole-miter 的定位

whole-miter 只用于：

- 开发阶段作为 shadow oracle，对照 local TFO proof；
- 随机抽查 accepted transactions；
- pass 结束后对最终网络做一次独立 `dsec/PDR` 审计；
- 定位 structural-edit seed、boundary 或 cache invalidation 的实现错误。

稳定版本的 candidate critical path 不包含 whole-miter。出现 `local UNSAT / whole SAT` 必须视为 local
proof 实现 bug。

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
功能完整的第一版在每个 accepted transaction 后重建 fanout/TFO/proof metadata，不依赖复杂 cache
invalidation。与 whole-miter shadow oracle 对照稳定后，再实现只失效受影响 TFO 的增量版本。

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
- `-K`：每个 victim 集合保留的构造候选数；
- `-M`：一个 divisor 替代的 leaf 数（当前为 1 或 2）；
- `-Q`：每个 reachable simulation frame 的 64-bit signature word 数；
- `-W`：当前实现中每批随机 reset-reachable trace 的 frame 数；将来 local proof window 参数应另设，不能
  与随机仿真长度混用；
- `-L`：constructed divisor 最大 AIG gate 数；
- `-a`：要求严格 retention + removal 两步证明；
- `-f`：开发/审计模式，对 accepted candidate 启用 whole-miter shadow oracle；正式运行默认关闭。

## 14. 实现阶段

实现策略是 correctness-complete first：先完成所有功能并在每次提交后保守重建数据，不把增量缓存、
多线程和极限性能放在第一版关键路径。完整版本稳定后，再逐项替换为 `-i` 风格的增量实现。

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

### Phase C：完整正确性版本

1. 构造原/加线/删线网络的 TFO union；
2. retention 的完整时序 TFO proof；
3. removal 的完整时序 TFO proof；
4. 正确的 base + induction obligations；
5. SAT/UNSAT/UNKNOWN 和 CEX 分类；
6. 有限 CEGIS；
7. 每次 accepted transaction 后保守重建 metadata；
8. 开发模式使用 whole-miter shadow oracle 对照。

### Phase D：增量性能版本

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
| speculative GIA duplicate | 已完成正相 AND supergate 的 explicit add/remove transaction | 可复用，multi-wire 仍待扩展 |
| existing literal 枚举 | 已完成：对完整拓扑安全 pool 做 `M1/M0` 位并行匹配，只保留近邻匹配项送 formal proof | 已可用；精确 sequential care 仍待接入 |
| constructed divisor | 已完成一门 `AND` 及输出反相（覆盖 AND/OR/AND-NOT）；`-B` 控制 base pool，`-K` 控制保留数，sampled-signature 完全去重 | 需扩展到两门以上函数和 exact cost ordering |
| structural hash/cleanup | 已完成 | 可直接复用 |
| exact `AND+Reg` gain | 已完成 | 可复用并扩展 level/MFFC cost |
| local sequential proof | 已完成：共享原 transition relation、复制受影响组合 TFO、比较 PO/RI 边界 | 每次 transaction 后保守重建；尚未复用 `-i` cache |
| final sequential miter | 已完成 | `-f` 开发 shadow oracle 和最终审计 |
| proof result | 当前只有 proved/reject 两类，UNKNOWN 被安全拒绝 | 需增加 SAT/UNSAT/UNKNOWN 分类和 CEX 输出 |
| 分步 retention/removal proof | 已完成：local proof 检查 `C==Cadd` 和更强的 `C==Cfinal`；`-f` 额外 direct whole-miter 审计 `Cadd==Cfinal` | direct-add local miter 仍可缩小第二个 proof |
| AND supergate wire addition | 已完成正相 AIG AND supergate 的 add/remove；`-M 2` 可用一个 divisor 同时替代同一 supergate 的两个 leaf | 需扩展到多个新增 divisor 的 general multi-wire transaction |
| victim-first MFFC ranking | 未实现；当前输出 candidate funnel 统计以区分结构收益和证明瓶颈 | 新增 |
| `M1/M0` 计算 | 已实现 sampled sequential care：翻转 target 后沿 trace suffix 重仿真，PO 或 RI 差异形成 `C_i^{seq}`；据此计算 `M1=C_i&k&P`、`M0=C_i&!k&P` | 需接入 formal/CEX care |
| reachable simulation signatures | 已实现：随机 PI、zero-reset RO、RI-to-RO 状态推进、bit-parallel word signatures；每个 victim 一次生成 Must masks，整池 divisor 共享匹配 | 需合并真实 reset/init 语义和 `&scorr` CEX |
| CEGIS | 未实现 | 核心新增 |
| local/window proof | 已实现完整组合 TFO 边界 proof；affected RI 作为跨帧归纳边界 | 需扩展到 supergate/multi-wire union TFO |
| `-i` structural-edit integration | 未实现 | 核心新增，但 TFO/active-list 机制已有参考 |
| 回归和服务器脚本 | 已完成：`scripts/bench_scorr_then_stran.py` 并行执行 `&scorr -> &stran -> dsec`，输出 CSV 中的 baseline、额外缩减、分阶段时间和证明漏斗 | 需做大规模统计 |

现有实现完成了命令外壳、显式 add/remove speculative rewrite、gain、local sequential proof 与可选
whole-miter shadow audit、commit/rollback、
分步证明，以及基于 reset-reachable signature 的约束反推、existing divisor matching 和一门构造 divisor。
目前真正未完成的核心是精确 sequential ODC、CEX-driven CEGIS、supergate/multi-wire 的 TFO union 和
结构修改的增量 metadata。

若以完整 V2 研究原型为 100%，当前的小 transaction 原型约完成 60%--65%：已有时序 sampled care、
existing/constructed divisor、显式 add/remove、单 leaf 与双 leaf 替代、local proof、whole-miter shadow、
候选漏斗统计和可复现实验入口。剩余主要是 CEX-driven CEGIS、多个新增 divisor 的 general transaction、
formal care 和增量 metadata；这些不应以牺牲证明语义的方式简化。实现顺序是先完成候选排序，再完成可导出
CEX 的证明接口，最后扩展 transaction 与增量优化。

## 16. 成功判据

第一阶段不预设平均 QoR 提升，而回答四个问题：

1. 对一个高收益 victim，`M1/M0` 是否能显著减少 connectable divisor 尝试数；
2. existing divisor 不满足时，一门 constructed divisor 增加多少合法机会；
3. deletion-directed search 在相同 proof budget 下是否比 randomized addition 接受更多正收益事务；
4. 基于修改点时序 TFO 的 proof 是否与 whole-miter oracle 一致，同时明显减少 SAT obligations。

只有同时证明候选机会密度和增量证明收益，才扩展 multi-wire、multi-victim 和两门以上构造。

### 16.1 当前实验入口

`scripts/bench_scorr_then_stran.py` 对每个输入严格执行：

```text
normalized input -> &scorr -> scorr.aig -> &stran -> final.aig -> dsec
```

因此 CSV 的 `stran_extra_and_reduction = scorr_and - stran_and` 与
`stran_extra_latch_reduction = scorr_latches - stran_latches` 直接回答：在已经完成 `&scorr` 后，
transduction 又找到了多少额外 AND/latch 缩减；`scorr_time_ms`、`stran_time_ms` 和 `dsec_status` 分别给出代价与最终
正确性。`--jobs` 控制 benchmark 级并行，`--timeout` 是每个 ABC 子任务的超时，`--scorr-args` 和
`--stran-args` 可直接指定完整参数串。`--keep-artifacts` 用于保留失败 case 的 AIG 和日志。

CSV 在每完成一个 benchmark 后原子更新。运行中第一次按 `Ctrl-C` 会取消尚未开始的 queued case，并将已完成
case 写成可直接分析的 partial CSV；最多只有当前并行运行的 `--jobs` 个 case 仍可能在后台收尾。不要对旧版
脚本使用这一约定：旧版只在全部结束后写 CSV。

脚本不默认添加 `&stran -f`，因为 whole-miter shadow 属于开发期审计成本；最终 `dsec` 对每个 benchmark
仍然是强制的。对固定 `&scorr` 参数，扫描 `&stran` 的 `-M/-D/-B/-K/-Q/-W/-C/-T` 即可得到质量-时间曲线。

## 17. 正确性注意事项清单

实现和review时必须逐项确认：

1. `&scorr` proof 必须完成 base + induction；有限 BMC 不能冒充无限时序证明。
2. conflict/refinement/time limit 返回 UNKNOWN，永不提交。
3. TFO 使用原、加线、删线三个结构的并集，不能漏掉新边或删除后的替代路径。
4. 修改到达 RI 后必须跨到下一帧 RO；只比较当前 PO 不正确。
5. 最终语义比较 PO traces，不强制所有内部 RO 一一相等。
6. inductive frontier 必须有sound relation/obligation，不能在第 `F` 帧直接截断。
7. divisor 不能位于 target 的组合 TFO，避免组合环。
8. local window 的每个离开边都必须成为 boundary；boundary 不完整时只能扩大或 fallback。
9. 小窗口 SAT 可能在更远下游被屏蔽，可扩大窗口；UNSAT 只有在 boundary 完整时才可接受。
10. structural cleanup 在显式 add/remove proof 之后执行；cleanup 必须使用ABC已有的等价保持操作。
11. accepted transaction 后第一版保守重建 fanout、TFO、signature 和proof metadata。
12. 并行候选基于旧snapshot时只能并行筛选/证明，提交必须串行并在当前网络上重新验证。
13. simulation 和全divisor bit-parallel matching 只负责候选生成，不能替代 formal proof。
14. 开发阶段 local proof 必须与 whole-miter shadow oracle 对照；正式算法稳定后关闭逐candidate audit。
15. 每个最终benchmark输出仍运行一次独立 `dsec/PDR`，用于发现实现错误，不作为主算法proof步骤。

## 18. 下一步实现框架：specification-driven divisor synthesis

下一阶段的研究重点不是继续盲枚举 divisor，而是把每个 victim 推导出的
`M1 => h=1`、`M0 => h=0` 当作一个不完全规格，并用它指导 divisor 的筛选与构造。
这对应两篇工作的结合：SODC 提供时序可观测性/局部证明的语义边界；randomized transduction
说明“加线再删线”可创造新的 don’t-care。这里的区别是：新增线 `h` 的目标函数先由待删
victim 计算出来，再寻找或构造满足该规格的 `h`。

### 18.1 迭代顺序

1. **基线与日志。** 先完成常数 `h=0/1` 的 redundancy baseline，区分 `SAT/UNSAT/UNKNOWN`，
   记录每个 victim 的规格大小、候选漏斗、证明时间和净 gain；这给出与 SODC 的直接比较点。
2. **持久 PatternDB。** 保留 random reachable trace、`&scorr`/local proof 的 CEX 以及后续
   定向 SAT pattern。每次提交 transaction 后重新模拟已有 PI trace，而不是清空样本；bit-parallel
   signature 只作安全的候选过滤。
3. **规格驱动的候选。** 依次尝试 existing literal、哈希等价 literal 和小构造函数。对于
   `h=a&b`，先要求 `a,b` 均覆盖 `M1`，再检查 `M0 & a & b = 0`；由此可在构造前剪枝，
   而不是为每对 divisor 建网并跑 proof。固定 support、level、AIG-cost 和 `top-K` 预算。
4. **CEGIS。** formal proof 的反例转成新 pattern，并一次淘汰所有违反该 pattern 的候选；
   只有 `UNSAT` transaction 才能提交，`SAT/UNKNOWN` 均不提交。
5. **逐级证明。** 先在完整 boundary 的小 TFO window 上证明；小 window 的 `SAT` 只表示
   “需要扩大 window”，不能据此否定候选。高分 survivor 扩大到完整时序 TFO，再使用复用
   `&scorr` 的 base + induction/CBS 基础设施作最终提交证明。
6. **性能化。** 在语义稳定后再接入 `-i` 的 structural-edit seed、active TFO、persistent
   unrolling/SAT；candidate 可以并行筛选或证明，但 commit 必须串行并在当前网络重新验证。

### 18.2 实验决策门

每一阶段先回答一个可证伪的问题，再扩展搜索空间：

- constant/SODC baseline 是否已有可观测的额外缩减？
- PatternDB + M1/M0 是否显著提高“通过 simulation 的候选 / 全部候选”比例？
- CEX 是否能在一次 proof 后批量删掉候选？
- existing divisor 不足时，一门/两门构造的净 gain 是否超过其 proof 成本？
- `-i` 风格局部证明能否与 whole-miter/dsec 审计一致，同时降低 proof time？

只有前一门成立才增加 constructed divisor 深度或 multi-wire transaction。这样可以把效果差的原因
明确归因为：规格没有机会、候选构造不足，还是时序证明开销，而不是把三者混在一次大搜索里。

### 18.3 已实现的第一轮闭环（2026-07-19）

- **Batch/PatternDB：** 每个 simulation batch 仍以随机 reset-reachable lanes 为底，但已保留最多 `-R`
  条 BMC CEX。CEX 的 PI trace（以及 register width 相符时的初始 state）被注入下一批 bit-parallel
  simulation；network transaction 后不会丢失这些 pattern。
- **CEGIS：** 当完整 local-TFO `&scorr` proof 未通过时，以 `-E` 帧 bounded BMC 尝试提取真实 SAT witness。
  只有 SAT witness 入库，并立即从相同 network snapshot 重新生成 `M1/M0`、筛选全部 candidates；没有
  witness 的失败只是不剪枝的 inconclusive 结果，绝不据此提交。
- **Adaptive proof：** `-A` 控制先验 TFO 深度。window 的每条 cut edge 都作为差异 boundary，因此 window
  PASS 是更强且 sound 的证明；window 未 PASS 一律扩展到原有完整 TFO，不会错误拒绝优化。
- **Profiling：** `&stran -p` 已分开报告 simulation、care/spec/search、gain、window miter/corr、完整
  retention/removal proof、CEX-BMC，以及 `stored-cex/restarts/sat/inconclusive`。target 行也给出该 gate 的
  window 命中和 CEX 产生情况。
