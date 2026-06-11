# `&scorr -i` Alias Dependency Bug Report

## 1. 结论

目前的实验结果表明，已观察到的 `-i` 错误根因是 TFO 遍历遗漏了
speculative reduction 引入的 representative-to-member alias dependency。

之前增加的 unresolved SAT/UNKNOWN retry 保护并不是 400k 问题的必要修复。
移除该保护、只保留 alias 修复后，400k 仍然通过 `-d` 检查。这说明 retry
只是把出错 pair 的端点额外放入 seed，绕过了遗漏的 alias 边，因而碰巧
覆盖了 400k 的错误路径。

现有实验的因果关系如下：

| 实现 | 400k | 500k | 说明 |
|---|---:|---:|---|
| 原始 `-i` | 失败 | 失败 | TFO 缺少 alias dependency |
| retry、无 alias | 通过 | 失败 | retry 只能覆盖部分遗漏路径 |
| retry + alias | 通过 | 通过 | alias 修复加入后两个用例均通过 |
| alias、无 retry | 通过 | 待重新确认 | 已证明 retry 对 400k 不必要 |

因此可以确认：

- 400k 的直接根因是 alias dependency 遗漏。
- alias 修复对 500k 是必要的，因为 retry-only 版本仍然失败。
- 在 alias-only 版本重新运行 500k 后，才能用实验结果确认 alias 修复对
  两个用例都独立充分。

## 2. 错误机制

旧的增量实现从 `pReprs` 变化的对象出发，只沿原始 AIG 的 physical fanout
计算 TFO。这个图不足以描述当前 SRM 的真实依赖关系。

在 speculative reduction 中，class member 的 reduced literal 直接使用其
representative 的 reduced literal。它隐式增加了原始 AIG 中不存在的边：

```text
representative -> class member -> physical fanouts(member)
```

当 representative 的 reduced value 因 class refinement 发生变化时，所有
引用该 representative 的 members 以及这些 members 的 fanout cones 都可能
变化。旧 BFS 看不到 `representative -> member`，所以可能把其中的 pair
判定为 unaffected，并复用上一轮的 UNSAT 结果。

但该 pair 在当前 class snapshot 构造出的完整 SRM 中可能已经变成 SAT。
`-d` 检测到的错误本质上就是：

```text
pair is outside physical-AIG TFO
but
pair is inside speculative-SRM TFO
```

这不是 SAT solver 将 UNSAT 错判为 SAT，也不是 CEX resimulation 必须拆开
某个特定 pair 的问题。错误发生得更早：该 pair 没有进入本轮 active SRM，
因此正常 solver 根本没有重新求解它。

### 2.1 示例：physical-AIG TFO 之外、speculative-SRM TFO 之内

假设物理 AIG 中存在以下关系：

```text
s ──────► r

b,c ────► m ──────► y ──────► ...

q ────────────────────────────
```

当前 correspondence classes 为：

```text
pRepr[m] = r
pRepr[y] = q
```

物理 AIG 中，`r` 不是 `m` 的 fanin，`r` 也无法通过 physical fanout 到达
`m` 或 `y`。但是 speculative reduction 处理 `m` 时不会使用 `m` 的物理
逻辑，而是直接使用 representative `r`：

```text
copy(m) = copy(r)
```

因此 SRM 的实际依赖图包含一条原始 AIG 中不存在的 alias edge：

```text
s ─physical─► r ─alias─► m ─physical─► y
```

现在假设一轮 refinement 改变了 `s` 的 representative：

```text
old: pRepr[s] = t
new: pRepr[s] = GIA_VOID
```

那么 `s` 是本轮 TFO seed。这个变化可以继续影响 `r` 的 reduced literal。
例如，SRM 表达式可能从：

```text
old:
S = T
R = T & A
M = R
Y = R & D
```

变为：

```text
new:
S = U & V
R = (U & V) & A
M = R
Y = R & D
```

虽然 `pRepr[m] = r` 本身没有变化，但 `m` 在 SRM 中引用的 `r` 已经变化，
所以 `y` 的 SRM literal 也可能变化。

旧实现只沿 physical AIG fanout：

```text
seed s
  └─physical─► r
```

到达 `r` 后，由于物理 AIG 中不存在 `r -> m`，遍历停止：

```text
physical TFO = {s, r}
```

因此 `y` 不在 TFO 中，pair `(q,y)` 会被 `-i` 跳过。

正确的 speculative SRM TFO 必须加入 alias edge：

```text
seed s
  └─physical─► r
                  └─alias─► m
                               └─physical─► y
```

于是：

```text
speculative SRM TFO = {s, r, m, y}
```

pair `(q,y)` 对应的 SRM miter：

```text
real(q) XOR real(y)
```

已经可能发生变化，因此必须重新求解。这个例子具体展示了：

```text
pair (q,y) is outside the physical-AIG TFO
but inside the speculative-SRM TFO
```

当前修复构造的 `representative -> members` adjacency，正是在补充例子中的
`r -> m` 依赖。

## 3. 为什么 retry 曾经修好 400k

retry 保护把上一轮仍保持 merged 的 SAT/UNKNOWN pair 两端直接加入下一轮
TFO seed。对于 400k，这个额外 seed 恰好落入遗漏的依赖锥，因此错误 pair
被重新求解，测试不再失败。

这是一种保守绕行，而不是对依赖图的修复：

- 它不能覆盖并非 retry pair 自身、但通过 alias 受到影响的其他 pair。
- 500k 在 retry-only 版本中仍然失败，证明这种保护不完备。
- alias-only 的 400k 通过，证明 400k 不需要该保护。

所以当前实现已经移除 retry 状态、retry seeds 和相应收敛条件。

## 4. Alias 修复

`Cec_IncrMgrComputeTfo()` 每轮根据当前 `pReprs` 重建：

```text
representative -> all current class members
```

TFO BFS 对每个访问到的对象执行两种传播：

1. 沿 representative-to-member alias edges 传播。
2. 从访问到的对象继续沿 physical AIG fanout 传播。

RI-to-RO 的跨帧传播仍受 SRM unrolling depth 限制。ring 模式中新建或改写的
edge 不依赖 TFO 命中，而由 `Cec_IncrMgrRingEdgeChanged()` 强制进入 active
集合。

这样计算的是当前 speculative SRM dependency graph 的保守 TFO，而不只是
原始 AIG 的 TFO。

## 5. `-d` Shadow Oracle 的验证方法

运行方式：

```text
&scorr -i -d
```

`-d` 必须和 `-i` 一起使用。对主 refinement loop 的每个增量轮次，代码在
同一个 class snapshot 和同一个 TFO mask 上构造两个互补集合：

```text
U_r = A_r union S_r
A_r intersection S_r = empty
```

其中：

- `U_r` 是当前完整 SRM 的 candidate pairs。
- `A_r` 是正常 `-i` 选择并重新求解的 active pairs。
- `S_r` 是本轮被 `-i` 跳过的 skipped pairs。

`CEC_EMIT_ACTIVE` 和 `CEC_EMIT_SKIPPED` 使用相同的 speculative reduction
和 SRM topology，只改变输出 PO 的 emission predicate。新建或改写的 ring
edge 永远属于 active 集合，不会错误地进入 skipped 集合。

对 `S_r` 构造 skipped-only shadow SRM 后，`Cec_ManIncrOracleCheck()`：

- 创建独立 SAT manager，不共享 active solver 的 learned clauses 或顺序。
- 设置 `nBTLimit = 0`，即不使用 conflict limit。
- 求解 shadow SRM 的每一个 skipped PO。
- 保留 PO 到 `(iRepr, iObj)` 的映射，以便报告具体错误 pair。

每轮所检查的核心条件是：

```text
for every P in S_r:
    SAT(full_current_SRM(P)) == UNSAT
```

因此，只要一轮输出：

```text
[incr-oracle r=N PASS skipped=M all-UNSAT]
```

就证明该轮所有被 `-i` 省略的求解，在当前 SRM 中都确实为 UNSAT。若存在
任何错误跳过，会输出：

```text
INCR-ORACLE BUG: round=N output=K pair=(iRepr,iObj), ...
```

并打印可用的 partial CEX。若 solver 返回 UNKNOWN，则输出
`INCR-ORACLE UNKNOWN`；UNKNOWN 不能作为正确或错误的证明。

## 6. 最终 Certificate

正常 `-i` 在没有新的 representative 或 ring-edge 变化时会直接收敛。
开启 `-d` 后，收敛点不会立即退出，而是清空 active TFO，使当前保留的所有
candidate pairs 都进入 skipped-only shadow SRM，再用无 conflict limit 的
独立 solver 全部求解。

此时：

```text
A_final = empty
S_final = U_final
```

最终 oracle PASS 因而证明：

```text
for every retained final correspondence P:
    SAT(final_current_SRM(P)) == UNSAT
```

这既检查每轮增量跳过，也防止某个错误 correspondence 一直保留到收敛点。

## 7. “证明正确”的准确边界

`-d` 可以证明的是：

> 相对于相同 snapshot 下的完整 SRM，主 refinement loop 中 `-i` 跳过的
> pair 没有包含 SAT pair；最终保留的全部 correspondence 在最终 SRM 中
> 都是 UNSAT。

该结论成立需要日志完整运行到最终 PASS，并且过程中没有：

- `INCR-ORACLE BUG`
- `INCR-ORACLE UNKNOWN`
- 外部终止、崩溃或未完成运行

它不是对整个 ABC 实现的无条件形式证明。它仍然信任：

- 完整 SRM builder 的语义正确。
- SAT solver 的 soundness。
- class/refinement 数据结构没有与 SRM 之外的独立错误。

另外，当前 `-d` 的 shadow oracle 位于主 refinement loop。BMC prepass 虽然
也使用 `-i` 的 TFO filter，但目前没有逐轮构造 BMC skipped-only shadow
SRM。因此当前证书应表述为“主 refinement loop 的 incremental skipping
certificate”，不能表述为已逐轮覆盖程序中所有 `-i` 路径。

## 8. 当前验证状态

- alias-aware TFO 已保留。
- unresolved SAT/UNKNOWN retry 保护已移除。
- 400k 在 alias-only 版本中通过 `-d`。
- 500k 曾在 retry + alias 版本中通过；alias-only 版本仍建议重新运行。
- 本地 `make -j4` 已通过。

如果 alias-only 的 500k 也完整输出最终 oracle PASS，则现有两个失败用例
都支持同一个结论：观察到的 `-i` correctness bug 是 speculative alias
dependency 在 TFO 中缺失，而不是独立的 unresolved-pair retry 问题。
