# TODO — 2026-06-04 晚上:incremental sim (`&scorr -I`) 测试

分支 `incre_sim`,binary 已 build(15:38)。新开关 `-I` = TFO-only 局部 resim,默认关。
设计/实现见 `md/scorr_incremental_sim_implementation.md`。

---

## 0. 前置确认(1 分钟)

```sh
./abc -c "&scorr -h" | grep -- "-I"     # 应看到 "-I : toggle incremental TFO-only resimulation after SAT"
```

把 benchmark 放好(log 里的路径是 `incre_spec/`)。重点 case:
- **ILA_Flute_BGEU / BLT / SRAI / XORI**  ← 唯一 sim 重的一族(Sim≈35%),主战场
- token_ring.42/43/47/49、Problem11、pals  ← 预期 sim≈0%,主要看**正确性**和**会不会变慢**

---

## 1. 测试矩阵(每个 case 三跑)

```sh
# A. baseline(全图 resim,随机 filler)
./abc -c "&r <case>.aig; &scorr -i -v;   &ps; &w out_base.aig" 2>&1 | tee base.log
# B. 增量 sim(局部 resim)
./abc -c "&r <case>.aig; &scorr -i -I -v; &ps; &w out_incr.aig" 2>&1 | tee incr.log
# C. 增量 sim + 细粒度 profile(看 cone 大小)
./abc -c "&r <case>.aig; &scorr -i -I -w" 2>&1 | tee incr_w.log
```

> 说明:都带 `-i`(active SRM),和现有 baseline 对齐;`-I` 只多了局部 resim。

---

## 2. 必看的三类观察

### (a) 正确性 —— 最高优先级,任何一条不过都要停下来查
1. **不崩溃 / 不 assert**。尤其留意 `cecCorrIncrSim.c` 里 `nWords` 一致性 assert。
2. **NEnd / 最终 ff·and 数**:B 相对 A 应当 **相等或更保守(化简略少)**,绝不能化简“更多”到不该等价的程度。
   - 看 `&ps` 的 `ff=` / `and=`,和 `_summary.tsv` 的 `NEnd`。
3. **soundness 硬检查**(关键!):baseline 和 incr 的化简结果做组合等价
   ```sh
   ./abc -c "&r out_base.aig; &miter -s out_incr.aig; &scorr; ... " # 或用 cec/&cec 对两个网络做等价
   ./abc -c "cec out_base.aig out_incr.aig"   # 若可比;不可比就分别 cec 回原图
   ```
   更稳的做法:分别确认 `out_base` 和 `out_incr` 都与**原始电路**序列等价(`dsec` / `&srm`+`bmc` 等你惯用的流程)。incr 只要 sound,二者都应通过。

### (b) cone 大小 —— 决定增量 sim 到底有没有用(看 incr_w.log)
每轮 `[prof N]` 行新增字段:
```
incr=loc/full/maxdirty/keys=<本轮局部batch数>/<fallback到全图的batch数>/<最大脏锥>/<nFrames*nObjs>
```
- 重点看 **低 CEX 轮**(`cex=R/T/F` 里 R 只有几百的那些)的 `maxdirty/keys` 比例。
  - `maxdirty/keys < ~15–20%` → cone 小,局部 sim 该轮赢 → **方向对**。
  - 即便低 CEX 轮 `maxdirty/keys` 仍接近 1 → 这些 CI 扇出太广,增量 sim 在 ILA 也救不了 → **转去打 floor/SAT**。
- 看 `loc` vs `full`:`full` 多 = 大多数 batch 撞 gate 退化成全图 = 没省。
- `[prof ALL]` 行:`loc`/`full` 是全程累计,`maxdirty` 是全程最大锥。

### (c) 时间 —— 是否真的更快(对比 base.log vs incr.log 末尾)
看末尾的 `Srm/Sat/Sim/Other/TOTAL`:
1. **Sim 是否下降**(这是 -I 的直接目标)。只在 ILA 族预期有明显变化。
2. ⚠️ **Sat 是否上升**:`-I` 放弃了 random filler 的 opportunistic split,可能少分类 → SAT 多干活。**重点确认 ILA 上 Sat 没涨过 Sim 省下的量**(否则净亏)。
3. **TOTAL 净变化**:ILA 看是否净赚;token_ring/pals/Problem11 看是否**没变慢**(sim≈0,只要 -I 的固定开销没拖累就行)。

---

## 3. 决策标准(测完据此定下一步)

| 观察到的情况 | 结论 / 下一步 |
|---|---|
| 任意 case 出现 unsound(化简多于 baseline 且等价检查失败) | **立刻停**,查 `cecCorrIncrSim.c` 的 refine / lane0 / RO-remap |
| ILA 低 CEX 轮 `maxdirty/keys < 20%` 且 TOTAL 净赚 | 方向对,调 `CEC_INCRSIM_FRAC_*` 做 sweep(0.05/0.1/0.2/0.3) |
| ILA 上 Sat 涨幅 ≥ Sim 降幅(净亏) | random filler 的 split 很关键 → 考虑“局部 cone 内补随机 lane” 或放弃 -I |
| 所有 case cone 都接近全图 | 增量 sim 此路不通 → 转 floor 复用(analysis §5)/ SAT 复用 |
| token_ring/pals/Problem11 因 -I 变慢 | -I 固定开销(dense 数组/source scan)过大 → 查或只在 sim 占比高时启用 |

---

## 4. 预期(基于上午 `hard_scorr_logs_v_i_w` 的旧 log)

- token_ring.47:时间几乎全在 **BMC 的 SAT** → `-I` 对它**无感**。
- token_ring.43:主 loop **SAT=65%** → `-I` 无感。
- pals / Problem11:**Other(per-iteration floor)=65–74%** → `-I` 无感,真正该打的是 floor。
- ILA_Flute:**Sim=35%**,且大量时间在“低 CEX 轮各付一次全图 sweep”的长尾 → **这是 -I 唯一可能赢的地方**,今晚重点量它的 cone。

---

## 5. 待讨论 / 可能的代码动作(测后再定,别提前做)
- 若决定试 “changed-repr TFO + 持久 pattern” 的另一条路线(见今天讨论),那是**另一套实现**,不是改参数。
- 若 ILA cone 小但 random-split 丢失导致 SAT 涨:试在 cone 内对未赋值 lane 填随机(局部随机 filler)。
