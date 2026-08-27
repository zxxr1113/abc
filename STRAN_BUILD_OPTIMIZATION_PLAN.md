# &stran Build candidate：数据结论、采集协议与优化路线

## 1. 当前结论

本轮分析使用 6 份最新的 root-mode CSV（共同 PASS case 做成对比较）。结论不是“proof 太慢”，而是 Build 的 resub 枚举/规范化太慢：

- 单 case 的 Build discovery / 总运行时间中位数为 67.5%–90.9%。
- resub enumeration / Build discovery 中位数为 92.8%–96.2%。
- `C1000,N20,B128,q50,w10` 相对 `C1000,N10,B64,q30,w8`，最终 reduction 平均只增加 0.338 个百分点，但 Build discovery 变为 4.076 倍，总时间变为 3.201 倍，并出现 61 个 timeout。
- 大配置的生成→证明→选择漏斗为 `74,265,293 → 174,193 → 8,063`：proof/gen 约 0.216%，selected/gen 约 0.0109%。继续无差别扩大 B/N/q 的质量密度很低。
- `b=1000` 相对 `b=100` 没有改善 Build：Build reduction 平均下降 0.110 个百分点，说明当前瓶颈不能靠单纯放宽 proof budget 解决。

因此第一优先级是：安全地跳过不可能成功的 root；再用 profiling 学出 staged/anytime 搜索次序和停止条件。暂不改变 proof soundness，也不先引入学习模型。

## 2. 已加入的 profiling 与安全 fast path

`schema=6` 将一个 Build candidate 从生成追踪到 proved、selected，并记录：

- 枚举漏斗：reservoir、pool、MFFC、iterator next、semantic invalid、non-positive/known/direct/page reject、accepted。
- iterator stage：one-gate、div-gate、gate-gate、greedy；各自 valid、accepted、耗时和最终 outcome。
- candidate 特征：raw resub rank、gate 数、discovery gain、CI overlap、最大 divisor rank。
- MFFC 分桶：root calls、iterator next、accepted、耗时。
- 每个 candidate 特征桶的 selected AND gain，用实际 QoR 贡献判断能否截断，而不是只看 selected candidate 数。

当前 fast path 只跳过 `MFFC=1` 的 constructed search。Build candidate 至少保留一个 gate，而接受条件是 `MFFC - gates > 0`，因此此类 root 不可能产生正 gain；0-gate constant/existing 情形由已有 direct lane 处理。

本地验证：

- `fib_05`：原版和新版都是 `726 → 712 AND, 64 Reg`，输出互相 `dsec` equivalent。
- `loopv3`：原版和新版都是 `1397 → 862 AND, 70 Reg`，输出互相 `dsec` equivalent。
- 两个 case 的 Build generated/proved/selected 计数逐项相同。
- `fib_05` 的同一 profiling 配置中，iterator next 从 49,301 降到 2,008；profile total 从约 0.111 s 降到约 0.083 s。小 case 的时间只作为正确性/方向性证据，服务器整套数据才用于报告加速比。

## 3. 服务器需要重新采集的数据

每次运行必须保留下列 provenance；runner 已自动写入 CSV：

- git commit、dirty 状态、ABC/runner/parser SHA-256；
- config ID、完整 `&scorr`/`&stran` 参数、UTC 开始时间；
- host/platform/Python、timeout、jobs、dsec mode；
- 输入 manifest ID、每个 AIG 的相对路径、大小和 SHA-256；
- 每阶段 wall/user/system CPU time、status、最终 AND/Reg、dsec status；
- 完整 schema-5/6 profile 列。

不要只上传 aggregate。需要一行一个 case 的原始 CSV，以便：

1. 只在共同 PASS case 上做 paired comparison；
2. 将 timeout/assertion 作为结果而不是删掉；
3. 同时报告 case-normalized median/mean 与 weighted work totals；
4. 检查少数高 gain candidate 是否被 cutoff 丢失。

## 4. 本地/服务器 case 设计

先用 `core` 套件，包含：

- 高 Build 正例：`loopv3`, `cal135`, `cal157`, `cal188`, `vis_QF_BV_bcuvis32`, `Float_div`；
- 中低收益正例：`xepic_a12`, `minepump_spec3_product38`；
- 结构不同或较慢的控制：`circular_pointer_top_w64_d16_e0`, `arbitrated_top_n3_w8_d32_e0`。

`all` 再加入更多正例和 expensive zero-Build 控制，包括 `circular_pointer_top_w128_d32_e0`、`arbitrated_top_n3_w8_d128_e0`、`pc_sfifo_2+token_ring.09`。控制 case 对 early stop 尤其重要：heuristic 不仅要保住正例，还要能尽快承认“这里找不到有价值的 Build candidate”。

收集：

```bash
bash scripts/collect_seqbuild_cases.sh BENCH_ROOT /path/to/stran_core core
bash scripts/collect_seqbuild_cases.sh BENCH_ROOT /path/to/stran_all all
```

脚本会输出 `manifest.tsv` 并列出缺失 basename。缺失项无需阻塞第一轮，但请连同输出发回。

## 5. 第一轮最小实验

第一轮隔离 B、q、N、K；不要同时改多个旋钮，组合配置只保留 `B32_q15`：

```bash
cd /path/to/codex-stran-proof-microbatch
make -j

AIG_DIR=/path/to/stran_core \
ABC_BIN=./abc \
OUT_DIR=/path/to/results/schema6_core \
JOBS=1 TIMEOUT=7200 SKIP_DSEC=0 \
bash scripts/run_stran_build_profile_sweep.sh

python3 scripts/analyze_stran_build_profile.py \
  /path/to/results/schema6_core/*.csv \
  | tee /path/to/results/schema6_core/analysis.txt
```

`JOBS=1` 是推荐的 profiling 模式，避免并发争用扭曲 wall/CPU。若服务器成本过高，可先在 core 上运行全部 7 个配置；之后只将 `ref` 和前两名带到 `all`/全 corpus。最终候选必须开启 dsec。

已有 6 份旧 CSV 的 paired 汇总：

```bash
python3 scripts/analyze_stran_build_sweep.py \
  --pairs \
  /path/to/old_results/stran_root_C0_N10_B64_K5_q30_j5_w3.csv \
  /path/to/old_results/stran_root_C100_N10_B64_K5_q30_j5_w3.csv \
  /path/to/old_results/stran_root_C100_N10_B64_K5_q30_j5_w8.csv \
  /path/to/old_results/stran_root_C1000_N10_B64_K5_q30_j5_w8.csv \
  /path/to/old_results/stran_root_C1000_N20_B128_q50_j5_w10.csv \
  /path/to/old_results/stran_root_Cb1000_N20_B128_q50_j5_w10.csv
```

## 6. 判定标准

硬门槛：

- 所有完成 case 的 dsec 必须 PASS；不得增加 assertion/crash。
- 比较只使用共同 PASS case，同时单列 gained/lost PASS 和 timeout。
- Build selected AND gain 的总捕获率至少 99%；任何 cutoff 都要检查每个高收益 case，而不只看全局总和。

优化目标：

- core 上 Build discovery wall 和 CPU 中位数至少 1.5× 加速；
- all/full corpus 上至少 1.3×；
- case-normalized 最终 extra reduction 中位数非劣于 ref 0.02 个百分点；总 final AND gain 至少保留 99%；
- expensive zero-Build 控制应明显减少 iterator next/time，不应把成本移到 proof lane。

## 7. 下一步 heuristic（由 schema-6 数据决定）

按风险从低到高：

1. **Static impossibility filter**：已实现 `MFFC=1` skip。继续检查 `pool-empty`、可证明的最小 gate 下界和 structural feasibility。
2. **Stage cascade**：先 one-gate/div-gate；只有前级没有足够质量密度时才进入 gate-gate/greedy。停止条件用“最近一段 iterator next 带来的 selected AND gain”，不是 accepted 数。
3. **Rank/divisor cutoff**：若前 `r` 个 raw recipe 或前 `d` 名 divisor 已覆盖 ≥99% selected gain，则动态缩小搜索；按 MFFC 桶单独估计，避免一个全局 cutoff 伤害大 MFFC root。
4. **Anytime budget**：给每个 root 初始小预算，按预测上界、历史 yield、MFFC 和当前 best gain 逐级加码。零收益 root 早停，高收益 root 保留长尾。
5. **Portfolio/cache**：对重复局部函数或 DSD 类别缓存成功 recipe；只有前四步仍不足时再做，避免先引入高复杂度状态。

第一轮数据回来后应先画/算四条 cumulative capture 曲线：raw rank、stage、divisor rank、gate 数，各自横轴为累计 generated/time，纵轴为累计 selected AND gain。曲线会直接决定第二轮实现是 stage cascade、rank cutoff，还是 MFFC-conditioned budget。

## 8. 论文依据

- Simulation-Guided Boolean Resubstitution：用 simulation signature 筛选候选、限制 divisor 数，并用 counterexample refinement 改善 pattern；支持先便宜候选、再逐级扩展的搜索结构。
  <https://people.eecs.berkeley.edu/~alanmi/publications/2020/iwls20_sim.pdf>
- Standardizing Boolean Transforms：将 resub 表达统一，并展示不同 solver 的质量/运行时间 trade-off；支持 solver/stage portfolio，而非单一大预算。
  <https://people.eecs.berkeley.edu/~alanmi/publications/2024/tech24_resub.pdf>
- Scalable Generic Logic Synthesis：强调 positive-gain k-resub、DAG-aware gain 以及生成前过滤。
  <https://msoeken.github.io/papers/2019_dac_1.pdf>
- Exact DAG-Aware Rewriting：DSD、exact synthesis 与缓存共同缩小重复局部搜索空间，适合作为后续高投入方案。
  <https://people.eecs.berkeley.edu/~alanmi/publications/2020/date20_rwr.pdf>
- Randomized Transduction：依据前轮效果动态调度高 effort search；支持把固定大预算改为反馈驱动的 anytime budget。
  <https://people.eecs.berkeley.edu/~alanmi/publications/2024/iwls24_transd.pdf>
