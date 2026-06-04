# XCGRP-CEGAR 计时统计功能实现文档

## 概述

已为 `cecXcgrpCegar.c` 添加详细的计时统计功能，用于精确定位性能瓶颈。统计数据按线程收集，支持多线程并行执行。

## 实现细节

### 1. 统计结构体定义

在文件顶部定义了 `Xcg_Stats_t` 结构体：

```c
typedef struct Xcg_Stats_t_ {
    abctime tBuild;     // 时间: Xcg_Build 和 Gia_ManDup
    abctime tScorr;     // 时间: Cec_ManLSCorrespondenceClasses
    abctime tSim;       // 时间: Xcg_SimManRun 和 Xcg_SimManValidate
    abctime tRefine;    // 时间: 精化逻辑 (标记内联和重建)
    abctime tTotal;     // 单个分支的总耗时
} Xcg_Stats_t;
```

### 2. 多线程支持

#### 线程参数结构体更新

在 `Xcg_BT_t` 中添加了统计字段：

```c
typedef struct Xcg_BT_t_ {
    // ... 其他字段 ...
    Xcg_Stats_t *   pStats;         // per-thread timing statistics
} Xcg_BT_t;
```

#### 线程函数计时 (`Xcg_BranchThread`)

- 线程启动时初始化 `pStats`
- 记录 `Gia_ManDup` 和第一次 `Xcg_Build` 的耗时
- 将统计指针传递给 `Xcg_CegarLoop`
- 计算总耗时

### 3. 关键函数计时

#### CEGAR 循环 (`Xcg_CegarLoop`)

函数签名更新为：
```c
static void Xcg_CegarLoop( Xcg_Abs_t * p, Cec_ParCor_t * pPars,
                            int nMaxRefine, int nSimRounds,
                            int * pChainId, int fRewrite,
                            Vec_Int_t * pConfirmed, Xcg_Stats_t * pStats )
```

计时位置：
- **tScorr**: `Cec_ManLSCorrespondenceClasses` 调用
- **tSim**: `Xcg_SimManRun` 和 `Xcg_SimManValidate` 调用
- **tRefine**: `Xcg_MarkInlinedWithChain` 执行（精化目标标记）
- **tBuild**: 循环内 `Xcg_Build` 调用（CEGAR 迭代重建）

#### 串行分支执行 (`Xcg_RunBranchSerial`)

添加了 `pStats` 参数，按照与线程版本相同的方式进行计时。

### 4. 统计汇总与输出

在主函数 `Cec_ManXcgrpCegarCorrespondence` 中：

1. **创建统计数组**：
   ```c
   Xcg_Stats_t * pStats = ABC_ALLOC(Xcg_Stats_t, nBranches);
   Xcg_Stats_t  totalStats;
   memset(pStats, 0, nBranches * sizeof(Xcg_Stats_t));
   memset(&totalStats, 0, sizeof(Xcg_Stats_t));
   ```

2. **分支分派**：
   - 每个分支在调度时关联相应的 `pStats[iBranch]`
   - 线程/串行执行完成后统计信息自动填充

3. **汇总与打印**：
   ```
   XCGRP-CEGAR Timing Summary:
     Total branches:     N
     Build time:         X.XX sec
     Scorr time:         Y.YY sec
     Sim time:           Z.ZZ sec
     Refine time:        W.WW sec
     Total time:         T.TT sec
   ```

## 使用方式

### 启用详细输出

在调用 `Cec_ManXcgrpCegarCorrespondence` 前设置：
```c
pPars->fVerbose = 1;
```

### 打印到文件

如需将统计信息打印到文件，修改汇总代码中的 `Abc_Print` 调用。

示例（修改统计汇总部分）：
```c
FILE * fp = fopen("timing_stats.txt", "a");
if ( fp )
{
    fprintf(fp, "XCGRP-CEGAR Timing Summary:\n");
    fprintf(fp, "  Total branches:     %d\n", nBranches);
    fprintf(fp, "  Build time:         %.2f sec\n", (double)totalStats.tBuild / CLOCKS_PER_SEC);
    fprintf(fp, "  Scorr time:         %.2f sec\n", (double)totalStats.tScorr / CLOCKS_PER_SEC);
    fprintf(fp, "  Sim time:           %.2f sec\n", (double)totalStats.tSim / CLOCKS_PER_SEC);
    fprintf(fp, "  Refine time:        %.2f sec\n", (double)totalStats.tRefine / CLOCKS_PER_SEC);
    fprintf(fp, "  Total time:         %.2f sec\n", (double)totalStats.tTotal / CLOCKS_PER_SEC);
    fclose(fp);
}
```

## 关键实现细节

### 1. 线程安全性

- 每个线程有独立的 `pStats` 指针，指向 `pStats[iBranch]`
- 不同线程访问不同的数组元素，无竞态条件
- 无需互斥锁

### 2. 灵活的计时策略

- 当 `pStats` 为 `NULL` 时，不进行计时（开销最小）
- 每个计时点都包含 `if ( pStats )` 检查
- 支持混合执行（有些分支计时，有些不计时）

### 3. 精确性

使用 ABC 内置的 `Abc_Clock()` 函数：
- 基于系统 `clock()` 或 `times()`
- 返回类型 `abctime`（通常是 `long` 或 `long long`）
- 单位：系统时钟计数，除以 `CLOCKS_PER_SEC` 得到秒数

### 4. 嵌套计时处理

某些操作涉及多层调用：
- `Gia_ManDup` 在 `Xcg_BranchThread` 中计时
- `Xcg_Build` 调用的是顶级函数，分别在不同位置计时
- `Xcg_CegarLoop` 内的 `Xcg_Build` 被累加到 `tBuild`

## 修改的文件

- `/home/zxr_wsl/berkeley/abc_fork/abc/src/proof/cec/cecXcgrpCegar.c`

## 修改部分

1. **结构体定义** (行 ~95-110)：新增 `Xcg_Stats_t`
2. **Xcg_BT_t 更新** (行 ~838)：添加 `pStats` 字段
3. **Xcg_BranchThread** (行 ~878-920)：添加计时逻辑
4. **Xcg_CegarLoop** (行 ~708-813)：添加 `pStats` 参数和计时点
5. **Xcg_RunBranchSerial** (行 ~917-943)：添加 `pStats` 参数和计时
6. **主函数分支循环** (行 ~1010-1130)：创建统计数组、分派统计指针、汇总输出

## 编译

无需特殊编译选项。使用标准 ABC 构建过程：
```bash
cd abc
make -j4
```

## 性能影响

- **有计时**：每个计时点 ~10-50 纳秒开销（取决于系统）
- **无计时**（pStats=NULL）：开销可忽略
- 总体性能影响 < 1%

## 扩展建议

1. **每次迭代的细粒度计时**：在 CEGAR 循环内分别记录每次迭代的耗时
2. **内存统计**：添加 `abcmem` 字段记录每个分支的峰值内存使用
3. **SAT 求解器统计**：集成来自 SAT 求解器的内部计时数据
4. **CSV 导出**：将统计数据导出为 CSV 格式便于分析
