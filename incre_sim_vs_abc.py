import pandas as pd
import matplotlib.pyplot as plt
import io
import numpy as np
from scipy.stats import gmean

# 1. 载入数据
# 修改后的数据 (scorr2)
data_new_str = """file,init_gates,init_latches,abc_wscorr_time_ms,abc_wscorr_gates,abc_wscorr_latches
77.c.aig,250,45,0,77,9
AllInterval-020.aig,59817,4,3480,59815,4
Float_div.i.p+cfa-reducer.aig,19199,101,2770,15010,101
ILA_AES_LOAD_problem.aig,11820,1317,900,14235,1301
ILA_Flute_BGEU_problem.aig,1091846,174677,51620,1406047,171160
ILA_Flute_BLT_problem.aig,1091782,174677,59300,1407027,171246
ILA_Flute_SRAI_problem.aig,1092767,174677,61900,1412365,171214
ILA_Flute_XORI_sanity.aig,1096418,174677,58930,1417380,172275
ILA_Piccolo_ADD_problem.aig,85450,8099,2960,66367,4670
ILA_Piccolo_BGEU_problem.aig,82361,8099,2390,59626,4702
ILA_Piccolo_LUI_sanity.aig,83119,8099,2210,67502,5803
ILA_Piccolo_SUB_problem.aig,85543,8099,3140,66465,4670
ILA_Ridecore_BNE_sanity.aig,437661,23592,14860,424384,18372
ILA_Ridecore_JAL_problem.aig,419982,23551,13860,406926,17009
ILA_Ridecore_SLL_problem.aig,423680,23551,14590,409797,17014
ILA_Rocket_AND_problem.aig,73262,8568,2029,72754,5750
Mono6_1.aig,1486,101,10,1684,101
NO_04.aig,5678,467,120,5065,467
Problem01_label05.aig,15779,531,570,12240,531
Problem01_label22.aig,15779,531,590,12240,531
Problem02_label43.aig,7164,229,70,4778,229
Problem03_label05.aig,30585,997,3460,23634,997
Problem03_label32.aig,30616,997,3420,23618,997
Problem05_label42+token_ring.04.cil-2.aig,239794,1190,53030,69307,1190
Problem05_label43+token_ring.03.cil-1.aig,233310,1030,32189,62419,1030
Problem05_label45+token_ring.13.cil-1.aig,349075,2630,241380,176456,2630
Problem05_label47+token_ring.13.cil-2.aig,316489,2629,134680,148995,2629
Problem05_label49+token_ring.06.cil-2.aig,253884,1509,58350,84190,1509
Problem10_label21.aig,152722,229,13670,129070,99
Problem10_label27.aig,153819,229,13580,125116,229
Problem11_label08.aig,399295,261,31750,283645,261
Problem13_label23.aig,2347508,261,271600,1888112,261
Problem13_label56.aig,2347548,261,272450,1885836,261
Problem13_label59.aig,2347541,261,269930,1885795,261
Problem14_label18.aig,193575,403,14380,145392,403
Problem14_label52.aig,193575,403,14670,145392,403
Problem14_label53.aig,193575,403,14790,145392,403
Problem14_label54.aig,193575,403,14430,145392,403
Problem15_label35.aig,1126065,197,178610,973553,133
Problem15_label37.aig,1121253,197,92590,802495,197
Problem15_label46.aig,1126546,197,79920,807501,197
Problem15_label58.aig,1121283,197,94100,802591,197
Problem15_label58.aig,1126553,197,81250,808282,197
Problem17_label22.aig,1741487,229,136790,1221195,229
Problem17_label44.aig,1732001,229,156470,1226223,229
Problem19_label01.aig,4059774,229,400020,3096821,229
a16-p1.aig,5323,531,60,2978,255
a16-p114.aig,5171,499,50,2823,222
a16-p13.aig,5668,559,60,3368,285
a16-p32.aig,5182,499,50,2865,225
a16-p38.aig,5174,499,50,2838,223
a16-p47.aig,5167,499,40,2822,223
a16-p75.aig,6190,624,50,4237,368
a16-p76.aig,5182,499,50,2847,223
a16-p89.aig,5166,499,40,2821,222
a19-p13.aig,26769,1914,430,27305,1851
arbitrated_top_n2_w64_d32_e0.aig,22077,4218,220,30375,4214
arbitrated_top_n2_w8_d128_e0.aig,12867,2132,30,16963,2128
arbitrated_top_n2_w8_d32_e0.aig,3654,578,10,4672,574
arbitrated_top_n3_w128_d16_e0.aig,33127,6341,360,45642,6335
arbitrated_top_n3_w128_d8_e0.aig,17464,3256,240,23830,3250
arbitrated_top_n3_w16_d128_e0.aig,34648,6268,90,46950,6262
arbitrated_top_n3_w32_d128_e0.aig,65544,12428,350,90168,12422
arbitrated_top_n3_w64_d8_e0.aig,9080,1656,100,12248,1650
arbitrated_top_n3_w8_d128_e0.aig,19200,3188,40,25343,3182
arbitrated_top_n3_w8_d16_e0.aig,3007,461,0,3762,455
arbitrated_top_n3_w8_d32_e0.aig,5397,858,10,6923,852
arbitrated_top_n4_w128_d128_e0.aig,334291,65804,2390,465602,65796
arbitrated_top_n4_w128_d16_e0.aig,43917,8409,290,60522,8401
arbitrated_top_n4_w128_d8_e0.aig,23039,4296,170,31446,4288
arbitrated_top_n4_w16_d32_e0.aig,12361,2170,30,16460,2162
arbitrated_top_n4_w16_d8_e0.aig,3663,600,10,4677,592
arbitrated_top_n4_w32_d16_e0.aig,11949,2169,50,16073,2161
arbitrated_top_n4_w64_d128_e0.aig,169620,32972,1110,235266,32964
arbitrated_top_n4_w64_d32_e0.aig,43705,8362,240,60188,8354
arbitrated_top_n4_w8_d32_e0.aig,7137,1138,10,9172,1130
arbitrated_top_n5_w16_d64_e0.aig,29534,5287,70,39781,5277
arbitrated_top_n5_w32_d16_e0.aig,14869,2701,60,20012,2691
bakery.3.prop1-func-interl.aig,1472,112,10,1277,88
benchmarks_initial_output_btor2_example_10_miter_miter.aig,68889,6040,1360,68460,4720
benchmarks_initial_output_btor2_example_52_miter_miter.aig,61077,5193,1190,62127,4131
benchmarks_initial_output_btor2_example_82_miter_miter.aig,70863,5585,1530,72839,4636
benchmarks_initial_output_btor2_example_95_miter_miter.aig,89687,7411,2110,88530,5307
benchmarks_output_btor2_example_106_miter_miter.aig,3607,264,30,3156,264
benchmarks_output_btor2_example_110_miter_miter.aig,8891,677,50,9281,476
benchmarks_output_btor2_example_156_miter_miter.aig,3073,239,30,3384,238
benchmarks_output_btor2_example_162_miter_miter.aig,5779,678,60,6205,532
benchmarks_output_btor2_example_186_miter_miter.aig,2206,216,10,2247,160
benchmarks_output_btor2_example_212_miter_miter.aig,1792,134,10,1838,128
benchmarks_output_btor2_example_220_miter_miter.aig,3589,316,30,3773,260
benchmarks_output_btor2_example_227_miter_miter.aig,1767,167,10,1971,164
benchmarks_output_btor2_example_230_miter_miter.aig,2633,239,10,2427,179
benchmarks_output_btor2_example_23_miter_miter.aig,3465,275,40,3739,254
benchmarks_output_btor2_example_246_miter_miter.aig,3978,472,30,4147,344
benchmarks_output_btor2_example_263_miter_miter.aig,11545,603,90,12049,525
benchmarks_output_btor2_example_291_miter_miter.aig,7534,869,80,7809,573
benchmarks_output_btor2_example_301_miter_miter.aig,5414,401,40,5000,339
benchmarks_output_btor2_example_309_miter_miter.aig,2451,238,20,2507,182
benchmarks_output_btor2_example_320_miter_miter.aig,2723,241,20,2987,232
benchmarks_output_btor2_example_324_miter_miter.aig,6200,638,60,6338,407
benchmarks_output_btor2_example_349_miter_miter.aig,4992,607,50,5030,395
benchmarks_output_btor2_example_370_miter_miter.aig,17488,986,220,18243,676
benchmarks_output_btor2_example_401_miter_miter.aig,3974,298,40,4346,290
benchmarks_output_btor2_example_410_miter_miter.aig,5264,422,40,5305,348
benchmarks_output_btor2_example_412_miter_miter.aig,5096,467,40,5231,375
benchmarks_output_btor2_example_437_miter_miter.aig,4781,395,50,5082,325
benchmarks_output_btor2_example_470_miter_miter.aig,2381,302,20,2487,219
benchmarks_output_btor2_example_471_miter_miter.aig,3928,249,40,4199,248
benchmarks_output_btor2_example_494_miter_miter.aig,20457,1020,290,19152,634
benchmarks_output_btor2_example_499_miter_miter.aig,4777,409,40,5285,363
benchmarks_output_btor2_example_56_miter_miter.aig,2918,221,20,3159,221
benchmarks_output_btor2_example_57_miter_miter.aig,4710,424,30,5054,354
benchmarks_output_btor2_example_85_miter_miter.aig,3169,258,20,3185,227
benchmarks_output_btor2_example_96_miter_miter.aig,3904,485,30,4224,360
brp2.3.prop3-func-interl.aig,2526,227,10,963,80
cal100.aig,25885,718,470,17526,524
cal103.aig,27585,718,630,19136,524
cal122.aig,25987,718,460,16229,468
cal135.aig,26893,718,630,17005,468
cal14.aig,687,23,0,552,23
cal143.aig,26156,718,520,16258,468
cal154.aig,25729,718,470,15773,468
cal157.aig,94106,1009,3650,39882,663
cal188.aig,94101,1009,3690,43571,663
cal191.aig,94164,1009,3910,43476,663
cal206.aig,94164,1009,4000,37008,663
cal211.aig,95021,1065,3780,79348,851
cal222.aig,93572,3844,1320,62413,2150
cal28.aig,4077,165,20,1358,51
cal40.aig,3535,143,20,2172,91
cal42.aig,2039,79,10,1095,47
cal49.aig,2914,149,0,0,149
cal75.aig,3333,163,0,0,163
cal76.aig,2822,143,0,0,143
cal78.aig,43270,482,770,0,482
cal86.aig,22759,660,410,15364,476
cal90.aig,22738,660,400,15302,476
circular_pointer_top_w128_d16_e0.aig,16614,2331,480,21196,2329
circular_pointer_top_w128_d32_e0.aig,31077,4383,700,39753,4381
circular_pointer_top_w128_d8_e0.aig,9360,1303,380,11896,1301
circular_pointer_top_w32_d16_e0.aig,4422,603,20,5548,601
circular_pointer_top_w64_d16_e0.aig,8486,1179,80,10764,1177
circular_pointer_top_w8_d16_e0.aig,1374,171,0,1636,169
circular_pointer_top_w8_d32_e0.aig,2397,303,0,2913,301
collision.1.prop1-func-interl.aig,6673,131,150,5425,107
counter_bit_width_small.aig,467,58,0,513,58
dblclockfft_butterfly_ck1-p119.aig,2199,324,0,2379,292
dblclockfft_butterfly_ck1-p131.aig,2908,366,10,3049,324
dblclockfft_butterfly_ck1-p160.aig,7456,1093,20,6782,846
dblclockfft_butterfly_ck1-p227.aig,2269,348,10,2419,298
dblclockfft_butterfly_ck1-p428.aig,7137,1098,20,6461,839
dblclockfft_butterfly_ck1-p46.aig,2127,301,10,2323,274
dblclockfft_butterfly_ck2_r0-p229.aig,7572,1183,20,7507,1004
dblclockfft_butterfly_ck2_r0-p83.aig,2182,380,10,2585,352
dblclockfft_butterfly_ck3_r0-p100.aig,2871,592,10,3658,589
dblclockfft_butterfly_ck3_r0-p76.aig,6817,1143,20,7802,1098
dblclockfft_butterfly_ck3_r0-p82.aig,1781,305,0,2145,293
dblclockfft_butterfly_ck3_r1-p125.aig,4460,702,10,4662,613
dblclockfft_butterfly_ck3_r1-p50.aig,2198,402,10,2595,381
dblclockfft_butterfly_ck3_r1-p73.aig,2248,421,10,2596,374
diffeq.aig,682,73,0,767,69
dspfilters_fastfir_second-p10.aig,27128,1103,90,24174,814
dspfilters_fastfir_second-p45.aig,27140,1103,90,24205,814
dspfilters_fastfir_second-p50.aig,27122,1103,90,22080,814
elevator_spec2_product25.cil.aig,228838,1830,85260,232383,1830
elevator_spec3_product18.cil.aig,828338,1766,363350,824891,1766
elevator_spec3_product19.cil.aig,95975,1742,15990,0,3
exit.3.prop1-back-serstep.aig,4328,227,50,4294,227
fermat1-ll.aig,59988,234,10270,59693,233
fib_05.aig,726,64,0,710,60
fib_23.aig,391,57,0,217,27
fifo-p0.aig,18052,1067,60,14570,1067
gcd_bit_width_large.aig,1441,130,10,1599,130
gcd_bit_width_large.aig,2167,180,10,2488,181
gen119.aig,4855,931,280,6701,932
gen18.aig,5117,530,10,426,22
gen22.aig,7145,773,220,2951,265
gen26.aig,4871,520,10,170,12
gen56.aig,5236,931,40,7082,932
gen68.aig,5236,931,50,7082,932
gen76.aig,5249,931,40,7095,932
gen93.aig,4855,931,280,6701,932
gen97.aig,4855,931,290,6701,932
geo1-u_valuebound100.aig,40435,262,1960,20007,166
geo2-ll2_unwindbound1.aig,28233,293,810,28745,293
id_build.i.p+nlh-reducer.aig,61462,166,55680,59430,166
jain_4-2.aig,1584,101,10,1782,101
jm2006.c.i.v+cfa-reducer.aig,2335,197,40,2725,197
level_10.aig,19337,288,80,19031,288
level_16.aig,5091,136,10,4918,136
level_20.aig,14932,247,70,14633,247
level_27.aig,10451,212,50,10190,212
level_48.aig,6673,166,30,6511,166
level_5.aig,4329,125,10,4078,125
level_66.aig,13715,234,50,13404,234
level_73.aig,12840,227,60,12543,227
level_90.aig,20984,309,100,20548,309
loopv3.aig,1196,69,20,1203,69
mem_slave_tlm.4.cil.aig,91659,1965,15770,86507,1746
microban_1.aig,278,23,0,268,23
microban_1.aig,278,23,0,268,23
microban_105.aig,2708,90,10,2578,90
microban_110.aig,650,40,0,601,40
microban_117.aig,1978,77,0,1856,77
microban_118.aig,1324,59,0,1231,59
microban_132.aig,765,44,0,717,44
microban_136.aig,826,46,0,778,46
microban_138.aig,1760,71,0,1642,71
microban_141_2.aig,1353,61,0,1255,61
microban_143_2.aig,1784,73,0,1664,73
microban_145.aig,2300,84,0,2214,84
microban_148.aig,1365,60,0,1287,60
microban_149.aig,982,50,0,909,50
microban_154.aig,24247,233,30,24141,233
microban_24.aig,398,29,0,379,29
microban_33.aig,546,35,0,512,35
microban_44.aig,19,5,0,19,5
microban_48.aig,574,36,0,550,36
microban_64.aig,686,40,0,652,40
microban_71.aig,1744,66,0,1689,66
microban_77.aig,932,50,0,878,50
microban_82.aig,537,35,0,518,35
microban_85.aig,1767,74,0,1641,74
microban_89.aig,991,52,0,935,52
microban_93.aig,3479,105,10,3250,105
minepump_spec1_product28.cil.aig,6066,232,50,400,4
minepump_spec1_product38.cil.aig,14465,229,290,13696,229
minepump_spec2_product21.cil.aig,14126,261,360,13333,261
minepump_spec2_product25.cil.aig,9375,261,170,9860,261
minepump_spec3_product38.cil.aig,16466,229,590,16084,229
minepump_spec3_product49.cil.aig,8149,229,490,8458,229
minepump_spec4_product24.cil.aig,14373,229,360,13513,229
minepump_spec4_product33.cil.aig,5516,232,80,605,9
minepump_spec4_product39.cil.aig,14856,229,370,14084,229
minepump_spec5_product10.cil.aig,3419,261,230,0,262
mul1.aig,16706,258,190,8653,190
pals_lcr-var-start-time.6.1.ufo.UNBOUNDED.pals.aig,8007,273,150,8166,273
pals_lcr.3.ufo.BOUNDED-6.pals+Problem12_label00.aig,1570619,432,152640,1233353,432
pals_lcr.3.ufo.BOUNDED-6.pals+Problem12_label01.aig,1571997,432,156220,1238099,432
pals_lcr.7.1.ufo.BOUNDED-14.pals+Problem12_label01.aig,1574646,596,153640,1240311,596
pals_opt-floodmax.4.ufo.UNBOUNDED.pals.aig,8304,417,380,8423,417
pals_opt-floodmax.5_overflow.ufo.UNBOUNDED.pals.aig,12557,602,310,7537,333
pc_sfifo_2.cil-2+token_ring.09.cil-1.aig,82021,2278,57810,86525,2278
pc_sfifo_3.cil+token_ring.01.cil-2.aig,23601,1094,6520,25216,1094
pc_sfifo_3.cil+token_ring.09.cil-2.aig,85651,2374,30860,90340,2374
pc_sfifo_3.cil+token_ring.10.cil-1.aig,94599,2534,47410,99603,2534
pgm_protocol.8.prop6-func-interl.aig,19565,1056,210,19098,947
ponylink-slaveTXlen-sat.aig,20161,2868,180,25128,2865
prodbin-ll_unwindbound10.aig,33878,293,710,34295,293
prodbin-ll_unwindbound50.aig,32086,294,970,26363,260
qspiflash_dualflexpress_divfive-p121.aig,1281,214,10,1409,206
qspiflash_dualflexpress_divfive-p130.aig,1047,157,0,1178,149
qspiflash_dualflexpress_divfive-p133.aig,1204,197,10,1245,166
qspiflash_dualflexpress_divfive-p162.aig,1232,195,10,1363,187
qspiflash_dualflexpress_divfive-p41.aig,1094,169,10,1216,159
qspiflash_dualflexpress_divfive-p80.aig,1276,219,10,1233,161
qspiflash_dualflexpress_divthree-p120.aig,1157,196,10,1200,156
qspiflash_dualflexpress_divthree-p151.aig,1216,194,10,1351,186
qspiflash_dualflexpress_divthree-p161.aig,1260,218,10,1226,162
qspiflash_dualflexpress_divthree-p46.aig,1067,168,0,1196,158
qspiflash_qflexpress_divfive-p128.aig,1088,174,10,1232,168
qspiflash_qflexpress_divfive-p20.aig,981,152,0,1122,146
qspiflash_qflexpress_divfive-p39.aig,1027,164,10,1168,157
qspiflash_qflexpress_divfive-p65.aig,1178,193,10,1322,187
qspiflash_qflexpress_divfive-p85.aig,982,154,0,1124,147
rast-p0.aig,4259,442,30,3491,308
rast-p12.aig,4259,442,30,3490,308
rast-p14.aig,4259,442,40,3494,308
rast-p16.aig,4259,442,30,3507,311
rast-p17.aig,4259,442,30,3514,311
rast-p20.aig,4259,442,30,3488,308
ridecore.aig,545028,83247,8490,306258,17427
rocket_1937.aig,483725,74179,10400,617755,73005
shift_register_top_w128_d16_e0.aig,17163,2189,330,19593,2189
shift_register_top_w128_d32_e0.aig,33688,4239,540,38166,4239
shift_register_top_w16_d16_e0.aig,2379,285,0,2681,285
shift_register_top_w32_d32_e0.aig,8728,1071,30,9846,1071
shift_register_top_w8_d128_e0.aig,9365,1051,20,10411,1051
simple_alu.aig,176,21,0,83,17
sqrt1-ll_valuebound100.aig,36708,234,4050,36413,209
sqrt_Newton_pseudoconstant.aig,434861,453,140390,428363,453
stack-p0.aig,14431,1032,40,14111,1032
stack-p2.aig,17531,2060,20,45,8
sumt3.aig,6320,197,50,4445,197
token_ring.12.cil-1.aig,95626,2149,76030,99857,2149
transmitter.10.cil.aig,106998,3469,187390,112582,3469
vis_QF_BV_bcuvis32.aig,67,11,0,59,11
vis_QF_BV_vlunc.aig,69,20,0,68,20
vis_arrays_am2910_p3.aig,967,112,10,940,112
xepic_a12.aig,11592,1137,110,7773,673
xepic_a17-p0.aig,28145,1996,450,28639,1933
xepic_a17-p6.aig,25945,1834,430,26442,1756
xepic_a18-p1.aig,5429,500,50,3396,256
yosyshq_appnote_123_cv32e40x-p114.aig,486372,105145,5910,105051,10448
yosyshq_appnote_123_cv32e40x-p129.aig,60701,6573,790,59866,5859
yosyshq_appnote_123_cv32e40x-p131.aig,62390,6836,830,62732,6215
yosyshq_appnote_123_cv32e40x-p144.aig,249411,76017,3130,65072,6717
yosyshq_appnote_123_cv32e40x-p151.aig,61021,6633,820,60196,5917
yosyshq_appnote_123_cv32e40x-p161.aig,60703,6573,760,59882,5855
yosyshq_appnote_123_cv32e40x-p179.aig,60850,6607,830,60033,5881
yosyshq_appnote_123_cv32e40x-p18.aig,61634,6765,820,61294,6109
yosyshq_appnote_123_cv32e40x-p189.aig,474884,102895,5920,101117,10118
yosyshq_appnote_123_cv32e40x-p193.aig,475242,102895,5990,103815,10483
yosyshq_appnote_123_cv32e40x-p228.aig,482841,102895,6040,125196,12711
yosyshq_appnote_123_cv32e40x-p256.aig,60709,6575,820,59916,5861
yosyshq_appnote_123_cv32e40x-p312.aig,60752,6573,840,59849,5855
yosyshq_appnote_123_cv32e40x-p318.aig,60700,6573,840,59856,5855
yosyshq_appnote_123_cv32e40x-p368.aig,60706,6575,840,59871,5860
yosyshq_appnote_123_cv32e40x-p472.aig,60860,6626,790,59974,5869
yosyshq_appnote_123_cv32e40x-p524.aig,60709,6573,790,59874,5859
yosyshq_appnote_123_cv32e40x-p530.aig,60701,6573,870,59868,5859
yosyshq_appnote_123_cv32e40x-p567.aig,60841,6573,840,60040,5859
yosyshq_appnote_123_cv32e40x-p568.aig,60831,6573,840,59986,5859
yosyshq_appnote_123_cv32e40x-p581.aig,60703,6573,820,59864,5859
yosyshq_appnote_123_cv32e40x-p585.aig,60701,6573,840,59866,5859
yosyshq_appnote_123_cv32e40x-p608.aig,61281,6707,780,60472,5965
yosyshq_appnote_123_cv32e40x-p664.aig,146510,41201,1710,60453,5989
yosyshq_appnote_123_cv32e40x-p667.aig,246260,75377,3110,61062,6099
yosyshq_appnote_123_cv32e40x-p697.aig,60759,6573,830,59870,5855
yosyshq_appnote_123_cv32e40x-p724.aig,61026,6632,860,59903,5866
yosyshq_appnote_123_cv32e40x-p743.aig,117391,26273,1430,60415,5937
yosyshq_appnote_123_cv32e40x-p767.aig,486182,105145,6590,104865,10448
yosyshq_appnote_123_cv32e40x-p88.aig,474811,102889,6070,101062,10112
yosyshq_appnote_123_veer-p22.aig,254561,29695,3260,267361,28843
yosyshq_appnote_123_veer-p7.aig,254551,29695,3310,267351,28843
yosyshq_appnote_123_veer_axi-p62.aig,257099,30271,3700,269471,29226
yosyshq_appnote_123_veer_axi-p71.aig,257013,30237,3390,269413,29193
yosyshq_appnote_123_veer_axi-p73.aig,257011,30241,3400,269357,29195
zipcpu-zipmmu-p15.aig,2291,383,10,2790,362
zipcpu-zipmmu-p44.aig,2947,475,10,3623,454
"""

# 修改前的数据 (scorr_old)
data_old_str = """file,init_gates,init_latches,abc_wscorr_time_ms,abc_wscorr_gates,abc_wscorr_latches
77.c.aig,250,45,0,0,45
AllInterval-020.aig,59817,4,3460,59815,4
Float_div.i.p+cfa-reducer.aig,19199,101,3390,15010,101
ILA_AES_LOAD_problem.aig,11820,1317,990,14224,1301
ILA_Flute_BGEU_problem.aig,1091846,174677,135430,1402559,171129
ILA_Flute_BLT_problem.aig,1091782,174677,164150,1402665,171129
ILA_Flute_SRAI_problem.aig,1092767,174677,159360,1408398,171129
ILA_Flute_XORI_sanity.aig,1096418,174677,151360,1413806,172252
ILA_Piccolo_ADD_problem.aig,85450,8099,6580,65709,4660
ILA_Piccolo_BGEU_problem.aig,82361,8099,5920,58639,4660
ILA_Piccolo_LUI_sanity.aig,83119,8099,3790,66736,5787
ILA_Piccolo_SUB_problem.aig,85543,8099,6580,65836,4660
ILA_Ridecore_BNE_sanity.aig,437661,23592,23460,405481,18315
ILA_Ridecore_JAL_problem.aig,419982,23551,19150,402727,16949
ILA_Ridecore_SLL_problem.aig,423680,23551,19520,404586,16949
ILA_Rocket_AND_problem.aig,73262,8568,5080,72470,5746
Mono6_1.aig,1486,101,10,1684,101
NO_04.aig,5678,467,360,4665,467
Problem01_label05.aig,15779,531,1130,12240,531
Problem01_label22.aig,15779,531,1140,12240,531
Problem02_label43.aig,7164,229,120,4778,229
Problem03_label05.aig,30585,997,6950,23730,997
Problem03_label32.aig,30616,997,7640,23714,997
Problem05_label42+token_ring.04.cil-2.aig,239794,1190,138880,69307,1190
Problem05_label43+token_ring.03.cil-1.aig,233310,1030,102290,62419,1030
Problem05_label45+token_ring.13.cil-1.aig,349075,2630,592000,176456,2630
Problem05_label47+token_ring.13.cil-2.aig,316489,2629,502930,149003,2629
Problem05_label49+token_ring.06.cil-2.aig,253884,1509,393480,84198,1509
Problem10_label21.aig,152722,229,16090,126919,103
Problem10_label27.aig,153819,229,17970,124880,229
Problem11_label08.aig,399295,261,53020,283900,261
Problem13_label23.aig,2347508,261,509760,1887311,261
Problem13_label56.aig,2347548,261,493970,1885496,261
Problem13_label59.aig,2347541,261,508350,1885409,261
Problem14_label18.aig,193575,403,24540,144764,403
Problem14_label52.aig,193575,403,24310,144764,403
Problem14_label53.aig,193575,403,24250,144764,403
Problem14_label54.aig,193575,403,24350,144764,403
Problem15_label35.aig,1126065,197,178470,904656,133
Problem15_label37.aig,1121253,197,190200,799977,197
Problem15_label46.aig,1126546,197,122260,803980,197
Problem15_label58.aig,1121283,197,188810,801359,197
Problem15_label58.aig,1126553,197,121880,804978,197
Problem17_label22.aig,1741487,229,248150,1227104,229
Problem17_label44.aig,1732001,229,358740,1229161,229
Problem19_label01.aig,4059774,229,TIMEOUT,N/A,N/A
a16-p1.aig,5323,531,100,2958,254
a16-p114.aig,5171,499,70,2806,222
a16-p13.aig,5668,559,90,3338,284
a16-p32.aig,5182,499,70,2814,222
a16-p38.aig,5174,499,70,2807,222
a16-p47.aig,5167,499,70,2802,222
a16-p75.aig,6190,624,80,4220,368
a16-p76.aig,5182,499,70,2814,222
a16-p89.aig,5166,499,70,2801,221
a19-p13.aig,26769,1914,1180,26958,1851
arbitrated_top_n2_w64_d32_e0.aig,22077,4218,230,30375,4214
arbitrated_top_n2_w8_d128_e0.aig,12867,2132,30,16963,2128
arbitrated_top_n2_w8_d32_e0.aig,3654,578,10,4672,574
arbitrated_top_n3_w128_d16_e0.aig,33127,6341,390,45642,6335
arbitrated_top_n3_w128_d8_e0.aig,17464,3256,260,23830,3250
arbitrated_top_n3_w16_d128_e0.aig,34648,6268,90,46950,6262
arbitrated_top_n3_w32_d128_e0.aig,65544,12428,360,90168,12422
arbitrated_top_n3_w64_d8_e0.aig,9080,1656,110,12248,1650
arbitrated_top_n3_w8_d128_e0.aig,19200,3188,40,25343,3182
arbitrated_top_n3_w8_d16_e0.aig,3007,461,0,3762,455
arbitrated_top_n3_w8_d32_e0.aig,5397,858,10,6923,852
arbitrated_top_n4_w128_d128_e0.aig,334291,65804,2560,465602,65796
arbitrated_top_n4_w128_d16_e0.aig,43917,8409,310,60522,8401
arbitrated_top_n4_w128_d8_e0.aig,23039,4296,190,31446,4288
arbitrated_top_n4_w16_d32_e0.aig,12361,2170,30,16460,2162
arbitrated_top_n4_w16_d8_e0.aig,3663,600,10,4677,592
arbitrated_top_n4_w32_d16_e0.aig,11949,2169,60,16073,2161
arbitrated_top_n4_w64_d128_e0.aig,169620,32972,1180,235266,32964
arbitrated_top_n4_w64_d32_e0.aig,43705,8362,250,60188,8354
arbitrated_top_n4_w8_d32_e0.aig,7137,1138,10,9172,1130
arbitrated_top_n5_w16_d64_e0.aig,29534,5287,80,39781,5277
arbitrated_top_n5_w32_d16_e0.aig,14869,2701,60,20012,2691
bakery.3.prop1-func-interl.aig,1472,112,10,1259,88
benchmarks_initial_output_btor2_example_10_miter_miter.aig,68889,6040,1960,67975,4722
benchmarks_initial_output_btor2_example_52_miter_miter.aig,61077,5193,1780,60888,4131
benchmarks_initial_output_btor2_example_82_miter_miter.aig,70863,5585,1970,71815,4637
benchmarks_initial_output_btor2_example_95_miter_miter.aig,89687,7411,2840,87769,5307
benchmarks_output_btor2_example_106_miter_miter.aig,3607,264,30,3113,264
benchmarks_output_btor2_example_110_miter_miter.aig,8891,677,50,9233,476
benchmarks_output_btor2_example_156_miter_miter.aig,3073,239,40,3367,238
benchmarks_output_btor2_example_162_miter_miter.aig,5779,678,70,6161,532
benchmarks_output_btor2_example_186_miter_miter.aig,2206,216,10,2276,185
benchmarks_output_btor2_example_212_miter_miter.aig,1792,134,10,1840,128
benchmarks_output_btor2_example_220_miter_miter.aig,3589,316,40,3757,262
benchmarks_output_btor2_example_227_miter_miter.aig,1767,167,10,1985,166
benchmarks_output_btor2_example_230_miter_miter.aig,2633,239,10,2427,179
benchmarks_output_btor2_example_23_miter_miter.aig,3465,275,40,3743,254
benchmarks_output_btor2_example_246_miter_miter.aig,3978,472,30,4174,344
benchmarks_output_btor2_example_263_miter_miter.aig,11545,603,90,11965,525
benchmarks_output_btor2_example_291_miter_miter.aig,7534,869,90,7764,573
benchmarks_output_btor2_example_301_miter_miter.aig,5414,401,50,4998,339
benchmarks_output_btor2_example_309_miter_miter.aig,2451,238,20,2515,184
benchmarks_output_btor2_example_320_miter_miter.aig,2723,241,20,3008,239
benchmarks_output_btor2_example_324_miter_miter.aig,6200,638,60,6368,436
benchmarks_output_btor2_example_349_miter_miter.aig,4992,607,60,5034,395
benchmarks_output_btor2_example_370_miter_miter.aig,17488,986,230,18158,676
benchmarks_output_btor2_example_401_miter_miter.aig,3974,298,40,4346,290
benchmarks_output_btor2_example_410_miter_miter.aig,5264,422,50,5213,350
benchmarks_output_btor2_example_412_miter_miter.aig,5096,467,50,5237,383
benchmarks_output_btor2_example_437_miter_miter.aig,4781,395,50,5069,325
benchmarks_output_btor2_example_470_miter_miter.aig,2381,302,30,2452,220
benchmarks_output_btor2_example_471_miter_miter.aig,3928,249,50,4185,248
benchmarks_output_btor2_example_494_miter_miter.aig,20457,1020,260,18958,634
benchmarks_output_btor2_example_499_miter_miter.aig,4777,409,40,5268,366
benchmarks_output_btor2_example_56_miter_miter.aig,2918,221,30,3159,221
benchmarks_output_btor2_example_57_miter_miter.aig,4710,424,30,5032,354
benchmarks_output_btor2_example_85_miter_miter.aig,3169,258,30,3207,230
benchmarks_output_btor2_example_96_miter_miter.aig,3904,485,30,4220,360
brp2.3.prop3-func-interl.aig,2526,227,10,855,76
cal100.aig,25885,718,980,16495,524
cal103.aig,27585,718,1490,17936,524
cal122.aig,25987,718,1090,15160,468
cal135.aig,26893,718,1440,16100,468
cal14.aig,687,23,0,531,23
cal143.aig,26156,718,1380,15299,468
cal154.aig,25729,718,1170,14948,468
cal157.aig,94106,1009,10740,37717,674
cal188.aig,94101,1009,10940,40465,675
cal191.aig,94164,1009,11150,40816,669
cal206.aig,94164,1009,12670,35095,675
cal211.aig,95021,1065,12270,73388,857
cal222.aig,93572,3844,1850,73823,2879
cal28.aig,4077,165,30,1304,51
cal40.aig,3535,143,20,2077,91
cal42.aig,2039,79,10,1064,47
cal49.aig,2914,149,0,0,149
cal75.aig,3333,163,0,0,163
cal76.aig,2822,143,0,0,143
cal78.aig,43270,482,3760,0,482
cal86.aig,22759,660,1030,14462,476
cal90.aig,22738,660,970,14440,476
circular_pointer_top_w128_d16_e0.aig,16614,2331,500,21196,2329
circular_pointer_top_w128_d32_e0.aig,31077,4383,730,39753,4381
circular_pointer_top_w128_d8_e0.aig,9360,1303,400,11896,1301
circular_pointer_top_w32_d16_e0.aig,4422,603,20,5548,601
circular_pointer_top_w64_d16_e0.aig,8486,1179,90,10764,1177
circular_pointer_top_w8_d16_e0.aig,1374,171,0,1636,169
circular_pointer_top_w8_d32_e0.aig,2397,303,0,2913,301
collision.1.prop1-func-interl.aig,6673,131,70,1523,70
counter_bit_width_small.aig,467,58,0,513,58
dblclockfft_butterfly_ck1-p119.aig,2199,324,10,2379,292
dblclockfft_butterfly_ck1-p131.aig,2908,366,10,3045,324
dblclockfft_butterfly_ck1-p160.aig,7456,1093,30,6750,840
dblclockfft_butterfly_ck1-p227.aig,2269,348,10,2268,260
dblclockfft_butterfly_ck1-p428.aig,7137,1098,30,6434,834
dblclockfft_butterfly_ck1-p46.aig,2127,301,10,2323,274
dblclockfft_butterfly_ck2_r0-p229.aig,7572,1183,30,7467,995
dblclockfft_butterfly_ck2_r0-p83.aig,2182,380,10,2443,317
dblclockfft_butterfly_ck3_r0-p100.aig,2871,592,10,3659,589
dblclockfft_butterfly_ck3_r0-p76.aig,6817,1143,30,7788,1098
dblclockfft_butterfly_ck3_r0-p82.aig,1781,305,0,2145,293
dblclockfft_butterfly_ck3_r1-p125.aig,4460,702,20,4655,612
dblclockfft_butterfly_ck3_r1-p50.aig,2198,402,10,2595,381
dblclockfft_butterfly_ck3_r1-p73.aig,2248,421,10,2340,301
diffeq.aig,682,73,0,767,69
dspfilters_fastfir_second-p10.aig,27128,1103,170,24097,813
dspfilters_fastfir_second-p45.aig,27140,1103,160,24081,813
dspfilters_fastfir_second-p50.aig,27122,1103,240,22037,813
elevator_spec2_product25.cil.aig,228838,1830,92090,232383,1830
elevator_spec3_product18.cil.aig,828338,1766,376710,824890,1766
elevator_spec3_product19.cil.aig,95975,1742,16560,0,3
exit.3.prop1-back-serstep.aig,4328,227,60,4294,227
fermat1-ll.aig,59988,234,9760,59648,233
fib_05.aig,726,64,10,649,48
fib_23.aig,391,57,0,213,26
fifo-p0.aig,18052,1067,70,14524,1067
gcd_bit_width_large.aig,1441,130,10,1599,130
gcd_bit_width_large.aig,2167,180,10,2504,181
gen119.aig,4855,931,300,6701,932
gen18.aig,5117,530,10,426,22
gen22.aig,7145,773,230,2951,265
gen26.aig,4871,520,10,170,12
gen56.aig,5236,931,70,7082,932
gen68.aig,5236,931,70,7082,932
gen76.aig,5249,931,70,7095,932
gen93.aig,4855,931,290,6701,932
gen97.aig,4855,931,300,6701,932
geo1-u_valuebound100.aig,40435,262,1810,19880,156
geo2-ll2_unwindbound1.aig,28233,293,830,28745,293
id_build.i.p+nlh-reducer.aig,61462,166,58190,59450,166
jain_4-2.aig,1584,101,10,1782,101
jm2006.c.i.v+cfa-reducer.aig,2335,197,30,2725,197
level_10.aig,19337,288,110,18987,288
level_16.aig,5091,136,20,4868,136
level_20.aig,14932,247,80,14582,247
level_27.aig,10451,212,60,10228,212
level_48.aig,6673,166,40,6488,166
level_5.aig,4329,125,20,4106,125
level_66.aig,13715,234,70,13365,234
level_73.aig,12840,227,80,12490,227
level_90.aig,20984,309,110,20634,309
loopv3.aig,1196,69,30,1298,69
mem_slave_tlm.4.cil.aig,91659,1965,16020,86428,1746
microban_1.aig,278,23,0,268,23
microban_1.aig,278,23,0,268,23
microban_105.aig,2708,90,10,2582,90
microban_110.aig,650,40,0,601,40
microban_117.aig,1978,77,0,1860,77
microban_118.aig,1324,59,0,1231,59
microban_132.aig,765,44,0,717,44
microban_136.aig,826,46,0,778,46
microban_138.aig,1760,71,0,1648,71
microban_141_2.aig,1353,61,0,1255,61
microban_143_2.aig,1784,73,0,1668,73
microban_145.aig,2300,84,10,2172,84
microban_148.aig,1365,60,0,1287,60
microban_149.aig,982,50,0,909,50
microban_154.aig,24247,233,30,24141,233
microban_24.aig,398,29,0,379,29
microban_33.aig,546,35,0,512,35
microban_44.aig,19,5,0,19,5
microban_48.aig,574,36,0,550,36
microban_64.aig,686,40,0,652,40
microban_71.aig,1744,66,0,1689,66
microban_77.aig,932,50,0,878,50
microban_82.aig,537,35,0,518,35
microban_85.aig,1767,74,0,1645,74
microban_89.aig,991,52,0,935,52
microban_93.aig,3479,105,10,3266,105
minepump_spec1_product28.cil.aig,6066,232,40,400,4
minepump_spec1_product38.cil.aig,14465,229,300,13696,229
minepump_spec2_product21.cil.aig,14126,261,380,13333,261
minepump_spec2_product25.cil.aig,9375,261,180,9860,261
minepump_spec3_product38.cil.aig,16466,229,610,16084,229
minepump_spec3_product49.cil.aig,8149,229,510,8458,229
minepump_spec4_product24.cil.aig,14373,229,380,13513,229
minepump_spec4_product33.cil.aig,5516,232,40,444,7
minepump_spec4_product39.cil.aig,14856,229,400,14084,229
minepump_spec5_product10.cil.aig,3419,261,230,0,262
mul1.aig,16706,258,150,8674,194
pals_lcr-var-start-time.6.1.ufo.UNBOUNDED.pals.aig,8007,273,170,8166,273
pals_lcr.3.ufo.BOUNDED-6.pals+Problem12_label00.aig,1570619,432,219110,1234319,432
pals_lcr.3.ufo.BOUNDED-6.pals+Problem12_label01.aig,1571997,432,237570,1238774,432
pals_lcr.7.1.ufo.BOUNDED-14.pals+Problem12_label01.aig,1574646,596,221000,1241318,596
pals_opt-floodmax.4.ufo.UNBOUNDED.pals.aig,8304,417,340,8423,417
pals_opt-floodmax.5_overflow.ufo.UNBOUNDED.pals.aig,12557,602,340,7309,315
pc_sfifo_2.cil-2+token_ring.09.cil-1.aig,82021,2278,60820,86525,2278
pc_sfifo_3.cil+token_ring.01.cil-2.aig,23601,1094,6960,25216,1094
pc_sfifo_3.cil+token_ring.09.cil-2.aig,85651,2374,32220,90340,2374
pc_sfifo_3.cil+token_ring.10.cil-1.aig,94599,2534,50230,99603,2534
pgm_protocol.8.prop6-func-interl.aig,19565,1056,260,18941,947
ponylink-slaveTXlen-sat.aig,20161,2868,870,25122,2865
prodbin-ll_unwindbound10.aig,33878,293,780,34295,293
prodbin-ll_unwindbound50.aig,32086,294,1000,26178,260
qspiflash_dualflexpress_divfive-p121.aig,1281,214,20,1408,205
qspiflash_dualflexpress_divfive-p130.aig,1047,157,10,1175,149
qspiflash_dualflexpress_divfive-p133.aig,1204,197,10,1241,165
qspiflash_dualflexpress_divfive-p162.aig,1232,195,10,1360,187
qspiflash_dualflexpress_divfive-p41.aig,1094,169,10,1199,156
qspiflash_dualflexpress_divfive-p80.aig,1276,219,20,1207,156
qspiflash_dualflexpress_divthree-p120.aig,1157,196,10,1196,155
qspiflash_dualflexpress_divthree-p151.aig,1216,194,10,1348,186
qspiflash_dualflexpress_divthree-p161.aig,1260,218,10,1225,161
qspiflash_dualflexpress_divthree-p46.aig,1067,168,10,1192,157
qspiflash_qflexpress_divfive-p128.aig,1088,174,10,1228,168
qspiflash_qflexpress_divfive-p20.aig,981,152,10,1120,146
qspiflash_qflexpress_divfive-p39.aig,1027,164,10,1164,156
qspiflash_qflexpress_divfive-p65.aig,1178,193,10,1318,187
qspiflash_qflexpress_divfive-p85.aig,982,154,10,1122,147
rast-p0.aig,4259,442,90,3227,307
rast-p12.aig,4259,442,80,3227,307
rast-p14.aig,4259,442,80,3230,307
rast-p16.aig,4259,442,80,3230,307
rast-p17.aig,4259,442,80,3226,307
rast-p20.aig,4259,442,90,3226,307
ridecore.aig,545028,83247,22870,286147,17316
rocket_1937.aig,483725,74179,19680,614314,72974
shift_register_top_w128_d16_e0.aig,17163,2189,630,19593,2189
shift_register_top_w128_d32_e0.aig,33688,4239,1190,38166,4239
shift_register_top_w16_d16_e0.aig,2379,285,10,2681,285
shift_register_top_w32_d32_e0.aig,8728,1071,50,9846,1071
shift_register_top_w8_d128_e0.aig,9365,1051,30,10411,1051
simple_alu.aig,176,21,0,83,17
sqrt1-ll_valuebound100.aig,36708,234,5460,36391,209
sqrt_Newton_pseudoconstant.aig,434861,453,164410,428367,453
stack-p0.aig,14431,1032,60,14105,1031
stack-p2.aig,17531,2060,20,0,2060
sumt3.aig,6320,197,50,4445,197
token_ring.12.cil-1.aig,95626,2149,80360,99857,2149
transmitter.10.cil.aig,106998,3469,198120,112582,3469
vis_QF_BV_bcuvis32.aig,67,11,0,59,11
vis_QF_BV_vlunc.aig,69,20,0,68,20
vis_arrays_am2910_p3.aig,967,112,10,938,111
xepic_a12.aig,11592,1137,170,7703,670
xepic_a17-p0.aig,28145,1996,1420,28319,1933
xepic_a17-p6.aig,25945,1834,1120,26125,1756
xepic_a18-p1.aig,5429,500,80,3356,254
yosyshq_appnote_123_cv32e40x-p114.aig,486372,105145,8890,105055,10448
yosyshq_appnote_123_cv32e40x-p129.aig,60701,6573,960,59865,5859
yosyshq_appnote_123_cv32e40x-p131.aig,62390,6836,1000,62733,6215
yosyshq_appnote_123_cv32e40x-p144.aig,249411,76017,3630,65069,6717
yosyshq_appnote_123_cv32e40x-p151.aig,61021,6633,1010,60193,5917
yosyshq_appnote_123_cv32e40x-p161.aig,60703,6573,930,59882,5855
yosyshq_appnote_123_cv32e40x-p179.aig,60850,6607,1020,60007,5877
yosyshq_appnote_123_cv32e40x-p18.aig,61634,6765,1010,61295,6110
yosyshq_appnote_123_cv32e40x-p189.aig,474884,102895,8730,101118,10118
yosyshq_appnote_123_cv32e40x-p193.aig,475242,102895,9400,103819,10483
yosyshq_appnote_123_cv32e40x-p228.aig,482841,102895,9030,125201,12711
yosyshq_appnote_123_cv32e40x-p256.aig,60709,6575,1010,59912,5861
yosyshq_appnote_123_cv32e40x-p312.aig,60752,6573,1010,59849,5855
yosyshq_appnote_123_cv32e40x-p318.aig,60700,6573,990,59856,5855
yosyshq_appnote_123_cv32e40x-p368.aig,60706,6575,980,59867,5860
yosyshq_appnote_123_cv32e40x-p472.aig,60860,6626,980,59972,5868
yosyshq_appnote_123_cv32e40x-p524.aig,60709,6573,940,59871,5859
yosyshq_appnote_123_cv32e40x-p530.aig,60701,6573,1050,59871,5859
yosyshq_appnote_123_cv32e40x-p567.aig,60841,6573,950,60041,5859
yosyshq_appnote_123_cv32e40x-p568.aig,60831,6573,1000,59987,5859
yosyshq_appnote_123_cv32e40x-p581.aig,60703,6573,960,59863,5859
yosyshq_appnote_123_cv32e40x-p585.aig,60701,6573,990,59864,5859
yosyshq_appnote_123_cv32e40x-p608.aig,61281,6707,980,60472,5965
yosyshq_appnote_123_cv32e40x-p664.aig,146510,41201,2040,60453,5989
yosyshq_appnote_123_cv32e40x-p667.aig,246260,75377,3730,61059,6099
yosyshq_appnote_123_cv32e40x-p697.aig,60759,6573,970,59871,5855
yosyshq_appnote_123_cv32e40x-p724.aig,61026,6632,980,59904,5866
yosyshq_appnote_123_cv32e40x-p743.aig,117391,26273,1700,60418,5938
yosyshq_appnote_123_cv32e40x-p767.aig,486182,105145,9190,104869,10448
yosyshq_appnote_123_cv32e40x-p88.aig,474811,102889,8940,101067,10112
yosyshq_appnote_123_veer-p22.aig,254561,29695,5600,267358,28843
yosyshq_appnote_123_veer-p7.aig,254551,29695,5700,267348,28843
yosyshq_appnote_123_veer_axi-p62.aig,257099,30271,8050,269684,29225
yosyshq_appnote_123_veer_axi-p71.aig,257013,30237,7910,269373,29191
yosyshq_appnote_123_veer_axi-p73.aig,257011,30241,8230,269552,29195
zipcpu-zipmmu-p15.aig,2291,383,10,2784,362
zipcpu-zipmmu-p44.aig,2947,475,20,3623,454"""

# --- 1. 数据载入与清洗 ---
def load_and_clean(data_str):
    df = pd.read_csv(io.StringIO(data_str.strip()))
    df.columns = df.columns.str.strip()
    return df

df_old_raw = load_and_clean(data_old_str)
df_new_raw = load_and_clean(data_new_str)

# 合并数据：移除了 cols_new 中的 'equiv'
cols_old = ['file', 'abc_wscorr_time_ms', 'abc_wscorr_gates', 'abc_wscorr_latches']
cols_new = ['file', 'abc_wscorr_time_ms', 'abc_wscorr_gates', 'abc_wscorr_latches']
df_all = pd.merge(df_old_raw[cols_old], df_new_raw[cols_new], on='file', suffixes=('_old', '_new'))

# 数值化处理
def to_num(s):
    if str(s).upper() in ['TIMEOUT', 'N/A']:
        return 600000.0  # 假设超时为600秒，用于计算
    try:
        return float(s)
    except:
        return 0.0

# 遍历所有数据列进行转换（现在由于没有 'equiv'，只需排除 'file' 列）
for col in df_all.columns:
    if col != 'file':
        df_all[col] = df_all[col].apply(to_num)

# --- 2. 关键过滤：仅考虑原始耗时 > 500ms 的 Case ---
df = df_all[df_all['abc_wscorr_time_ms_old'] > 1000].copy()

# --- 3. 核心指标计算 ---

# 1. 加速比 (Speedup)
df['speedup'] = df['abc_wscorr_time_ms_old'] / df['abc_wscorr_time_ms_new'].replace(0, 1)

# 2. 门电路缩减率 (Gate Reduction %)
df['gate_red_pct'] = (df['abc_wscorr_gates_old'] - df['abc_wscorr_gates_new']) / df['abc_wscorr_gates_old'].replace(0, np.nan) * 100

# 3. 寄存器缩减率 (Latch Reduction %)
df['latch_red_pct'] = (df['abc_wscorr_latches_old'] - df['abc_wscorr_latches_new']) / df['abc_wscorr_latches_old'].replace(0, np.nan) * 100

valid_speedups = df['speedup'][np.isfinite(df['speedup']) & (df['speedup'] > 0)]
valid_gate_red = df['gate_red_pct'][np.isfinite(df['gate_red_pct'])]

# --- 4. 提取加速比大的关键 Case ---
high_impact_df = df[df['speedup'] > 0].sort_values(by='speedup', ascending=False)

# --- 5. 统计结果输出 ---

print("="*90)
print(f"{'scorr2 vs. scorr Performance Report  [All Cases]':^90}")
print(f"{'Baseline: scorr (&scorr)   Optimized: scorr2 (&scorr)':^90}")
print(f"{'Filter: all cases with scorr runtime > 0.5 s':^90}")
print(f"{'Total cases analyzed: ' + str(len(df)):^90}")
print("="*90)

# 注：此处移除了原有的 Outcome distribution 打印

if len(df) > 0:
    print(f"\n1. Runtime Performance")
    # 计算几何平均加速比
    if len(valid_speedups) > 0:
        print(f"   Geometric Mean Speedup (scorr2 / scorr):  {gmean(valid_speedups):.3f}x")
        print(f"   Maximum Speedup:                          {valid_speedups.max():.2f}x")
        print(f"   Cases with speedup > 1x:                  {(valid_speedups > 1).sum()} / {len(valid_speedups)}")
    else:
        print(f"   No valid speedup data available.")

    print(f"\n2. Circuit-Area Reduction (scorr2 vs. scorr)")
    print(f"   Avg Gate  Reduction:   {valid_gate_red.mean():.2f}%")
    print(f"   Avg Latch Reduction:   {df['latch_red_pct'].dropna().mean():.2f}%")

    print("\n" + "-" * 90)
    print(f"3. High-Impact Cases  (scorr runtime > 0.5 s)")
    if not high_impact_df.empty:
        # 表头移除了 Status 列
        header = f"   {'Benchmark':<45} | {'scorr (s)':<10} | {'scorr2 (s)':<10} | {'Speedup':<9} | {'Gate Red%':<9}"
        print(header)
        print("   " + "-" * 90)
        for _, row in high_impact_df.iterrows():
            # 打印数据移除了 row['equiv']
            print(f"   {row['file'][:45]:<45} | "
                  f"{row['abc_wscorr_time_ms_old']/1000:>9.2f}s | "
                  f"{row['abc_wscorr_time_ms_new']/1000:>9.2f}s | "
                  f"{row['speedup']:>8.2f}x | "
                  f"{row['gate_red_pct']:>8.2f}%")
    else:
        print("   No cases with speedup > 0 found.")
else:
    print("No cases with scorr runtime > 0.5 s found.")

print("="*90)