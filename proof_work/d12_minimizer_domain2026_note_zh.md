**新增点积下界 −0.9957 排除了此前近反足点，但相同 degree12 最终保存核在缩小后的必要域内仍有明显数值负谷。** 本次总数值阶段 17.813781247 秒，唯一job bash-881已收齐exit0；没有新SDP、旧全球根重跑、T2延续或第二次搜索。

新点积下界是父线程提供的 GLOBAL MINIMIZER 必要条件；这里没有将其推广到任意 E≤U 配置，也未在本任务内重证该条件。所用域为 Gram≥0、每个dot∈[−9957/10000,14/25]、R_old_h27≤K，K=7(U−B)=23110944441047426495795816172910031/50000000000000000000000000000000000000。旧R807项在搜索阶段转浮点，指定最差点随后以 Fraction 精确核对域条件。

固定输入仍是 [d12_competitive_probe2026_snapshot.json](</home/dsh/Thomson Problem/proof_work/d12_competitive_probe2026_snapshot.json>) 的最终 iteration2，SHA256 `70211e9762a6893f3cf2699f115c1d3bf3e8212b58870268ec89b6bd02f7434c`。原始 A/c 由 [d12_contact2026_solver.py](</home/dsh/Thomson Problem/proof_work/d12_contact2026_solver.py>) 的 IndependentActual 六排列Q递推独立评估，不调用新 compiled；完整 evaluator 文本与依赖hash嵌入结果。此前job857已完成收齐，本次未重复857或触及父线程提到的其他solver任务。

| 已发现点 | 新 R actualf（80位原A递推截显） | exact Gram 十进制显示 | exact K−R_old 十进制显示 |
|---|---:|---:|---:|
| random_low | -0.000914074014754752472105645… | 1.7727676690084689e-05 | 0.00019965938513119311 |
| DE_result | -0.000928711397218041099203678… | 1.0928646173579353e-13 | 0.00013909725778856775 |

random_low coordinates: `-0.9457080898901464, -0.6695418187936286, 0.39181335775890314`。
精确dot下界余量=62489887637317/1250000000000000，上界余量=8409332112054843/50000000000000000；exact necessary domain=True，old R≈0.00026255950368975542。

DE_result coordinates: `-0.9391148010394065, -0.6773164129765319, 0.38329155180117336`。
精确dot下界余量=113170397921187/2000000000000000，上界余量=2208855602485333/12500000000000000；exact necessary domain=True，old R≈0.00032312163103238075。

随机点有明确 Gram 与预算正余量，可避免把DE边界附近的浮点可行误差当结论。两点在有限十进制解释下的 Gram、旧预算与dot界已精确核对；80位新actualf仍是数值计算，不是新区间负值证书。这里不声称这些三角可扩展为九点极小配置，也不声称 degree12 核族不可行。

采样与有限搜索：

- 总生成 12000 个候选，评估 1444 个eligible随机点，超过1000要求；其中 81 个 R<−1e−7。原JSON字段名 `negative_below_minus_1e7_count` 对应源码实际阈值 −1e−7。
- 8个SLSQP起点全部尝试：T1/T2/T3、两个candidate的1e−4邻域、三个新random低点；5条success，5个终点严格满足浮点域。三条random局部终点有轻微负Gram，保留但不计为域内点。每起点2.4秒guard，全部原始状态保留。
- DE上限12秒，实际 4.464119270 秒正常收敛，4543个objective点；没有延长或重启。
- 全12个candidate最大 |R|=3.4278136e-15。两处candidate邻域局部结果只见约1e−15舍入尺度残差；这些有限起点不构成局部非负证明。

旧T1/T2/T3中心新R依次为 3.0514519379160054e-05, 2.0964494194891659e-05, 2.4451464969432735e-06，三者均为正。此前random与DE近反足点的最低dot均精确低于−.9957；排除记录保留在结果。新的负谷位于约(−.9391,−.6773,.3833)附近，现有两点诊断不构成其完整范围或最低值断言。

归档与复现：

- [d12_minimizer_domain2026_results.json](</home/dsh/Thomson Problem/proof_work/d12_minimizer_domain2026_results.json>)：完整有限搜索、8个SLSQP状态、精确域分数、80位actualf、依赖hash、模型迭代/SHA与已抽取evaluator。
- [d12_minimizer_domain2026_probe.py](</home/dsh/Thomson Problem/proof_work/d12_minimizer_domain2026_probe.py>) 与 [d12_minimizer_domain2026_probe.log](</home/dsh/Thomson Problem/proof_work/d12_minimizer_domain2026_probe.log>)：唯一数值程序及原日志。
- [d12_competitive_probe2026_snapshot_metadata.json](</home/dsh/Thomson Problem/proof_work/d12_competitive_probe2026_snapshot_metadata.json>) 与 [d12_competitive_probe2026_snapshot.json](</home/dsh/Thomson Problem/proof_work/d12_competitive_probe2026_snapshot.json>)：冻结原模型及完整 original A/x/N/c。

工作区根目录复现命令为 `PYTHONPATH=proof_work:proof_work/python_deps OPENBLAS_NUM_THREADS=1 python3 proof_work/d12_minimizer_domain2026_probe.py`；为了保留证据，重运行须另选输出prefix。本任务没有证明域内非负、域最小值或全球最优。全球严格LB不因这些数值诊断改变。
