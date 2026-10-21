**最终 iteration2 保存核在必要 competitive 域中仍有明显数值负值。** 这是固定保存核的数值诊断，不是全域最小值、全局证明、Thomson 反例或 degree12 核族不可行结论。

固定一次读取的模型来自 [d12_competitive_probe2026_snapshot.json](</home/dsh/Thomson Problem/proof_work/d12_competitive_probe2026_snapshot.json>)；原始来源为 [d12_contact2026_results.json](</home/dsh/Thomson Problem/proof_work/d12_contact2026_results.json>)。所用 iteration=2，history=[0,1,2]，完整原文件 SHA256=`70211e9762a6893f3cf2699f115c1d3bf3e8212b58870268ec89b6bd02f7434c`。trace=7.801171936026683，reduced minB=9.768539625290575e-08；这些 PSD 数值不是精确 PSD 证书。后续没有跟随更新文件。

新 R 全程使用原始 A/c：从 [d12_contact2026_solver.py](</home/dsh/Thomson Problem/proof_work/d12_contact2026_solver.py>) 的 IndependentActual 类单独抽取执行，正确 Q0=1,Q1=t−uv,Q[k+1]=2(t−uv)Q[k]−(1−u²)(1−v²)Q[k−1]、六排列平均。未调用新 compiled。两个最终发现点另外由通用 mpR 原始矩阵递推在80位精度核对；该高精度计算仍非区间证明。

搜索域为 all dots∈[-1,14/25]、Gram≥0、R_old_h27≤K。K=7(U−B)=23110944441047426495795816172910031/50000000000000000000000000000000000000≈0.000462218888820948508；B来自 [nonsharp_d10_root25_7599205_v10.json](</home/dsh/Thomson Problem/proof_work/nonsharp_d10_root25_7599205_v10.json>)，U来自 [pair056_optimized_certificate.json](</home/dsh/Thomson Problem/proof_work/pair056_optimized_certificate.json>)。旧807项精确有理多项式仅在搜索中转浮点；没有另加旧 separable C 条件。旧根验证器未重跑。

旧 fullworst 与旧 seed1 三谷在最终模型上的点诊断如下；预算差列为 R_old−K，正数意味着该指定十进制点被预算排除。所有列出的预算符号均已另以 Fraction 精确求值，完整分数在结果中。

| 指定点 | 最终 R_new actualf | R_old−K | Gram（浮点显示） |
|---|---:|---:|---:|
| fullworst_from_iteration0 | 0.001919296312590441 | 0.002727813619464823 | -5.240252676230739e-14 |
| fullworst_from_iteration1 | 1.325221252827802e-05 | 0.0006632383451647298 | 0.4447017177510924 |
| fullworst_from_iteration2 | -0.004771723031149845 | 0.00446547936238023 | -6.128431095930864e-14 |
| final_fullworst_strict_inside | -0.004771475799791577 | 0.004465424757184059 | 2.019335577529979e-06 |
| seed1_valley_T1 | 3.051451937916005e-05 | -0.0004411936824326434 | 0.3758744707205931 |
| seed1_valley_T2 | 2.096449419489166e-05 | -0.0004509004355852844 | 0.7230428501255173 |
| seed1_valley_T3 | 2.445146496943273e-06 | -0.0004544180976134088 | 0.7482623899118641 |

最新 fullworst 和其 strict-inside 微移点均被精确旧预算排除；旧 T1/T2/T3 中心已经抬正。接触候选12点最大 |R_new|=3.42781e-15。这些有限点结果不能说明其邻域或其他三角均非负。

随机生成 24000 个候选，评估 2786 个 eligible 点（超过2000要求）；随机最小 R_new=-0.0011835940180014784。SLSQP 已完成 24 个起点，包括T1/T2/T3、12个candidate和candidate扰动；其中22条 success、20条终点满足严格浮点 eligible。未成功/不满足约束终点均保留，未用作域内最优点。DE约束包括Gram和旧R预算，限20秒，实际 8.106896 秒正常收敛，4399 个objective点。

| 已发现点 | R_new（80位原A递推，截显） | exact Gram（十进制显示） | exact K−R_old（十进制显示） |
|---|---:|---:|---:|
| random_minimum | -0.00118359401800135714856238… | 8.560113288485344e-05 | 0.00022287046778574302 |
| DE_best | -0.00212476557755960009327014… | 5.1252333715453137e-14 | 4.5056167889167487e-15 |

random_minimum coordinates: `-0.9994670105438834, -0.03345627511650647, 0.0021510521154539664`。

DE_best coordinates: `-0.9999972489976633, -0.001172828547513688, -0.0011728066803398662`。

随机负点的 Gram 与预算均有明显正余量。DE 最低点非常接近 Gram/K 双边界；因此还保留了这个更稳健的随机内点。两点均已精确 Fraction 核对 Gram>0、K−R_old>0 与点积界；这仅严格核对已指定十进制三角的必要域条件，R_new<0仍按数值 discovery 报告，且不说明可扩展为九点低能量配置。

唯一主job bash-857：exit0，job_output已收齐。主数值阶段 63.193737491 秒；仅对已发现两点做 Fraction+80位复核用 0.970260417 秒；合计 64.163997908 秒<90。没有第二轮搜索、SDP、T2延续或旧全球根重跑。所有本任务相关job均已收齐。

可复现文件：

- [d12_competitive_probe2026_probe.py](</home/dsh/Thomson Problem/proof_work/d12_competitive_probe2026_probe.py>)：固定 snapshot 输入的唯一有限数值程序；输出包含抽取的原A evaluator源文本、模型/依赖hash、指定点、24个完整SLSQP结果及DE结果。
- [d12_competitive_probe2026_results.json](</home/dsh/Thomson Problem/proof_work/d12_competitive_probe2026_results.json>)：完整数值结果及所用original A/c。
- [d12_competitive_probe2026_snapshot_metadata.json](</home/dsh/Thomson Problem/proof_work/d12_competitive_probe2026_snapshot_metadata.json>) 与 [d12_competitive_probe2026_snapshot.json](</home/dsh/Thomson Problem/proof_work/d12_competitive_probe2026_snapshot.json>)：迭代/SHA和原始全部模型数据。
- [d12_competitive_probe2026_verify_points.py](</home/dsh/Thomson Problem/proof_work/d12_competitive_probe2026_verify_points.py>) 与 [d12_competitive_probe2026_verified_points.json](</home/dsh/Thomson Problem/proof_work/d12_competitive_probe2026_verified_points.json>)：只复核已发现点的精确旧预算符号、Gram与80位actualf。
- [d12_competitive_probe2026_probe.log](</home/dsh/Thomson Problem/proof_work/d12_competitive_probe2026_probe.log>)：原运行日志。

运行环境为工作区根目录下 `PYTHONPATH=proof_work:proof_work/python_deps OPENBLAS_NUM_THREADS=1 python3 proof_work/d12_competitive_probe2026_probe.py`。为保护原artifact，重运行须先改用新输出prefix并绑定一个明确snapshot；不得覆盖本次证据。
