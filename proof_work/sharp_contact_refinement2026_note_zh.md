# Sharp contact refinement 2026：第一有限批次记录（仅数值发现）

本批次未得到严格全局证明，也未达到 minR > −1e−7 且 PSD >= −1e−9 的联合目标。最终 reduced blocks 数值为正，但在父线程已认证的必要竞争域 C>=0 内仍找到严格内部负点。它否定这一份具体数值核的非负性；不是 Thomson 构型反例，也不是该模型族不存在的证明。r 使用有限有理近似，未声称它就是候选的精确根。

## 直接可用结果

原始 A/x/N/B/c、系数索引、全部轮次指标和竞争域验证集中于 [sharp_contact_refinement2026_best_original_data.json](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_best_original_data.json>)。最终 PSD cutting-plane 模型在键 best_PSD_cutting_plane_solution；亦可从 [sharp_contact_refinement2026_results.json](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_results.json>) 的 best_solution 取得。c=4.161069114792391，F111=16.11522856415924，12c−1.5F111=25.75998653126984。basis nullities 为 (9,9,7,7,5,5,3,3,1,1,0)，190 个 reduced symmetric unknowns。

最终竞争域负点为 p=[-0.759220762336624, -0.29211600772137486, 0.32931701954562287]。80位按有限 JSON 十进制系数独立重算：

- R=-0.0000077376542507240858555040745229768330183647287001196750746148410267713792524346964。
- det Gram=0.3758745842903280841186196845880507300501580825536。
- C=0.030367191162598904809916182441277837010704396561260660049144365491641246312775207。

这点满足严格排序、box、Gram>0 与 C>0。一个约束 DE、多起点 SLSQP 和直接原 A recurrence/gradient polish 一致找到该谷。见 [sharp_contact_refinement2026_competitive_validation.json](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_competitive_validation.json>)。此前全 Gram-box 最坏点 (.3727866847029806,.56,−.040144373353202034) 的 C≈−.0017373224042854，不能作为竞争域障碍；它仅保留为原模型的整个box诊断。

## 接触与边界条件

原39eq包含12个R=0和九内点三方向gradR=0，数值rank32。以Fraction精确r特征后QR，并使用未round的12个Fraction三角重建，最小二乘一致误差8.22e−15。增加三个边界共六条 TᵀgradR=0，增广数值rank33、一致误差6.29e−15。rank均是数值标签，不是精确秩证明。

令 C_r=r²/2−1，B_r=2r²−1。边界(C_r,r/2,r/2)的非自动切向式是 R_v+rR_u=0；边界(−r,−r,B_r)的是 R_u−2rR_t=0；重复坐标的反对称切向由对称性自动。边界(−1/2)^3的全部切向由全对称自动，但法向系数的符号仍须检查。不能强加三个完整梯度为零。

两种非等边条件之间有结构性关系：它们的候选重数为6与3，沿半径r变分得到6L_C−6L_B=7E'_D3h(r)，其中L_C=R_v+rR_u、L_B=R_u−2rR_t。理由是候选nullspace矩和为二次型zᵀBz且z=0，其一阶变分为零，另外九内点梯度已消失。在真正驻点r*，E'=0只迫使L_C=L_B，不能据此令两者各自为零。这解释新增一个独立条件的数值现象。

所有新模型使用正确的边界二阶必要条件 lambda>=0 及 Tᵀ(H_R−lambda H_g)T PSD，其中gradR=lambda gradg，g=1+2uvt−u²−v²−t²，H_g=[[-2,2t,2v],[2t,-2,2u],[2v,2u,-2]]。同时施加九内点H_R PSD。未误加边界完整gradR=0或未经曲率修正的H_R PSD。

## 三轮切平面

原nonsharp训练11632点，旧sharp训练7988点，去重并集11632点；加入关键点以及1e−3、1e−2邻域（各400个三维点、各200个v=t点）和接触点后初始12833点，末轮14031点。所有旧训练点保留。objective=minimize tau/1e−6，无trace penalty；trace cap10000。CLARABEL每次设置time_limit90秒、tol_gap_abs/rel/feas=1e−10、max_iter350。单次迭代跨过截止时导致实际solver time约94秒；没有SCS fallback。整个批次共三次切平面solve，已结束。

| 轮(0起) | cuts | status | iter | solver秒 | min eig B | trace | 独立全box minR | 内部Hess min |
|---|---:|---|---:|---:|---:|---:|---:|---:|
| 0 | 12833 | MaxTime | 25 | 94.203 | -0.00400509938 | 646.872824 | -0.001213470542 | -0.00214637456 |
| 1 | 13282 | MaxTime | 25 | 94.372 | -0.00195406567 | 626.145537 | -6.772937626e-07 | -0.00112282272 |
| 2 | 14031 | AlmostSolved | 35 | 94.729 | 2.34436957e-06 | 660.664885 | -0.0004048077633 | 2.00375712e-05 |

前两轮min eig B明显为负，solver tau不能当界。末轮primal residual=2.044134182e-12，dual residual=1.713376484e-12，gap_abs=3.513381994e-09，status AlmostSolved/optimal_inaccurate，非精确PSD认证。末轮max contact error=6.1811667e-14，boundary tangent error=4.2703439e-14，原A最小eig=-9.569023e-15。独立原A实际值与compiled polynomial在搜得点最大差4.7212234e-14；独立sample design交叉差6.2172489e-15。

末轮三个边界在SVD正交切向基下：

| 候选index | lambda | corrected tangent Hess min eig |
|---|---:|---:|
| 3 | 0.000429029923949913 | 0.0108606876927829 |
| 4 | 0.00140442539464361 | 0.0194309728793525 |
| 7 | 5.63282072374561e-05 | 0.0388174487230056 |

关键点(−.29693709,.4225354,.4225354)的真实Gram=.4487280179298211925912。原PSD接触投影R≈−1.23366120835e−5；末轮R≈+.000773956487194874。该关键反例已被末轮修复，但另有上述竞争域谷。

## 独立 contact/PSD 可行性诊断

[sharp_contact_refinement2026_contact_psd.json](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_contact_psd.json>) 保存三个案例：原投影；加入rank33切向后的最近PSD解；再加完整正确local jets的最近PSD解。这些是无采样不等式的小型可行性诊断，不增加cutting-plane轮数。前两项最小B eig分别1.23e−11、3.56e−11；第三项4.59e−12，trace21.89149565，internal Hess min1.69e−11，三lambda最小2.31e−9，corrected tangent Hess最小.0001339704。第三项仅1.075秒、18iter，primal5.69e−12/dual1.46e−11/gap2.97e−10。由此可见新增必要条件与PSD在数值上相容；它们仍不足以保证全域非负，低trace local-jets核在key仍R≈−1.94668e−5。

## 复现与状态

主要脚本：[sharp_contact_refinement2026_core.py](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_core.py>)、[sharp_contact_refinement2026_refine.py](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_refine.py>)、[sharp_contact_refinement2026_contact_psd.py](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_contact_psd.py>)、[sharp_contact_refinement2026_competitive.py](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_competitive.py>)、[sharp_contact_refinement2026_export.py](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_export.py>)。它们均在本批次独立前缀文件中，不编辑父验证器、主报告或manifest。原始Q0=1,Q1=t−uv，Q[k+1]=2(t−uv)Q[k]−(1−u²)(1−v²)Q[k−1]，每个S对六种排列取平均。始终使用actualf=(2−2s)^−1/2，未使用旧h11。高精度点值是数值重算，非区间证明。

在工作目录 `/home/dsh/Thomson Problem` 用新输出前缀复现（不覆盖原数据）：

```sh
PYTHONPATH=proof_work:proof_work/python_deps OPENBLAS_NUM_THREADS=1 python3 proof_work/sharp_contact_refinement2026_reproduce.py --prefix sharp_contact_refinement2026_replay_
```

该runner按contact→三轮refine→export→competitive运行。仅重验原末轮竞争域可用：

```sh
PYTHONPATH=proof_work:proof_work/python_deps OPENBLAS_NUM_THREADS=1 python3 -c 'import sharp_contact_refinement2026_competitive as m; m.PREFIX="sharp_contact_refinement2026_recheck_"; m.run("sharp_contact_refinement2026_results.json")'
```

上式读取保留的第一批原模型并写入新的recheck前缀，若该前缀已有输出则拒绝覆盖。可自行换用另一个新前缀。全部随机种子、solver设置及完整训练点已保存。第一批相关job均已收齐：bash-516（失败的初始写文件诊断，exit2）、bash-524/534/539/546/550/556（exit0）。

后续：父线程在本批完成后明确授权另一有区别的有限竞争域批次：仅C>=0 cuts，<=3500 active cuts，保留全部训练审计，加入本竞争谷，tau+1e−8trace，最多三轮CLARABEL90秒。本记录和本批原数据保持为第一批次的历史状态。
