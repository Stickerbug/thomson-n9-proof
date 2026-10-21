# 固定坏三角的两球帽排除证书

本子任务已严格认证一个固定有理三角的球面外点代价下界，并认证锚点约束扩大 1e−8 后仍成立。它不构成九点 Thomson 全局证明，也没有提高全局能量下界。

固定三角参数为 u=−0.759220762336624、v=−0.29211600772137486、t=0.32931701954562287。锚点取 a=(1,0,0)，b=(u,sqrt(1−u²),0)，c=(v,(t−uv)/sqrt(1−u²),sqrt(1+2uvt−u²−v²−t²)/sqrt(1−u²))。代价为 phi(q)=R(u,a·q,b·q)+R(v,a·q,c·q)+R(t,b·q,c·q)，其中 R 是[旧严格下界模型](</home/dsh/Thomson Problem/proof_work/nonsharp_d10_root25_7599205_v10.json>)保存的精确有理 residual_monomial。

## 完整覆盖与算术

用 q=(2x,2y,sign*(1−x²−y²))/(1+x²+y²)，sign=±1，分别覆盖完整参数正方形 [−1,1]²。每个半球都对应其中单位圆盘，因此两个正方形覆盖整个球面，多出的重叠不影响证明。

源多项式总次数不超过27。将三个锚点坐标包围为384位二进制区间，再向下截到128位二进制有理数。程序逐坐标断言 k/2^128 <= true_coordinate < (k+1)/2^128，故任一单位 q 的锚点内积误差小于 3/2^128。令 Sder=sum |R_ijk|*(j+k)，精确验证 (1+3/2^128)^26<2，从而三个残差之和的误差不超过 18*Sder/2^128<1e−25。认证多项式阈值额外增加1e−25，抵消全部坐标近似误差。

将分母乘为 (1+x²+y²)^27 后，采用整数齐次 Horner 生成55×55二元系数，精确转换成Bernstein系数；64位二进制定点只向安全方向取整。细分使用de Casteljau逐步向下取整，始终保留下界。验证器只从完整根盒启动；不读取局部前沿，不把未解决盒当作成功。

## 剪枝与球帽条件

三个锚点约束剪枝仅在整盒的近似锚点内积严格大于 14/25 + allowed_slack + 3/2^128 时进行，保证不会误删真实允许域。allowed_slack在原证书为0，在扩域证书为1e−8。

两个球帽为 p_i·q>89/100，中心精确取 (9999999/10000000) 乘以下有限十进制向量：(0.3213589784,0.5134140431,−0.7956974471) 及 (0.3181271408,−0.7597356584,−0.5670950993)。程序用Fraction验证两中心平方范数都小于1。仅当整盒的某个球帽条件Bernstein下界严格为正，才允许使用较低代价阈值m；其它盒必须同时通过m和帽外阈值tau。

同帽两个单位点满足 q·s >= 2*(89/100)^2−1=2921/5000>14/25，因此在九点互距约束下每帽至多一个外点。两帽即使相交，其并集也至多容纳两个外点。若全域phi>=m、帽外phi>=tau且m<=tau，则六个外点的总代价至少2m+4tau。

## 保存的结果

| 证书 | m | tau | 正图节点/剩余 | 负图节点/剩余 | 六点代价下界 |
|---|---:|---:|---:|---:|---:|
| 原允许域 | 0.00003 | 0.0001 | 71/0 | 79/0 | 0.00046 |
| 锚点上限扩大1e−8 | 0.00003 | 0.0001 | 71/0 | 79/0 | 0.00046 |
| 扩域并强化阈值 | 0.00004 | 0.000105 | 77/0 | 95/0 | 0.0005 |

原证书正负图分别有32/34个正性终端盒、4/6个锚点排除盒；最大深度9/10。强化证书分别35/42个正性终端盒、4/6个排除盒，最大深度9/13。每个报告都保存完整终端盒的二进制位置、下界、树哈希、输入哈希与依赖哈希。

原验证器：[verify_fixed_triangle_two_caps_v1.py](</home/dsh/Thomson Problem/proof_work/verify_fixed_triangle_two_caps_v1.py>)；[原完整报告](</home/dsh/Thomson Problem/proof_work/fixed_triangle_two_caps_chart_certificate_v1.json>)。

扩域验证器：[verify_fixed_triangle_two_caps_widened_v1.py](</home/dsh/Thomson Problem/proof_work/verify_fixed_triangle_two_caps_widened_v1.py>)；[扩域完整报告](</home/dsh/Thomson Problem/proof_work/fixed_triangle_two_caps_widened_certificate_v1.json>)。

强化包装脚本：[verify_fixed_triangle_two_caps_stronger_v1.py](</home/dsh/Thomson Problem/proof_work/verify_fixed_triangle_two_caps_stronger_v1.py>)；[强化完整报告](</home/dsh/Thomson Problem/proof_work/fixed_triangle_two_caps_stronger_certificate_v1.json>)。强化计算在收到停止追加阈值实验的消息前已完成，之后不再追加。它通过显式设置模块M和TAU调用冻结的扩域验证器，报告记录实际阈值与包装脚本哈希。

与父线程精确预算核验 K=7(U−B)−R(T)≈0.0004411936503893693 结合，原六点下界0.00046已产生严格矛盾，强化下界0.0005裕量更大。应引用[精确预算报告](</home/dsh/Thomson Problem/proof_work/fixed_triangle_two_cap_budget_exact_v1.json>)中的Fraction比较；不能只将7(U−B)≈0.0004622188888与0.00046比较。下一阶段需要覆盖固定三角的非零邻域及其它负谷区域，当前不能声称整体负残差区已排除。

所有本子任务后台结果均已收齐：646/649为早期文件保存失败exit2，655/658为数值发现exit0，666为精确图构造exit0，673为首次全树认证exit0，681/683/686为正式保存及原/扩域/强化重跑exit0。没有仍在运行的本子任务后台计算。
