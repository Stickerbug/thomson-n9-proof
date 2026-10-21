# 十阶凸组合核的精确化准备与全域拼接

状态更新：有理weights[112219/500000,0,387781/500000]已冻结；真实r*全部45contact与reducedB严格PD已认证（delta最大约1.440298496066966e−12）；全部12类f/H27二阶jets通过。仍未证明全域非负。下文准备阶段文字保留其历史语境。

## 基与种子

发现包sharp_contact_refinement2026_batch3_best_original_data.json的SHA256为099e143bb86171f6292ef19ff7ae051510c76f0585e42bdcada7c866f46b4929。first与两third的N在k=0..10逐JSON元素完全相等；可直接对190个reducedB上三角坐标有理混合。共同基的严格含义仍由真实r*的解析Ntilde与seed1证书的有理T1定义，不能将浮点N本身当exact。

make_seed.py接受三个非负有理权重且断言和为1。它验证三模型N一致、B与x打包一致，生成有理190seed，保留源hash。仅[1,0,0]生成器smoke成功，不据此冻结最终凸组合。

kernel.py复用seed1的有理T1、已认证33行/33列，在I384真实r*上解精确选中接触方程。全部45行的区间残差都必须包含0，作为一致性检查；精确全45方程依靠既有rank33与W兼容性定理，而不是“区间含0”单独推出。其余157坐标固定为有理混合seed。

PSD每个reducedB实际以向外I384 LDL验证，原A=Ntilde*T1*B*T1^T*Ntilde^T随之PSD。原A有强制零空间，不能从deltaA小或浮点eigenvalue正推断PSD。记录修正delta的精确区间；不把旧seed1的5.358e−12限额当所有新seed的先验。

jets.py对新证书重建原A，独立二阶AD；h必须为真实接触H27（contact_minorant_factor_v1.py定义），曲率使用contact_minorant_curvature_v1.json的严格界，不能用某个有理近似h27代替接触。九种内部Hessian PD、三种边界lambda>0和切向LagrangeHessian PD都须实际通过，不能仅凭seed1权重占比推断。

## 全域checker避开接触零点

不要期待统一正容差Bernstein直接覆盖R=0接触。先给12种类型的全排列构造严格局部邻域证书；余域再用有理化多项式+系数不确定性外向界做Bernstein递归。若某全域盒完全包含于已经证明的局部域，可作local-certified叶终止；相交而非包含不够。

内部九类：在接触cube的整个凸包证明三维Hessian正定。由真根接触精确R=0、gradR=0和Taylor积分得cube内R>=0。必须给全盒Hessian界，pointjet PD不是neighborhood证明。

边界三类在排序坐标下可取lower Gram root u=b(v,t)=vt−sqrt((1−v²)(1−t²))。Gram可行侧u>=b；在扩展盒证明R_u>0，在(v,t)矩形证明B(v,t)=R(b(v,t),v,t)的2×2 Hessian PD。真接触B*=0,gradB*=0即得boundary面B>=0，再由R_u>0得整Gram侧R>=0。无需强行证明全三维R−lambda*g Hessian PD。

导数公式：
 b_v=t+v*sqrt((1−t²)/(1−v²)),
 b_vv=sqrt(1−t²)/(1−v²)^(3/2),
 b_vt=1−vt/sqrt((1−v²)(1−t²)),
其余交换v,t。链式
 H_B,vv=R_uu*b_v²+2R_uv*b_v+R_vv+R_u*b_vv，
 H_B,vt=R_uu*b_v*b_t+R_ut*b_v+R_uv*b_t+R_vt+R_u*b_vt。

取v,t在接触±delta，u区间需覆盖接触u±delta与整个b(v,t)像；简单扩到3delta也须实际验证包含关系。所有平方根分母须以严格区间证明远离0。

局部可对真实代数多项式系数作1e−18等固定网格中点有理量化，同时明确累计Σ系数误差*monomial_bound（导数也要加相应次数因子）；以该显式误差扩展Bernstein grad/Hessian区间，避免大系数Horner消去。H27本身必须真实代数接触，量化仅作为区间评价辅助，不能改变目标函数使零点失去精确性。

远区盒：先Gram排除，再点积必要域与旧Rbudget排除，再局部域包含判定，再R的Bernstein下界。旧Rbeta应严格使用当前d10模型和pair056固定U；不能误用d4旧域或自行换更紧U。所有未处理盒必须归零，有限样本/DE正结果不替代全覆盖。

## 待权重后命令

 PYTHONPATH=proof_work/python_deps python3 proof_work/d10_sharpconvex_exact2026_make_seed.py --weights A B C --output proof_work/d10_sharpconvex_exact2026_seed.json
 PYTHONPATH=proof_work/python_deps python3 proof_work/d10_sharpconvex_exact2026_kernel.py --seed-input proof_work/d10_sharpconvex_exact2026_seed.json --output proof_work/d10_sharpconvex_exact2026_certificate.json
 PYTHONPATH=proof_work/python_deps python3 proof_work/d10_sharpconvex_exact2026_jets.py --certificate proof_work/d10_sharpconvex_exact2026_certificate.json --output proof_work/d10_sharpconvex_exact2026_jets.json

新核证书可独立重放：kernel.py --certificate NEWCERT --output NEWREPLAY（不用seed-input），重建并逐项比较LU、delta、solution和PSD。以上新文件不修改旧证书或父报告。

## 实际导出接口

_coefficients.json的R_coefficients和F_coefficients为[[[a,b,c],I.bounds()],...]，H_coefficients_ascending为真实HermiteH27的28个单项式系数I384包络，local_centers含按数值排序的12种接触点及真实root中心区间。它们是相关真实代数系数的外包络；不能把端点当真实多项式。

真正代数定义为：33选中接触方程确定33坐标，其余157坐标固定有理；NN=Ntilde(r*)T1定义A；h=H27(r*)；E*=候选真实能量；c=(E*+(3/2)F111)/12。常数目标严格等于E*，I384的E/c仅是该精确对象的包络。c按浮点数四舍五入会破坏sharp证明。

导出程序_export.py的export(cert,output,ctx=None)接受_kernel.run(...,return_context=True)返回上下文，避免重复构建接触系统。F多项式用精确Fraction Qk递推与I384 A相乘，再对六置换平均；h直接从contact_minorant_factor_v1.json真实Newton数据转换。当前导出807项R，9.12秒。

局部脚本_local.py先以有理dyadic中心作tensor binomial平移，然后在小盒以区间Horner评价导数，避免原坐标多项式的大系数消去。平移系数仍为严格区间，不改变真实多项式。内部Hessian与边界graphHessian均实际在完整盒计算，不能把pointjets通过误作邻域已证。

## 已完成：严格正宽度局部域

_local.json现已认证全部12类实际邻域，5.93秒。原cube半宽依次为：AAA .001，CBA .0001，CCA .001，AFF .001，GAF .0001，BFF .0001，GGB .0001，CFF .00001，CGF .00001，DDD .00001，DFF .0001，GDF .0001。labels按数值排序，域树也按u≤v≤t处理即可；对无排序树须将12类全部置换或先严格排序。

局部叶的有效终止域是rows.box中完整原cube与Gram可行域的交集。expanded_u仅作为边界证明时覆盖u到b(v,t)垂直路径的辅助盒，不能拿其替代box扩大local终止域。

内部证明：任意cube点与真实接触点的连线在cube内，R*=gradR*=0及全盒HessPD给Taylor积分R>=0。

边界证明：矩形(v,t)的每一点到真实接触(v*,t*)的连线在矩形内，精确value/tangent contact推出B*=gradB*=0；全矩形B的HessPD给B>=0。任意cube内Gram可行点满足u>=b(v,t)，且u到b的整条垂直线段在expanded_u×矩形内；Ru>0给R(u,v,t)>=B(v,t)>=0。b由lowerroot定义，分母与平方根严格远离0已由区间运算成功保证。

本轮没有任何远区全域遍历；全域最优性仍需父线程处理剩余必要域并最终pending=0。
