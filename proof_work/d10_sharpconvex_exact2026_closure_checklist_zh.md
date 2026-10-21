# 新十阶sharp证书的独立数学闭合核查

状态：本说明核对真实代数对象、接触兼容性、局部覆盖与计数恒等式。尚不声称远区全覆盖；只有远区严格完成且pending=0后，才适用末尾最优性结论。PSD、接触和局部状态不是全域状态。

## 1. 候选、驻点及固定能量上界

r*在certify_pair_moments.py的[L,Uroot]内；本节的Uroot与能量上界U_E不同。端点E_family'严格异号给存在性。对于0<r<1，

 E_family'=−2sqrt(3)/r²+(3/2)r/(1−r²)^(3/2)+6r/(4−r²)^(3/2)+6/(2−r)^(3/2)−6/(2+2r)^(3/2)。

各项导数之和严格正：4sqrt(3)/r³+(3/2)(1+2r²)/(1−r²)^(5/2)+6(4+2r²)/(4−r²)^(5/2)+9/(2−r)^(5/2)+18/(2+2r)^(5/2)>0。因此r*唯一。

候选六个prism点(r cos(2πj/3),r sin(2πj/3),±sqrt(1−r²))，三个caps(cos((2j+1)π/3),sin((2j+1)π/3),0)。点积按ABCDFG顺序为(1−3r²/2,2r²−1,r²/2−1,−1/2,r/2,−r)，无序重数(6,3,6,3,12,6)，和36。E*=Σ这些重数f(node)，f(t)=(2−2t)^(-1/2)。

固定U_E来自pair056_optimized_certificate.json['U']，严格等于Fraction('25.75998653126983156407570227376049402866')；I384候选能量上端<U_E。verify_pair056_saved.py重算有理LP及余量给任何E≤U_E构型的全部点积<14/25。紧性与碰撞能量无穷给全局极小构型Xmin存在，Emin≤E*<U_E，故其点积都在[−1,.56)。

## 2. 真实H27的minorant无需误差因子数值

取六个真实候选节点及八个有理补充节点−1,−9/10,−2/5,−1/5,1/10,9/20,13/25,14/25，共14个不同节点。H27是真正Hermite多项式，在全部14节点匹配f与f'。

对任何t∈[−1,14/25]，Hermite余项给

 f(t)−H27(t)=f^(28)(ξ)/28! * Π14j(t−s_j)²≥0，
 f^(28)(ξ)=55!!*(2−2ξ)^(-57/2)>0。

ξ位于t与插值节点凸包内，整个凸包小于1，故光滑性满足。t恰为节点时由接触等式得0。这个定性证明已足够保证minorant；contact_minorant_factor_v1的Stieltjes K数值上下界不是全局最优值闭合的必要前提，但其真实Newton系数必须与此Hermite定义一致。脚本导出的是这些真实系数的I384包络，并非某个有理h27近似。

## 3. 任意新seed与有理T1均适用的45行接触定理

令Gk(r)为九点候选的完整有序三点核矩阵和。candidate_low_rank_notes.md的锚点坐标直接有限求和证明

 Gk=6(1−r²)^(k mod2) p_hat p_hat^T+3 c c^T。

candidate_low_rank.py的features给精确Q(r)两行。其共同零空间Nk(r)满足GkNk=0。任意常数有理T1,k与任意对称reducedBk，Ak=Nk T1,k Bk T1,k^T Nk^T仍满足GkAk=0；不要求T1另外可逆。

45行由12种值条件、9种内部各3梯度、3种边界各2切向条件组成。190列是reduced对称B上三角自由坐标。W有10个对称关系、1个84三角重数加权值关系、1个沿候选r速度的切向/梯度关系。

记L_F=7F+Σ三边d+F111/8，其中d(t)=F(1,t,t)。值重数和S(r)=Σ84 L_F=(7/6)Σk<Ak,Gk>=0。对r求导时，系数变化项<Ak',Gk>也为0，因为Ak'=Nk'T1 B T1^T Nk^T+Nk T1 B T1^T Nk'^T，两项都包含GkNk=0。因此余下固定核系数的点坐标方向导数给第12关系。这覆盖全部190列和任意157个非零自由seed，绝非仅33列的检查。

d10_contact_left_geometry_v1.py精确验证W的12×12子式det=−36r非零，及Wb前11行恒0、最后=7E_family'(r)。所以r*处Wb=0。新generic核的I384 LU证明选中33×33子式非零，故rankM≥33；WM=0且rankW12给rankM≤33。因此ImM=kerW，33选中方程确定的解必满足全部45行。

精确解定义：157个坐标等于有理凸组合seed；其余33个由真实r*选中系统唯一解。T1是旧seed1证书保存的有理常数，新seed不改变Wupper证明。区间残差包含0只是实现一致性检查，不单独证明接触；真正全45成立依靠上述rank与兼容性。所有reducedBk的严格区间LDL给Bk>0，故Ak≥0。

## 4. 独立核对729项、能量常数与缺陷恒等式

F为完整三变量对称核。令S=Σi,j,k F(xi·xj,xi·xk,xj·xk)，d(t)=F(1,t,t)，F111=F(1,1,1)。按指标重数精确计数：

 S=6Σ84异点三角F+6Σ36无序点对d+9F111。

异点三角有6种排列；每个无序点对有6个恰两指标相等的有序三元组；全等9个。计数504+216+9=729。

真正代数常数c=(E*+(3/2)F111)/12=E*/12+F111/8。R=H(u)+H(v)+H(t)−7F(u,v,t)−d(u)−d(v)−d(t)−c。

每对边在7个异点三角出现，故

 (1/7)Σ84R=Σ36H−Σ84F−Σ36d−12c，
 S/6=Σ84F+Σ36d+(3/2)F111。

相加给Σ36H−E*，从而对任意九点构型恒有

 E−E*=Σ36(f−H)+(1/7)Σ84R+S/6。

由三点核PSD定理S=Σk<Ak,Gk(X)>≥0，对任意球面X成立，包含重复指标；R逐点验证只需异点三角。PSD定理不是F逐点非负。所有量的定义来自新seed新Ak和真H；不含旧25.745或25.7599205目标。

## 5. 局部认证的精确覆盖范围

_local.json每个rows.box是由真实中心包络端点向两侧扩大得到的完整outerbox；真中心在其中。内部全outerbox HessPD与精确R*=gradR*=0，通过连线Taylor积分给outerbox全域R≥0，不只对center±delta的某个内盒成立。

边界三类排序后处于Gram lowerroot u=b(v,t)=vt−sqrt((1−v²)(1−t²))。45contacts的两个切向等式在g_u≠0时等价于B(v,t)=R(b(v,t),v,t)的梯度零，且R*=0给B*=0。认证在完整(v,t)矩形证明HessB>0，故B≥0。expanded_u覆盖outerbox的u范围与b全像，且该扩展盒Ru>0；对每个Gram可行outerbox点，u≥b，沿整条垂直段积分得R(u,v,t)≥B(v,t)≥0。

只能将outerbox或其严格包含子域用作全域树local terminal。expanded_u是证明辅助域，不是更大的已认证终止cube。边界乘子lambda≥0的额外远区充分判据R−lambda*g≥0是sound，因为可行g≥0；其局部activation仅减少认证机会，不会遗漏可行点。

## 6. 远区完成后即得全局最小值，不要求唯一性

当前sharp_global_away2026_engine.py的ROOT_BOX为[−1,14/25]^3，无旧Rbudget或−.9957裁剪。因此若它在真实系数外包络上，以Gram排除/对称楔排除、已重放local域包含、Bernstein R≥0或R−lambda*g≥0等sound叶覆盖全树且pending=0，就已证明所有Gram可行异点三角R≥0。把第4节恒等式应用Xmin，三项非负推出Emin≥E*；候选本身能量E*给反向不等式，所以Emin=E*。

这个全Gram版本不依赖旧nonsharp下界和反足排除。如果后续改用受限域，必须另重放对应旧证书、beta固定U和全局极小构型必要性；不能将full版与restricted版前提混用。

此处证明候选达到最小值已足够。唯一性是附加命题，需要等号集合及Gram拼接分析，不能把它当最小值证明的必要缺口。

## 7. 有限复现依赖与验收清单

A. 基础算术及根/候选：dyadic_interval.py；certify_pair_moments.py（端点符号和能量）；certify_all_degree.py提供第二算术实现及相同root常数，不需要其所有阶LP障碍结论；candidate_triple_types_v1.json的84三角分类；candidate_low_rank.py及其坐标数学证明。

B. 上界域：pair056_optimized_certificate.json的固定有理U；verify_pair056_saved.py只用保存有理系数重做LP/minorant/exclusion。

C. 接触：d10_contact_left_geometry_v1.py/json（12左关系及右端）；d10_exact_contact_psd_seed1_v1.json只作为T1/33行列模板；新d10_sharpconvex_exact2026_seed.json保存190个有理新seed。原浮点发现包只是这些有理数的发现来源，不是exact-only重放依赖。

D. 真Hermite：contact_minorant_factor_v1.py/json（真实Newton节点/系数，case1零起始索引即第二case），重做Hermite递推与节点隔离。minorant由第2节解析Hermite余项证明；若用旧jets额外复核，还须contact_minorant_curvature_v1.py/json。local主证明直接用真实H多项式，不依赖曲率status作为证明。

E. 新kernel exact-only：d10_sharpconvex_exact2026_kernel.py --certificate NEWCERT --output FRESHREPLAY。重建解析N/T1、全部M、LU解、全部Bk LDL，并逐项比较保存证据，不读取浮点发现模型。证明全45依第3节数学W定理。

F. 新系数：d10_sharpconvex_exact2026_export.py --certificate FRESHREPLAY --output FRESHCOEF。从真实方程定义的核计算F/R和真实H27包络，检查root与bits对应。可向export(cert,output,ctx)传kernel(...,return_context=True)避免重复。

G. 新局部：d10_sharpconvex_exact2026_local.py --source FRESHCOEF --output FRESHLOCAL，或run(source_path,output_path,ctx=None)。逐盒重新评价导数和LDL，不能只读saved status。ctx若给，必须就是对应coef文件在同一构造链得到的dict。

H. 新远区：sharp_global_away2026_engine.py/check_away接FRESHCOEF的真实系数区间与FRESHLOCAL实际域，任意exact inscription必须包含于已证outerbox。输入poly保证真实对称性，所有系数量化误差显式外包络，所有树叶覆盖全root，pending必须0。当前run1仅是有限attempt适配器，标有local_proofs_replayed_here=False；独立wrapper须先完成E/F/G后再调用engine，不能把该False解释为已经独立证明local前提。

所有脚本禁用python -O/PYTHONOPTIMIZE，记录完整source与artifact SHA256。新local API变更前的源保存在d10_sharpconvex_exact2026_local_pre_api.py；已有local结果未修改，新API重放另存local_api_replay.json并记录implementation_sha256。运行输出用尚不存在的新路径。发现权重、PSD浮点特征值、DE样本最低值均不是上述验收证据。
