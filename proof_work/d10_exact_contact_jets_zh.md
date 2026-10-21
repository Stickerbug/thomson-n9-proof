# 精确十阶核的候选点二阶jets，以及严格负残差见证

## 本轮结论

对d10_exact_contact_psd_seed1_v1.json精确定义在真实驻点r*上的修正核：

- 九种内部候选三角的Hess Rf严格正定。
- 三种边界候选三角的法向乘子lambda严格为正，且切向Lagrangian Hessian严格正定。
- 将f换成精确根定义的H27 minorant，扣除各候选节点上(f−H27)''的已认证区间损失后，以上全部正定结论仍成立。
- 但同一精确修正核在下述Gram内部有理三角处残差严格为负。因此该核不能满足完整Gram域的全局非负要求。H27残差同样为负。

本轮没有做完整邻域认证，也没有排除其他核或给出Thomson九点构型反例。若使用额外竞争域，负见证是否属于该竞争域应另由其定义检查；这里严格认证的是Gram域内部及残差负性。

## 精确核与独立二阶计算

核由先前33阶接触方程精确定义，而不是取某个有理近似r。入口仅读证书有理Tk、190seed和行列选择，重新构造解析Nk、校正及PSD。新helper return_context返回其完整区间包络，原checker命令入口保持原有认证路径。

新程序重新构造原始矩阵

    Ak=Ntilde_k Bk Ntilde_kᵀ，

之后从原始矩阵及Qk递推独立计算F的二阶3变量forward AD。乘法规则为

    Hess(ab)=b Hess(a)+grad(a)grad(b)ᵀ
             +grad(b)grad(a)ᵀ+a Hess(b)。

通过精确整数多项式u²v+v³在(u,v)=(2,3)的值、两梯度、三个Hessian条目交叉检查AD规则，全部精确通过。
Qk及全部六个坐标排列都经同一AD计算。对d(t)=F(1,t,t)，使用

    d'=F_v+F_t，d''=F_vv+2F_vt+F_tt。

内部Hessian为

    Hess Rf = diag(f'')−7 Hess F−diag(d'')，
    f''(t)=3/(2−2t)^(5/2)。

每个3×3矩阵进行纯整数384位向外区间LDL检查，全部主元下界严格大于零。

## 边界条件与坐标排序

接触线性定理已证明边界切向梯度精确为0，因此grad R=lambda grad g；不以区间包含零替代等式证明。法向

    grad g=(2(vt−u),2(ut−v),2(uv−t))，

lambda以(gradR·gradg)/(gradg·gradg)区间计算。结果均有严格正下界；以下仅近似展示：

    BGG: lambda≈0.00140442539669，
    CFF: lambda≈0.000429029925115，
    DDD: lambda≈0.0000563282028923。

在candidate_triple_types的字母排序坐标下，使用的精确切向基是

    BGG: [[0,−4r],[1,1],[−1,1]]，
    CFF: [[0,2r],[1,1],[−1,1]]，
    DDD: [[1,1],[−1,1],[0,−2]]。

各列与精确Gram法向正交且列独立。BGG是原几何脚本点(−r,−r,B)切向基经相同坐标排列后的形式，不能直接复制而忽略排序。

分别计算并认证

    Tᵀ(Hess Rf−lambda Hess g)T >0。

## H27曲率损失

使用contact_minorant_curvature_v1.json中精确root-defined H27的六个曲率上界。其节点顺序为(C,G,D,B,A,F)，不是本程序的(A,B,C,D,F,G)。代码显式映射并检查节点区间重叠；曲率源生成脚本精确识别相应真实节点。
每个loss=(f−H27)''使用[0,saved_upper]区间，作

    Hess RH27=Hess Rf−diag(loss)。

梯度接触相同，故边界lambda不变。九个内部Hessian及三个切向Lagrangian Hessian在扣除该损失后仍全部通过严格区间LDL。

本结果依赖上述已认证曲率文件；没有使用旧有理近似h27或浮点Hermite数据。

## 同一个精确核的严格负残差点

有理坐标

    p=(−0.759220762336624,
       −0.29211600772137486,
        0.32931701954562287)。

程序用区间原始矩阵递推重做F(p)、每个d(p_i)、F111和真实候选能量，得到

    Gram(p)>0，约0.3758745842903281，
    −0.000007738 < Rf(p) < −0.000007737 <0。

粗十进制界是精确有理数，并用区间整数端点严格向外核对；JSON同时保存Rf与Gram的完整2^384分母整数端点。
由于H27≤f，在此点有RH27≤Rf<0，无需再计算H27多项式即可严格排除这个核在完整Gram域上的残差非负性。

此见证是三个点积变量构成的可行三角，否定这组辅助核的残差条件；它不是一个低于候选能量的九点构型。

## 重跑

    PYTHONPATH=proof_work/python_deps OPENBLAS_NUM_THREADS=1 python3 \
      proof_work/d10_exact_contact_jets_v1.py \
      --certificate proof_work/d10_exact_contact_psd_seed1_v1.json \
      --output proof_work/d10_exact_contact_jets_new_replay.json

输出名须尚不存在。完整证据为d10_exact_contact_jets_v1.json，独立进程复跑结果为d10_exact_contact_jets_replay.json。脚本保存全部内部Hessian、曲率扣除后的包络、边界lambda、切向矩阵及LDL主元，还保存负残差见证。

这些是候选点处的严格二阶jets，不在本文件提升为任何完整邻域或全局非负证明。
