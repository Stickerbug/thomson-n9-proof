# Thomson 九点问题：文献、严格证书与待外审的全局证明

> 最新状态：新核的零误差全域认证、真根接触/PSD、十二类局部证明及完整重放均已通过；接触兼容性与总能量恒等式审查已合并。证明链在本地闭合，但尚无外部同行评议或独立实现；Lean 工程已形式化候选几何、族能量恒等式、族能量导数与驻点存在唯一性、族内严格全局极小性、逐对路径导数、能量梯度逐对和及其内积形式、多点路径导数、梯度零点等价、一阶最优性条件与能量置换不变性、全局极小元存在性、能量泛函的等距不变性与内积表示、逐对能量界、候选能量严格极小、精确距离谱与物理域 Gram 约束的几何必然性、有序内积三元组的排序不变性、候选能量 < 26 的有理上界、能量齐次性与 f(t) 内积 rpow 形式、Bachoc–Vallentin 三点正性、三点恒等式、见证式 SOS 三点界、叶证书语义与覆盖组装、PSD 证书语义、区间算术与 Bernstein 系数证书语义、带符号乘非负区间的 `mulMixed`、Bernstein 基区间包络、三元乘积包络与有限和包络、冻结命题到全局下界的等价归约、区间严格单调性、严格凸性、能量连续性、等距不变性与内积表示及域受限覆盖逻辑，最终定理仍未形式化。完整论证见[证明候选稿](</home/dsh/Thomson Problem/proof_work/THOMSON_N9_PROOF_CANDIDATE_zh.md>)；下文第4—12节中的旧下界和失败核记录属于研究历史，第13节给出最终状态。

## 1. 当前结论

研究对象是经典 Coulomb Thomson 问题：在单位球面上选择九个点，最小化

\[
E(X)=\sum_{1\le i<j\le9}\frac1{\|x_i-x_j\|},\qquad x_i\in S^2.
\]

检索到的公开资料仍将九点严格全局问题列为未解；本次没有找到已发表且可核验的九点证明，也不能声称穷尽全体文献。随后本次研究构造了一个新三点PSD核，并在本地闭合了它的完整计算机辅助证明链，得到待外部复核的结论

\[
\boxed{E_{\min}(9)=E_D(r_*),\quad E_D(r_*)\approx25.75998653126983156407570227376049402864.}
\]

这是本次研究产物，尚无外部同行评议或独立实现；Lean 已检查候选几何、九点互异、族能量恒等式、族能量一阶/二阶导数、驻点存在唯一性与族内严格全局极小性、逐对路径导数、能量梯度逐对和及其内积形式、多点路径导数、梯度零点等价、一阶最优性条件与能量置换不变性、全局极小元存在性、区间严格单调性、严格凸性、能量连续性、能量泛函的等距不变性与内积表示、逐对能量界、候选能量严格极小、精确距离谱与物理域 Gram 约束的几何必然性、有序内积三元组的排序不变性、候选能量 < 26 的有理上界、能量齐次性与 f(t) 内积 rpow 形式、Bachoc–Vallentin 三点正性、三点恒等式、见证式 SOS 三点界、叶证书语义与覆盖组装、PSD 证书语义、区间算术与 Bernstein 系数证书语义、带符号乘非负区间的 `mulMixed`、Bernstein 基区间包络、三元乘积包络与有限和包络、冻结命题到全局下界的等价归约、以及域受限覆盖逻辑，但最终定理未形式化，也不能写成学界已公认解决。新核的真根接触修正、严格PSD和十二类局部盒全部重算通过；96位完整根域认证δ=0，136125节点、pending=0；从原始有理seed开始的第二次完整重放一致。接触几何与总能量恒等式亦经精确审查。详见[完整证明稿](</home/dsh/Thomson Problem/proof_work/THOMSON_N9_PROOF_CANDIDATE_zh.md>)和第13节。

| 问题 | 本次最终结果 |
|---|---|
| D3h 一参数族内唯一最优 | 已由严格凸性证明 |
| 候选在完整构型空间内严格局部最优 | 已有区间 Hessian 证书，模去旋转后成立 |
| 候选的全局最小能量 | 本地计算机辅助证明链已闭合，待外审 |
| 达到候选能量的新核与十二类三点邻域 | 真根PSD、全部局部盒和全域非负性均通过 |
| 最优构型的全局唯一性 | 未证明 |
| 更低能量九点反例 | 未发现 |
| 旧固定核和旧三种权重凸包 | 存在严格负残差，已弃用；不否定新核或候选 |
| 任意阶标准两点 LP 达到或任意逼近候选能量 | 已排除，见第5节；本次成功使用三点核 |

## 2. 文献状态与阅读路线

### 2.1 必须区分的问题

本文仅讨论单位 S² 上的势 1/r。Riesz 一般 s、对数势、Tammes 最大最小距离、RP² 上的直线排列，均不能直接替代这个问题。数值极小点、Hessian 正定、有限精度全局下界与精确全局最优性，也是不同层次的结论。

### 2.2 与本问题直接相关的资料

1. [MathWorld: Thomson Problem](https://mathworld.wolfram.com/ThomsonProblem.html)。已读取条目，明确写九点仍 unknown。其页脚日期是网站日期，不能用来断言该条目的具体修订日期；小 n 已解列表也应与原论文交叉核查。
2. Richard E. Schwartz, [The 5 Electron Case of Thomson's Problem](https://arxiv.org/abs/1001.3702), *Experimental Mathematics* 22(2), 157–186 (2013), [DOI](https://doi.org/10.1080/10586458.2013.766570)。五点严格计算机辅助证明，是几何域排除与局部分析结合的参考，不能直接推广为九点定理。
3. Henry Cohn and Abhinav Kumar, [Universally optimal distribution of points on spheres](https://arxiv.org/abs/math/0607446), *JAMS* 20, 99–148 (2007), [DOI](https://doi.org/10.1090/S0894-0347-06-00546-7)。解释普适最优和两点正定多项式方法；九点候选不自动属于其 sharp 构型定理。
4. Henry Cohn and Jeechul Woo, [Three-point bounds for energy minimization](https://arxiv.org/abs/1103.0485), *JAMS* 25, 929–958 (2012), [DOI](https://doi.org/10.1090/S0894-0347-2012-00737-1)。三点半正定核的关键来源。文中涉及 RP² 的七直线结论不能当成 S² 上七电荷结论。
5. David de Laat, [Moment methods in energy minimization: New bounds for Riesz minimal energy problems](https://arxiv.org/abs/1610.04905), *Transactions AMS* (2019), [DOI](https://doi.org/10.1090/tran/7976)。提供收敛的矩方法层级及四点界；其五点数值 sharp 实验不等于九点严格证明。
6. Jianyuan Yin, Zhen Huang and Lei Zhang, [Constrained high-index saddle dynamics for the solution landscape with equality constraints](https://arxiv.org/abs/2011.13173), *J. Sci. Comput.* 91, 62 (2022), [DOI](https://doi.org/10.1007/s10915-022-01838-3)。包含 Thomson 能量景观数值研究，可帮助发现竞争临界构型；不提供九点全部构型的严格穷尽。
7. Paolo Amore et al., [Exploring the energy landscape of the Thomson problem: local minima and stationary states](https://arxiv.org/abs/2506.08398) (2025)。局部极小数值研究至 N=150，驻点景观研究至 N≤24；摘要明确是 numerical investigation。
8. Liudmyla Kryvonos, Lukas Liehr and Mitchell A. Taylor, [Energy minimization for eight points on the sphere](https://arxiv.org/abs/2609.22077) (18 Sep 2026)。已读取摘要与正文；作者声称严格证明八点 Coulomb/对数最优方反棱柱，并由 Lean 验证。其[代码库](https://github.com/lukasliehr/Energy-Minimization-8-Points)含证书。本文未自行编译 Lean；八点结论不解决九点，也不能仅把程序中的 N 改成 9。
9. *A deterministic global optimization algorithm for the Thomson and Tammes problems*, [DOI 10.1016/j.dam.2026.05.015](https://doi.org/10.1016/j.dam.2026.05.015)。已定位题名和书目信息，但原站全文访问受限；本次不能根据二手摘要把它认作九点严格求解。
10. [七点 Lean 项目](https://github.com/huwngtran/thomson-n7-lean) 的自述包含 “Statement not human-certified. Not peer reviewed.”。新闻报道、项目 README 和经审阅定理应分别看待。

历史入口还包括 Melnyk–Knop–Smith, *Extremal Arrangements of Points and Unit Charges on a Sphere: Equilibrium Configurations Revisited*, *Canadian Journal of Chemistry* 55, 1745–1761 (1977)，以及 MathWorld 列出的 constrained global optimization 文献。上述为本次关键文献地图，不声称收集或读完所有有关球面能量的论文。

## 3. 候选构型及已证明的局部部分

设 r∈(0,1)，h=√(1−r²)。六个棱柱顶点及三个帽点为

\[
x_k^\pm=(r\cos(2\pi k/3),r\sin(2\pi k/3),\pm h),\quad
c_k=(\cos((2k+1)\pi/3),\sin((2k+1)\pi/3),0),\quad k=0,1,2.
\]

其 36 对能量恰好化为

\[
E(r)=\sqrt3+\frac{2\sqrt3}{r}+\frac3{2\sqrt{1-r^2}}+
\frac6{\sqrt{4-r^2}}+\frac{12}{\sqrt{2-r}}+\frac6{\sqrt{2+2r}}.
\]

每项二阶导数非负且总和严格正，两端能量发散，所以族内唯一驻点就是族内唯一极小点；这一推断已由 `Minimum.lean` 的 `exists_unique_familyEnergy_min`（E' 严格单调 + 中值定理）在 Lean 中形式化；`familyEnergy_strictAntiOn_Ioo` 与 `familyEnergy_strictMonoOn_Ioo` 进一步给出区间形式：能量在 `(0,r_*)` 上严格递减、在 `(r_*,1)` 上严格递增。精确区间运算得到

\[
r_*\approx0.71054833409295381132780417927279124376803,
\]

\[
25.75998653126983156407570227376049402863
<E_*<25.75998653126983156407570227376049402866.
\]

完整九点空间在模去三维旋转后有 15 个自由度；只检查 E''(r)>0 不足以证明局部最优。另有完整图册 Hessian 的区间 LDL 证书，验证指定旋转切片坐标立方体 |z_a|≤10⁻⁴ 内严格凸。这里的 10⁻⁴ 是该图册坐标的半宽，不应解释成任意距离下的球半径；LDL 枢轴下界也不是最小特征值下界。

证明细节见[局部证书说明](</home/dsh/Thomson Problem/proof_work/local_certificate_notes.md>)，扩大的验证程序为[预条件局部检查器](</home/dsh/Thomson Problem/proof_work/certify_local_preconditioned.py>)。

## 4. 最新全局下界为什么是无条件的

令 f(t)=(2−2t)⁻¹ᐟ²。先前独立的有理两点证书证明：凡 E≤U 的九点构型，任意异点内积都小于 14/25，其中 U 是上述候选能量上端。证书由[保存系数检查器](</home/dsh/Thomson Problem/proof_work/verify_pair056_saved.py>)重新验证，详见[竞争点对排除证明](</home/dsh/Thomson Problem/proof_work/competitive_pair056_proof_zh.md>)。

在 [-1,14/25] 上选有理 27 次多项式 h，严格认证 0≤f−h<10⁻¹¹。定义

\[
Q_0=1,\quad Q_1=t-uv,\quad Q_{k+1}=2(t-uv)Q_k-(1-u^2)(1-v^2)Q_{k-1}.
\]

S_{k,ij} 是 u^i v^j Q_k 的六种坐标排列平均，F=Σ_k⟨A_k,S_k⟩，11 块有理 A_k 均严格正定。固定锚点后，用横向复数坐标可写 Q_k=Re((ζ_y conjugate(ζ_z))^k)，因此全部有序三元组上的核和非负：Σ_all F≥0。

令 d(t)=F(1,t,t)，并定义

\[
R(u,v,t)=h(u)+h(v)+h(t)-7F(u,v,t)-d(u)-d(v)-d(t)-c,
\quad B=12c-\tfrac32F(1,1,1).
\]

对任意九点构型有精确恒等式

\[
E-B=\sum_{36\text{ pairs}}(f-h)+\frac17\sum_{84\text{ unordered triples}}R+
\frac16\sum_{729\text{ ordered triples}}F.
\]

若三个互内积可实现，则 g=1+2uvt−u²−v²−t²≥0。对整个 Gram 域与 [-1,14/25]³ 的交，使用向外舍入整数 Bernstein 张量证明 R≥0，即得 E≥B。

最新模型的 B=515199/20000=25.75995。它把原有理核与首个PSD接触核按1/2凸组合；接触核只作有理量化及10⁻¹¹I抬升，各块精确LDL通过，再统一使用h27并按目标B重建c、F、R。完整根盒搜索处理47397个节点：11592个正叶、12091个Gram/排序排除叶、0个待处理盒，最大总深度40，48位向外整数舍入，78.96秒。完整树满足11592+12091=(47397+1)/2；模型SHA256为84332b9cb33759ab9fcefec9648452c5e73125998a2fc8b0a4046e3a42b19d1f。

原模型B₀=51519841/2000000=25.7599205的202923节点完整证书仍保留。后文固定三角、预算及必要域继续使用这个旧模型的R₀，不能只把其中B₀替换为25.75995而不更换残差。

若 E>U，则自动 E>B；若 E≤U，则竞争点对证书保证此域适用。因此最终下界适用于所有九点构型，而不限于预先假定的 D3h、无反极点或某些数值样本。

主要复算文件：

- [最新有理凸组合模型](</home/dsh/Thomson Problem/proof_work/d10_convexmix2026_proposal.json>)及[完整闭合报告](</home/dsh/Thomson Problem/proof_work/d10_convexmix2026_proposal_result.json>)。
- [旧预算模型](</home/dsh/Thomson Problem/proof_work/nonsharp_d10_root25_7599205_v10.json>)及[旧闭合报告](</home/dsh/Thomson Problem/proof_work/nonsharp_d10_root25_7599205_v10_result.json>)，仍用于后文R₀。
- [根域精确检查器](</home/dsh/Thomson Problem/proof_work/verify_high_degree_conditional.py>)。
- [精确张量转换](</home/dsh/Thomson Problem/proof_work/exact_tensor_bernstein.py>)。
- [h27 保存系数证书](</home/dsh/Thomson Problem/proof_work/conditional_h27_certificate.json>)。

从项目根目录复算（检查器避免覆盖既有报告，所以复制一个新名字）：

```bash
replay_model=$(mktemp proof_work/replay_XXXXXX.json)
cp proof_work/d10_convexmix2026_proposal.json "$replay_model"
PYTHONPATH=proof_work:proof_work/python_deps OPENBLAS_NUM_THREADS=1 python3 proof_work/verify_high_degree_conditional.py "$replay_model" --budget 300000 --seconds 180 --max-axis-depth 80 --axis-strategy adaptive --bits 48
```

不能使用python -O，入口明确拒绝禁用断言。精确代数、PSD、归一化及覆盖判断不信任浮点求解器。本线程从完整根域检查了新凸组合模型的47397节点树；这尚不是外部独立实现的复核。较早审查者对旧模型重算了哈希、66个精确LDL枢轴、全部F/R系数、归一化及根张量范围，静态检查双子覆盖和整数溢出保护；他没有独立重复旧202923节点整树。更早25.7598模型已有70位任意精度整数实现复核。相关实现共享部分辅助代码，不称完全独立验证。

## 5. 标准两点 LP 存在统一正缺口

对候选构型，六种内积及其无序对重数为

\[
(1-3r_*^2/2,-1/2,2r_*^2-1,r_*^2/2-1,r_*/2,-r_*),
\quad(6,3,3,6,12,6).
\]

M_l=Σ_{i,j}P_l(x_i·x_j) 满足 M_1=0，而所有 l≥2 的 M_l>m=1/1000。l=2,…,229 用精确区间递推验证；l≥230 用 |t|<3/4 和

\[
|P_l(t)|<\sqrt{176/(49l)},\qquad
M_l\ge9-72\sqrt{176/(49l)}>1/1000
\]

给出统一尾界。

设任意有限阶标准 Legendre LP 多项式 p=Σa_lP_l≤f，a_l≥0(l≥1)，B=(81a_0−9p(1))/2，G=E_*−B。记 q=Σ_{l≥2}a_lP_l，A=Σ_{l≥2}a_l，则 |q|≤A，G≥mA/2。

取候选中重数 6 和 12 的两内积 a=r_*²/2−1、b=r_*/2，δ_a=f(a)−p(a)≥0，δ_b=f(b)−p(b)≥0，则 G≥6(δ_a+δ_b)。中点的 p≤f 给出

\[
D:=\frac{f(a)+f(b)}2-f\!\left(\frac{a+b}2\right)
\le\frac{\delta_a+\delta_b}2+\frac{q(a)+q(b)}2-q\!\left(\frac{a+b}2\right)
\le G/12+2A\le G(1/12+4/m).
\]

精确区间证明 D/(1/12+4/m)>10⁻⁵（显示值约 1.530710873×10⁻⁵）。因此对所有阶数统一地有

\[
\boxed{B<E_*-10^{-5}.}
\]

这比“每个有限阶都不能恰好取等号”更强：这些有限阶界的上确界也不能逼近 E_*。同理适用于满足绝对一致收敛及同一缺陷恒等式的 Legendre 展开。不涉及三点/四点界、额外条件约束的两点方法或一般全局优化。

精确复算见[统一缺口检查器](</home/dsh/Thomson Problem/proof_work/uniform_pair_lp_gap_v1.py>)与[有理区间结果](</home/dsh/Thomson Problem/proof_work/uniform_pair_lp_gap_v1_certificate.json>)。全阶尾界的原始推导见[全阶障碍说明](</home/dsh/Thomson Problem/proof_work/all_degree_obstruction.md>)。

## 6. 已证伪一个更高目标的证书

同一旧核在目标 25.759925 时，取精确有理点

\[
(u,v,t)=(-296937/1000000,84507/200000,84507/200000).
\]

它在竞争盒内，且 g=8974579606349087/20000000000000000>0。但 R≈−3.4392570492699536×10⁻⁷<0。审计符号重建全部 807 项 R，又以独立标量 Q 递推、六排列平均和 Horner 求值精确交叉检查。

因此该固定核不可能认证 25.759925；单纯加深细分或提高精度无法修复。固定 A/h 只调 c 时，其目标必要上限约为 25.75992087289154。这个上限不是全域下界，也不是九点候选反例；上述三点未被证明能扩展成能量更低的九点构型。

见[负残差审计脚本](</home/dsh/Thomson Problem/proof_work/audit_d10_root25_759925_negative_witness.py>)和[完整有理结果](</home/dsh/Thomson Problem/proof_work/audit_d10_root25_759925_negative_witness.json>)。旧的 25.759925、25.75993、25.75995 深度/时间受限尝试均不计为证书。前沿盒中心为正也不能说明覆盖盒为正；已纠正过未转换归一化坐标的中心诊断。未闭合的前沿不携带完整覆盖树，禁止将其直接恢复后宣称全根域通过。

## 7. 其他严格几何信息及后续缺口

凡 E≤U，已有证书还给出 −0.999998<x_i·x_j<0.56。下侧来自固定反极点对时 E≥25.78，再用移动近反极点的能量误差 70/4041 排除邻域。见[反极点排除说明](</home/dsh/Thomson Problem/proof_work/antipodal_anchor_notes_zh.md>)。另外[竞争三角必要条件](</home/dsh/Thomson Problem/proof_work/competitive_triple_constraint_certificate.json>)排除了三个互内积均≥1/2 的点。这两条不是第 4 节最新下界的额外依赖。

进一步对全局极小构型，可利用驻点条件得到更强的点对下界：x_i·x_j>−9957/10000=−0.9957。新锚定证书认证：含反足点对、其余7点轴向坐标在[−0.63,0.63]、其余点对内积≤0.57的构型，E≥25.80。48位完整根域检查159节点无未决盒；70位任意精度整数、无对称剪枝复跑219节点无未决盒，两者共享底层多项式/Bernstein函数，不能称完全独立实现。

证明排除近反足对时，同时把两点沿大圆各移动θ/2使之成为反足；在原驻点处，该联合路径的能量一阶导数为0。若原内积≤−0.9957，则θ<93/1000；其他点距离沿路径始终>1783/2000。令H(d)=2/d³−1/(4d)，联合路径二阶导数上界为M=(7/2)H(1783/2000)+1/4，因此能量增量≤M(93/1000)²/2≈0.039560459033。移动后的轴向内积绝对值<0.6065，符合新反足证书；由此原能量≥25.80−增量>U，矛盾。这是全局极小构型、以及E≤U的光滑驻点的必要条件，不能套用于任意非驻定竞争构型。见[扩大轴向域的反足验证器](</home/dsh/Thomson Problem/proof_work/antipodal_anchor2580_2026_wide063_verify.py>)、[70位无对称复跑](</home/dsh/Thomson Problem/proof_work/antipodal_anchor2580_2026_wide063_object_replay.json>)及[双点变分有理常数检查](</home/dsh/Thomson Problem/proof_work/antipodal_anchor2580_2026_symmetric9957_check.py>)。该新区域约束尚不构成九点全局最优性证明，也没有改变能量夹逼。完整双点变分推导见[反足证书与驻点排除证明](</home/dsh/Thomson Problem/proof_work/antipodal_anchor2580_2026_notes_zh.md>)。

在加入−0.9957点对下界和旧三角预算后，对冻结的十二阶最终核另作17.81秒诊断，仍找到负残差：p=(−0.9391148010394065,−0.6773164129765319,0.38329155180117336)，80位原A复算R≈−0.0009287113972。该指定点的Gram、点对范围和旧预算条件都经Fraction核对；它仍只是辅助证书失败的证据，未证明能扩展为驻定九点构型，也不是Thomson反例。见[缩小极小构型必要域后的诊断](</home/dsh/Thomson Problem/proof_work/d12_minimizer_domain2026_results.json>)。

续接十二阶求解加入924个确定性网格cut，永久保留集合共1056点，active4500，并预计算消元后的Dred/bred。该次后台任务先返回running，随后工具注册表返回unknown job，日志停留于BUILD，保存history为空；没有退出码，不能判定数学失败、完成或进程已结束。已停止重复启动，以免重复计算。详见[运行状态证据](</home/dsh/Thomson Problem/proof_work/d12_contact2026_batch2_runtime_observation.json>)和[源码与依赖快照](</home/dsh/Thomson Problem/proof_work/d12_contact2026_batch2_provenance.json>)。

另一次独立命名的受限域试验已正常完成，不能与上述状态不明的任务混淆。新试验明确使用当前807项旧残差、B=25.7599205、β=7(U−B)，只保留点积在[−0.9957,0.56]、Gram≥0、R_old≤β的训练及搜索点。三轮纯minτ均报告optimal，训练τ约10⁻¹⁷，但trace约756、1189、1134，搜索仍找到负残差约−0.1451、−0.005643、−0.006546。每轮575个指定点由原始A递推复核；最终负点(−0.9956998397982685,−0.0025253139791771534,−0.0025239243541001852)的全部严格域条件由Fraction核验，旧预算裕量仍>3.47×10⁻¹⁰。残差值本身属于数值模型，未宣称精确负证书。这说明有限训练误差为零不足以保证全域非负，不能据此断言方法不可行。详见[受限域三轮报告与整块Bernstein约束设计](</home/dsh/Thomson Problem/proof_work/d12_restricted2026_report_zh.md>)、[逐轮模型](</home/dsh/Thomson Problem/proof_work/d12_restricted2026_results.json>)及[指定点精确域检查](</home/dsh/Thomson Problem/proof_work/d12_restricted2026_strict_negative_points.json>)。

等号核还必须满足正确的 Gram 边界条件。若边界接触处 R=0，则 ∇R=λ∇g、λ≥0，且在切空间 T 上 Tᵀ(∇²R−λ∇²g)T 半正定；直接要求 Tᵀ∇²R T 半正定是过强条件。三种候选边界三角的法向、切向基及曲率已在符号 r 下逐项验证，见[边界恒等式检查器](</home/dsh/Thomson Problem/proof_work/boundary_sharp_geometry_v1.py>)与[符号结果](</home/dsh/Thomson Problem/proof_work/boundary_sharp_geometry_v1.json>)。这些是必要条件，不足以证明残差全域非负。

候选的 84 个无序三角已在符号 r 下枚举为 12 类，重数相加为 84；其中恰有 3 类恒处 Gram 边界，其余 9 类在真实 r_* 的区间内严格处于内部。见[三角分类程序](</home/dsh/Thomson Problem/proof_work/candidate_triple_types_v1.py>)及[精确分类表](</home/dsh/Thomson Problem/proof_work/candidate_triple_types_v1.json>)。

等号证书所需的势函数插值也已有严格构造：27 次 Hermite 多项式 H 在全部六个真实候选内积处匹配 f、f'，在整个竞争区间满足 0≤f−H<1.5×10⁻⁹。其代数系数保存为严格区间，不能把区间端点当作精确系数。证明利用 f−H=ωK，其中 ω=∏(t−t_j)²、K 是正且递增的 Stieltjes 积分因子。节点上的二阶导数损失上界最大约 1.36×10⁻⁹。详见[接触插值证明](</home/dsh/Thomson Problem/proof_work/contact_minorant_factor_notes_zh.md>)、[区间构造与误差检查器](</home/dsh/Thomson Problem/proof_work/contact_minorant_factor_v1.py>)和[节点曲率检查器](</home/dsh/Thomson Problem/proof_work/contact_minorant_curvature_v1.py>)。这部分没有证明任何新的残差核全域非负，也不改变第 1 节的能量夹逼。

另已完成一个精确线性存在性结果：对真实驻点 r_*，当前十阶对称三点核的 45×190 接触、内部梯度及边界切向线性系统秩恰为 33，因此存在实解，全部解形成 157 维仿射空间。证明结合全部 k≤10 候选矩阵在 Q[r] 中的精确重建、12 个独立左关系、根区间上 33 阶非零子式，以及 E'(r_*)=0 导出的右端兼容性。详见[严格接触可解性证明](</home/dsh/Thomson Problem/proof_work/STRICT_CONTACT_SOLVABILITY_zh.md>)及[区间子式检查器](</home/dsh/Thomson Problem/proof_work/d10_root_minor_interval_v1.py>)。

在此基础上，已对第一组数值 PSD seed 做真正驻点上的精确接触校正：固定 157 个有理参数，定义其余 33 个参数为所选接触方程的精确解，并严格认证 max|Δ_i|<5.358×10⁻¹²。十个非空 reduced B 块的全部区间 LDL 枢轴为正，因此所有原始 A_k=Ñ_k B_k Ñ_kᵀ 半正定。母线程已分别复跑发现模式和仅读取已保存有理证书的 exact-only 模式，均 exit0，后者不运行 QR、最小二乘或读取原数值模型。见[精确接触及 PSD 构造](</home/dsh/Thomson Problem/proof_work/d10_exact_contact_psd_seed1_zh.md>)和[检查器](</home/dsh/Thomson Problem/proof_work/d10_exact_contact_psd_seed1_v1.py>)。对这个精确校正核，又已逐类认证候选 12 种三角处的二阶条件：9 种内部三角的 Hessian 严格正定；3 种 Gram 边界三角的法向乘子 λ>0，切向 Lagrangian Hessian 严格正定。扣除接触 H27 的已认证曲率损失后仍全部成立。母线程复跑全部检查 exit0。这只认证各接触点上的二阶条件，没有给出核残差在完整邻域内的定量非负证书。见[二阶条件与负残差说明](</home/dsh/Thomson Problem/proof_work/d10_exact_contact_jets_zh.md>)和[复核程序](</home/dsh/Thomson Problem/proof_work/d10_exact_contact_jets_v1.py>)。

同一检查器还严格证明：在有理三角 p=(-0.759220762336624,-0.29211600772137486,0.32931701954562287) 处 Gram 行列式为正，但 −7.738×10⁻⁶<R_f(p)<−7.737×10⁻⁶。由于 H27≤f，相应 R_H27 也为负。这已经证伪该精确接触 PSD 核在全部 Gram 域的残差非负性；仅否定此核，不是九电荷反例，也不排除其它核。接触、PSD 与候选点二阶条件不足以闭合全局证明，不提高第 1 节的全局下界。

已开始十二阶接触核的新检验，并完成其严格代数准备：全部k=0,…,12的候选矩阵在QQ[r]中独立重建，验证G_k=6(1−r²)^(k mod2)p_kp_kᵀ+3c_kc_kᵀ；各零空间基的消去恒等式及非零主元均通过真实根区间认证，故是完整基。零空间维数为11,11,9,9,7,7,5,5,3,3,1,1,0，对称参数共有322个。十阶核补零嵌入十二阶且保留全部接触函数；结合12条几何左关系，十二阶接触算子秩仍恰为33，真实根处线性系统有解，仿射解空间维数289。随后完成三轮数值搜索，全部返回tau=0、近似接触误差≤1.2×10⁻¹⁴；trace依次5.65818、7.46652、7.80117，reduced B的最小数值特征值约10⁻⁷。但各轮搜索均发现负残差，依次约−0.0305846、−0.0137151、−0.00477172。最后负点向Gram区域内部移动后仍为R≈−0.00477148、Gram≈2.02×10⁻⁶；原始A递推与compiled值相差≤8.1×10⁻¹⁵，另一直接design计算相差≤9.6×10⁻¹⁶。搜索共享compiled实现，原A复算属于相对独立的点值检查，不是完全独立搜索。尚未认证新的精确PSD seed或残差全域非负，没有提高全球下界，也不是Thomson反例。竞争域诊断已完成：三轮报告的full-domain最坏点都被旧残差预算R_old≤7(U−B)精确排除；旧T1/T2/T3谷中心在最终新核上也均为正。但在该预算域内仍发现近反足负点(−0.9994670105438834,−0.03345627511650647,0.0021510521154539664)，80位原始A递推给R_new≈−0.001183594018，Gram和旧预算裕量均由Fraction精确证为正。该点只是辅助核障碍，不是九点反例；尚未纳入后来可能证明的“仅全局极小构型”的驻点排除条件。见[竞争域诊断说明](</home/dsh/Thomson Problem/proof_work/d12_competitive_probe2026_note_zh.md>)及[精确域条件和80位复核](</home/dsh/Thomson Problem/proof_work/d12_competitive_probe2026_verified_points.json>)。见[数值实验报告](</home/dsh/Thomson Problem/proof_work/d12_contact2026_report_zh.md>)及[全部三轮原始矩阵与数值记录](</home/dsh/Thomson Problem/proof_work/d12_contact2026_results.json>)。见[精确验证程序](</home/dsh/Thomson Problem/proof_work/d12_candidate_kernel_exact2026.py>)、[完整分块证书](</home/dsh/Thomson Problem/proof_work/d12_candidate_kernel_exact2026.json>)和[接触秩证明](</home/dsh/Thomson Problem/proof_work/d12_candidate_kernel_exact2026_zh.md>)。

完整证明尚需至少一种新结构：

1. 找到在真实 r_* 处满足等号、全 Gram 域非负的三点或更高点核，精确验证并从等号恢复 D3h 几何。以有限小数半径构造的“精确有理接触”只是数值探索条件，不能替代真实 r_* 的代数条件。
2. 证明任何 E≤E_* 构型都落入现有局部凸性证书的旋转切片邻域。能量夹逼本身不推出这个结论，必须建立全局几何稳定性或完成其余 15 维构型域排除。
3. 使用四点矩层级或带九点整体可扩展性约束的方法，排除三点松弛产生的伪竞争三角。
4. 若搜索发现 E<E_* 的九点，须将坐标有理化或立体投影有理化，并以向外区间给出反例能量上界严格低于候选下界；随机搜索和单个残差负点均不足够。

## 8. 固定坏三角的外点延拓：双球帽严格排除

设旧有理核的残差为 R，B=25.7599205，U 为候选能量严格上界。对任意 E≤U 的竞争构型，缺陷恒等式给出所有 84 个无序三角残差之和 ≤7(U−B)。固定其中一个三角 T=(a,b,c)，令

    φ(q)=R(a·b,a·q,b·q)+R(a·c,a·q,c·q)+R(b·c,b·q,c·q)。

T 自身与六个外点贡献的 18 项互不重叠，其余三角残差非负，所以必要条件是

    R(T)+Σ_{j=1}^6 φ(q_j) ≤ 7(U−B)。

外点还必须满足全部锚点内积及彼此内积 <14/25。此处使用已经全域认证的旧核 R，不对新接触核假定残差非负。

在第 7 节负残差见证对应的固定 T 上，旧核 R(T)≈2.10252384315792×10⁻⁵，六外点预算约0.0004411939703893693。正确单位 Cholesky 锚点下，分别优化一个或两个外点可以找到低于对应平均预算的可行数值点，因此这些松弛没有给出排除证据。早期错误锚点的数值结果已废弃，见[纠正记录](</home/dsh/Thomson Problem/proof_work/fixed_first_triangle_q_corrected_archive_v1.json>)及[双外点记录](</home/dsh/Thomson Problem/proof_work/fixed_first_triangle_twoq_spacing_probe_v1.json>)。

同时约束六外点的 12 维数值探索（5 个起点，约38秒）找到最佳可行 Σφ≈0.0005563971829045636，高于预算约0.00011511653；两个起点收敛至同一值，最大约束违例为0。详见[六外点探索记录](</home/dsh/Thomson Problem/proof_work/fixed_first_triangle_sixq_spacing_probe_v1.json>)。该可行值是最小值的数值上界，不是严格下界，不能据此宣称 T 已被排除。即使固定 T 排除成功，也还须覆盖其邻域和其它竞争区域。

随后已完成固定 T 的严格排除。取两个闭球帽 H_j={q:p_j·q≥89/100}，其中

    p_1=(9999999/10000000)(.3213589784,.5134140431,−.7956974471),
    p_2=(9999999/10000000)(.3181271408,−.7606356584,−.5670950993)。

所有小数均按精确有理数解释。已以 Fraction 验证 ‖p_j‖²<1，故同帽两点内积至少 2(89/100)²/‖p_j‖²−1>0.56。已有两点排除意味着每帽至多容纳一个外点；两帽并集至多容纳两个，不要求帽不相交。

使用两个有理球面图册 q=(2x,2y,±(1−x²−y²))/(1+x²+y²)，每图完整检查 [-1,1]²，严格认证全部允许位置的 φ≥3/100000，以及两帽并集外 φ≥1/10000。真正代数锚点以 128 位 dyadic 坐标近似；独立整数平方根证明每坐标误差<2⁻¹²⁸，再由残差系数导数和给出 φ 误差<6.244×10⁻³³。认证阈值额外加了 10⁻²⁵，因此包含这项误差。多项式齐次化、精确 Bernstein 根系数和整数向外细分覆盖全部图册；第一图71节点、第二图79节点，待处理均为0。母线程已从根域独立重跑同一检查器通过；共享算术依赖意味着这不是完全独立实现。

因此六点满足 Σφ≥2×0.00003+4×0.0001=0.00046。而模型与全局报告哈希绑定的精确有理预算 K=7(U−B)−R(T)≈0.0004411939703893693，严格差值约1.880634961×10⁻⁵。两者矛盾，故第7节所列固定三角不能扩展成任何 E≤U 的九点构型。这排除了一个接触核的负残差见证，不代表该接触核已在所有竞争三角上成立，也不提高第1节的全局下界。

复算资料：[双帽检查器](</home/dsh/Thomson Problem/proof_work/verify_fixed_triangle_two_caps_v1.py>)、[母线程完整根域重放](</home/dsh/Thomson Problem/proof_work/fixed_triangle_two_caps_parent_replay_v1.json>)、[帽容量精确算术](</home/dsh/Thomson Problem/proof_work/two_cap_capacity_exact_v1.json>)及[固定三角精确预算](</home/dsh/Thomson Problem/proof_work/fixed_triangle_two_cap_budget_exact_v1.json>)。仍须把排除覆盖到一个明确邻域及所有其余坏三角，才能用于完整最优性证明。

进一步的第一接触核数值搜索发现另外两个负样本簇，中心约为 (.346480293,.346480553,.346480725) 与 (−.071348864,.339279344,.339279344)，残差分别约 −1.00778×10⁻⁶、−6.66857×10⁻⁷；并未证明这些簇覆盖所有负域。见[搜索及聚类说明](</home/dsh/Thomson Problem/proof_work/negative_valley_seed1_2026_note_zh.md>)。针对两中心，已发现满足全部锚点及两两内积限制的六外点，Σφ 分别约 .0002975039、.0002107611，均低于相应预算。因此本节只用18项外点残差的松弛无法排除这两中心；这些可行点组并非更低 Coulomb 能量的反例。继续必须使用剩余45个“一个锚点加两个外点”三角、20个纯外点三角，或不同的核。数据见[其他负谷的外点组合](</home/dsh/Thomson Problem/proof_work/two_other_valleys2026_well_graph.json>)。现已用有理立体投影将六外点精确单位化，并以384位向外舍入区间严格认证上述辅助反例和能量下界；见[严格反例证书](</home/dsh/Thomson Problem/proof_work/two_other_valleys2026_certified_witness.json>)及[检查器](</home/dsh/Thomson Problem/proof_work/two_other_valleys2026_certify_witness.py>)。

只枚举已发现低井时，T2 的8个合规六点组合中，min(Φ+Ψ)约 .0510687313；T3 的1个合规组合给出 .0007705909，均高于各自预算。这里 Φ 是18项带两个锚点的残差，Ψ是45项带一个锚点的残差。这说明遗漏的外点对条件可能有效，但仅限这些离散组合，不能推及全部连续六点。详见[其他负谷阶段报告](</home/dsh/Thomson Problem/proof_work/two_other_valleys2026_findings_zh.md>)。

固定三角的排除已解析扩展到每个内积坐标半宽δ=10⁻¹⁰的闭立方体，比初始10⁻¹³邻域扩大1000倍。预算导数界S≈1669.1425675850548；把φ中的固定边限制在半宽10⁻⁹薄层后，单点扰动系数L=Σ边(D₀+8D₁+8D₂)≈4319.439961718143。全部薄层使用完整长方体，不使用Gram剪枝。精确有理裕量2m+4M−K−(6L+S)δ约1.60477713768×10⁻⁵>0。复用完整球面图和全局根域证书作为带哈希依赖，本轮未重跑它们。见[邻域证明及PSD求和附录](</home/dsh/Thomson Problem/proof_work/t1_neighborhood_sensitivity2026_neighbor_v3_note.md>)、[薄层检查器](</home/dsh/Thomson Problem/proof_work/t1_neighborhood_sensitivity2026_neighbor_v3.py>)及[证书](</home/dsh/Thomson Problem/proof_work/t1_neighborhood_sensitivity2026_neighbor_v3_certificate.json>)。父线程已独立重放v2与v3。这仍远未覆盖整个负残差谷。

当前两外点探索采用 W(q,r)=Ψ(q,r)+(φ(q)+φ(r))/5，每个外点出现于五对，故 Σ₁₅W=Φ+Ψ。若能在全部合规点对上严格证明 W≥m 且15m>K，即可排除固定三角。有限搜索目前T2最小已见值约7.80537×10⁻⁵、T3约3.55854×10⁻⁵，分别高于K/15≈3.00600×10⁻⁵和3.02945×10⁻⁵；这些只是 inf W 的上界候选，未构成下界或延拓排除。见[两外点场策略审查](</home/dsh/Thomson Problem/proof_work/external_pair_field2026_note_zh.md>)。首次四维连续域检查已完成预算内试验：59秒内处理2660盒、细分2628盒、按内积限制排除32盒，接受W下界的盒为0，仍有2600个待处理盒，因此没有证明W下界。只读审计核验5260个树节点的父子关系、四个完整根域及全部排除；每根的终端盒总体积均精确为16。主要障碍是单项式Horner区间过宽，代表性深层盒中的单个R宽度仍约1002。下一步试验三维Bernstein残差范围查询，避免重复同一Horner搜索；若统一下界失败，可转向[完整球面cell与加权组合证书设计](</home/dsh/Thomson Problem/proof_work/two_other_valleys2026_weighted_cell_certificate_design_zh.md>)。

新增T2二维单点筛选已从两个完整图域运行完毕：以φ≥1/5000为接受条件，正、负半球图分别处理1265、1341盒；高代价叶183、222个，内积或图圆盘排除叶1、4个，保留低代价叶449、445个。所有低叶深度14。每张图终端矩形的参数面积总和精确为4；两图低区域占447/16384≈2.72827%，其点对乘积域占199809/268435456≈0.0744347%。这些是图参数面积比例，不是球面面积，也不是运行时间保证。任一外点处于高代价叶时，由其他R非负立即得到W≥φ/5≥1/25000；所以只需继续检查低区域×低区域。见[二维检查器](</home/dsh/Thomson Problem/proof_work/t2_unary_screen2026.py>)及[完整叶记录](</home/dsh/Thomson Problem/proof_work/t2_unary_screen2026_result.json>)。尚有894²个有序低矩形对，未宣称全部闭合。独立审计以128×128网格核验两张图的终端矩形每格恰覆盖一次，并另行核对代数锚点舍入误差及原全局模型哈希；没有独立重建全部54次Bernstein数组。

低叶保存的负系数最小值b还能给出φ≥max(0,τ+b/(2⁶⁴D_min²⁷))：因b<0，取分母下界使该值更保守；原阈值中的EPS严格超过代数锚点近似误差。用两叶下界之和≥1/5000，可直接接受303673个有序点对。另将894个低盒分为30个容量一组，384位区间逐组包围完整矩形，全部组坐标直径平方<0.88，所以同组两单位点内积>0.56，排除55904个有序点对。两类有19105个重叠，合计处理340652个；剩余458584个有序点对，即229292个无序点对，尚未证明其W下界。容量程序已由母线程复跑；数值中心只用于提出分组，最后的直径、唯一归属和覆盖判据均用精确算术检查。见[叶下界恢复](</home/dsh/Thomson Problem/proof_work/t2_unary_leaf_pair2026.py>)、[容量一分组证明](</home/dsh/Thomson Problem/proof_work/t2_low_cells2026_capacity_note.md>)和[剪枝并集记录](</home/dsh/Thomson Problem/proof_work/t2_low_pair2026_combined_pruning.json>)。

独立静审还发现未来超时输入的风险：叶下界恢复程序原先只读取low_pending，可能跳过budget_pending。当前上游结果没有任何budget_pending，既有计数不受影响；程序已增加明确断言，存在预算未访问盒时立即拒绝处理。原运行源码另行归档并核对旧结果中的SHA256，未在活动批次中改写输入结果。

对这229292个无序待处理点对，第一批90秒Bernstein检查访问487个：369个严格证明W≥1/25000，117个严格违反内积限制，1个仍未决；未访问228805个，最终未决228806个。前缀记录以完整894编号集合、初始剪枝规则和按字典序访问记录定义覆盖，不能把未列入记录的点对删除。唯一已访问未决对的下界约3.82440×10⁻⁵，未达到4×10⁻⁵；不能归咎于时间截断。见[批次检查器](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_lowpair_batch.py>)及[结果](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_lowpair_result.json>)。数据层覆盖及分数算术审计已通过；另一检查器又在31.32秒内独立重建精确根系数，重算全部I384输入、13293次整数细分、7284个终端最小值及1110个查询覆盖，487条记录全部通过。它共享底层Bernstein变换和细分算术，因此不是完全独立软件实现；见[严格重播结果](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_lowpair_replay.json>)和[点对证明及层级设计说明](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_lowpair_note_zh.md>)。

分层产品检查也已完成一次118.46秒试验：建立1786个编号集合树节点，处理2012个产品块；40个下界通过块覆盖51689个有序点对，40个间距排除块覆盖78683个，3个容量排除块覆盖2352个。完整799236个有序点对逐项覆盖次数均为1，所有预算未处理块显式保留。独立数据审计核验3862个产品树节点、全部区间包围、分数算术及查询覆盖。与原初剪取并集后，新关闭57349个有序点对，仍有401235个未决；这一步尚未利用反向点对的对称闭包，也未合并前缀记录。新层级查询的根系数和细分例程沿用已测试实现，数据审计未再次重建各终端系数，不能称完全独立数值证明。见[层级检查器](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_hierarchy.py>)、[原始结果](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_hierarchy_result.json>)和[独立覆盖审计](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_hierarchy_audit.json>)。固定T2仍未排除，全球能量下界没有变化。随后将初剪、分层终端块和前缀记录作并集，再依据已精确验证的R对称性加入反向点对，最终399788个有序点对已关闭，399448个仍未决；相对初剪新增关闭59136个。这个数据聚合没有运行新oracle，也不能将其称为T2的完整排除。见[完整聚合记录与校验和](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_aggregation.json>)。

另一次2201训练点对的8维PSD对偶拟合，在5000个独立允许点对中有53个违反，最差残差约−0.00152548；该矩阵明确不可用，不能作为下界。见[拟合失败归档](</home/dsh/Thomson Problem/proof_work/sixq_dual2026_t2_bash_proposal_note_zh.md>)。目前优先推进精确矩形块覆盖。

第二版加入整块已证mask复用、跳过粗域无效查询并将细查询加至60次细分/16叶；178.10秒处理1067个块，仅重新识别已有证据覆盖的106124个点对，没有新增通过或排除。完整覆盖检查仍为每项恰1，未决块全部保存；与已有证据合并后仍为399788已关闭/399448未决。更细的oracle消耗了预算而未到达新的小块，本支线暂不继续重复增大预算。该结果不改变任何数学下界。

新增局部预算检查已完成：在T1中心±10⁻⁶的整个三参数立方体上，对三条∂R直接作96位有向Bernstein变换，严格得到预算K(T)=7(U−B)−R(T)的梯度一范数小于0.001061，计算1.50秒。这样，若另行完成扩大允许域至0.560008的固定球面证书、并对整个参数立方体证明球面参数导数界M_u、M_v、M_t，则ΣM<3.13421477978是一个保守充分条件。后两项尚未证明；没有据此扩大T1已证邻域。见[预算梯度检查器](</home/dsh/Thomson Problem/proof_work/t1_local_budget_gradient2026.py>)和[精确分数结果](</home/dsh/Thomson Problem/proof_work/t1_local_budget_gradient2026.json>)。

下一种扩大T1邻域的方法是先在球面上组合∂φ/∂(u,v,t)，再对二维齐次多项式作Bernstein界，避免分别对R在三维完整立方体求绝对导数。若三个一阶导均≤M、参数Hessian每项≤H，则六点代价损失≤18Mδ+27Hδ²；中心预算的导数也可在小参数盒上另行认证。这仍是待实现方案。δ变大后，固定锚点检查器必须重新覆盖anchor-dot≤0.56+8δ；不能继续复用只放宽10⁻⁸的旧球面证书。

另一个十二阶核负残差谷已取得新的固定三角严格排除。取精确有限小数T=(−0.9457080898901464,−0.6695418187936286,0.39181335775890314)，其Gram≈1.77278×10⁻⁵。对所有满足三条锚点内积≤0.56的球面外点，双有理图册完整根域认证φ_T(q)≥1/10000：共80树节点、39细分、41终端叶，其中27叶接受下界、14叶严格违反锚点上限，待处理为0。保存树的另一重放程序独立执行整数向下细分，重建根系数、核对全部锚点舍入与多项式点值、核验两图各面积4及所有终端判据，全部通过；共享齐次化及Bernstein后端，不能称完全独立实现。虽然原程序允许下端点和圆盘剪枝，实际树完全没有使用它们，因此结论不依赖驻点内积下界。

六个外点于是至少贡献0.0006，严格大于此T的旧预算K≈0.0001995903851311931，差值约0.0004003406148688069。这排除该固定T出现在任何E≤U的九点构型中，没有证明整个谷或某个邻域均被排除。见[新球面检查器](</home/dsh/Thomson Problem/proof_work/d12_newvalley_extension2026_exact_verify.py>)、[完整树证书](</home/dsh/Thomson Problem/proof_work/d12_newvalley_extension2026_exact_result.json>)、[树重放程序](</home/dsh/Thomson Problem/proof_work/d12_newvalley_extension2026_exact_audit.py>)及[重放结果](</home/dsh/Thomson Problem/proof_work/d12_newvalley_extension2026_exact_audit.json>)。

扩大近Gram边界的坏谷时，宜使用光滑锚点参数a=(1,0,0)、b=(u,√(1−u²),0)、c=(v,−√(1−v²−z²),z)，此时第三内积t=uv−√(1−u²)√(1−v²−z²)、Gram=(1−u²)z²。z=0平滑描述共面边界，避免直接对√Gram求参导数的奇异性。尚未完成这一参数域的统一排除。

四点单外点乘子的固定模型障碍也已有严格见证。使用[冻结低trace十二阶快照](</home/dsh/Thomson Problem/proof_work/d12_competitive_probe2026_snapshot.json>)，SHA256为70211e9762a6893f3cf2699f115c1d3bf3e8212b58870268ec89b6bd02f7434c，iteration2、trace7.801171936026683；将JSON中的A、c逐项按Fraction(str(value))解释为明确有理数，c=4586543114249177/2000000000000000。取精确有限小数
T=(−0.6385403003811887,−0.5549003805968542,0.3503407663001601)，
q₀=(0.3712592268143786,−0.6736806264879448,−0.639)，q=q₀/||q₀||。
锚点按Cholesky精确定义，其中Gram=102470759040191119139793751654127136395901832577/250000000000000000000000000000000000000000000000>0，q₀·q₀=200000000000000001390023886397/200000000000000000000000000000。384位整数向外舍入、原A六排列Q递推与旧807项多项式的只读重算给出严格界：

−0.000015588 < R_new(T) < −0.000015587，
−0.000023975 < φ_T(q)−K(T)/6 < −0.000023974。

六个相关内积均严格在[−0.9957,0.56]内，0<R₀(T)<β、0<φ<K/6，故四个三角的旧残差总和也严格小于β。没有核查LP24的额外Cpair条件，不能称通过所有已知约束。在上述已检查域，对这个冻结有理模型，任意λ≥0（即便依赖T或q）都有R_new+λ(φ−K/6)<0。因此这种固定核加单外点预算乘子的充分结构不可能成立。不能移用于尚未构造的精确接触修正核，也不能排除改变核、加强域条件或耦合多个外点。没有产生九点Thomson反例。因新文件路径的写入失败，本轮诊断在内存执行、stdout记录，未生成独立脚本或证书文件；上述具体有理输入、模型哈希及严格界在此归档。

对同一T再加入双外点耦合W=(φ(q)+φ(r))/5+ΣₐR₀(a·q,a·r,q·r)。真实六外点必有一对W≤K/15，因为对15对求和得到Σ₆φ+Σ₄₅ψ≤K。有限采样3000球面点、筛选1213允许点并检查低φ的256点所形成24485合法点对，采样最小W=0.00008371962106495371，高于K/15≈0.000029447696779298272；这是所选有限点对的上界，尚无连续域排除证明。

最新一次十二阶非接触实验保留322个数值零空间变量，去掉所有接触/二阶约束，在完整Gram∩[-1,0.56]³域训练，两轮后结束，总246.60秒。两轮CLARABEL均达到MaxTime，返回矩阵的最小特征值为−2.0494×10⁻⁴和−1.8863×10⁻⁴，训练残差也分别为−2.7730×10⁻⁴和−2.4804×10⁻⁴；独立12000随机点中有450和222个违例。原A核复核的最低观测残差为−4.2532×10⁻⁴和−6.1369×10⁻⁴，原核/编译求值相差不超过1.44×10⁻¹⁴。由此，这两个返回模型均不具备可认证的PSD可行性，没有做有理精确化，也没有提高25.7599205这一已认证下界。求解未成功不等于322维核空间不存在更好模型。完整数据见[非接触实验模型](</home/dsh/Thomson Problem/proof_work/d12_nonsharp2026_results.json>)、[源程序](</home/dsh/Thomson Problem/proof_work/d12_nonsharp2026_experiment.py>)和[日志](</home/dsh/Thomson Problem/proof_work/d12_nonsharp2026_experiment.log>)。

对上述新T做连续域单点筛选，原两张球面图完整根域在27.71秒处理：正图243节点，high34/excluded9/low_valid35/unresolved44；负图327节点，high33/excluded5/low_valid53/unresolved73。high证明φ≥0.00011，low_valid证明φ>0.00004；117个深度20未决盒未获此下界，时间待处理为0，不能宣称全域φ≥0.00004，也不能把负Bernstein系数当作函数负值。原输出只保留8个未决示例，另109个loc/下界未输出；进程结束后不能据此恢复完整严格全局下界或开展完整点对覆盖。两图保留low+unresolved参数面积分别17/1024及9/512；参数面积不是球面面积。

已有局部标签仍可作有限点对剪枝：全域φ≥0可由旧R₀证书得到，两个high成员或一个high加一个low_valid成员均使(φ(q)+φ(r))/5≥0.00003>K/15。按67个high、88个low_valid、117个unresolved终端矩形计，272²=73984个有序矩形对中，67²+2·67·88=16281个可用此规则处理，余57703个仍未决。此为类别计数与局部充分条件，不是全点对域排除证书；缺失终端数据不能当已处理区域。

另一次反极点25.82提案完成了精确PSD、Q₄核重建、h₁₁下界及归一化检查，但全根域细分触发“AssertionError: Depth guard reached; no certificate”，没有成功证书或保存的未决盒。不能升级此前25.80结果或驻点点对阈值，也不能由该退出断言提案必定为假。见[失败记录](</home/dsh/Thomson Problem/proof_work/antipodal_anchor_improve2026_failed_verification.json>)及[认证说明](</home/dsh/Thomson Problem/proof_work/antipodal_anchor_improve2026_exact_notes.md>)。

## 9. 与当前证书匹配的必要域及四点闭合条件

当前必要域使用807项旧有理残差R₀，B₀=25.7599205，固定U取第1节上界，β=7(U−B₀)≈0.00046221888882094853。全局极小构型的全部84个异点三角均满足Gram≥0、各点积在[−0.9957,0.56]且0≤R₀≤β。下端点限制使用驻点性；不能推广为任意低能量非驻定构型。候选12种三角的R₀约在[5.4987576×10⁻⁶,5.5151016×10⁻⁶]，最小预算余量>0.0004567。父线程已逐行检查并独立重跑来源匹配的区间程序，通过全部12类。第一版误读较早d4证书，所给0.1049预算虽对应一个较弱有效域，但不匹配当前求解器；保留旧档并明确由v2替代。见[修正版定理与来源说明](</home/dsh/Thomson Problem/proof_work/restricted_sharp_theorem2026_v2_source_corrected_zh.md>)、[区间成员检查](</home/dsh/Thomson Problem/proof_work/restricted_sharp_theorem2026_v2_source_corrected_candidate_check.py>)及[结果](</home/dsh/Thomson Problem/proof_work/restricted_sharp_theorem2026_v2_source_corrected_candidate_check.json>)。

如果新PSD核、minorant和精确常数B_new=E_*已构造，只需证明其残差在上述必要域非负，即可证明候选达到全局最小能量。唯一性可以另外处理；不必先分类所有零点。新PSD核的729项完整有序和全球非负，重复指标不要求属于84个异点三角的必要域。

还可用四点延拓加强必要域。令K(T)=β−R₀(T)，φ_T(q)如第8节定义。六外点满足Σφ≤K，故至少一个外点满足φ≤K/6。于是每个实际三角T都有一个满足点积界、真实球面四点Gram秩≤3、φ≤K/6的延拓。若λ(T)≥0，并能在全部允许四点上严格证明

    R_new(T)−λ(T)[K(T)/6−φ_T(q)]≥0，

则选上述外点便得R_new(T)≥0，从而可接回全局最优性充分条件。这只是待构造的证书形式。候选接触处可能强制λ=0；可测试λ=cΣ边ω(t)，其中c≥0、ω(t)=∏六节点(t−t_j(r_*))²，但没有证明存在可行λ或该四点不等式全域成立。

还可改选锚点：令a=min₈₄ R₀(T)，选择达到最小值的三角T₀。由所有R₀≥0及Σ₈₄R₀≤7(U−B₀)，严格得到

    0≤a≤(U−B₀)/12=0.000005502605819297006308522813374502388…<1/180000。

因此，针对“至少存在一个这样的锚点”的延拓穷尽，只需覆盖R₀(T₀)≤1/180000，比每个任意三角使用β的上界强约84倍。这里不能把这个条件施加于全部84个三角，更不能仅证明新残差在这块较小域非负就直接套用三点求和定理。

对所选T₀，每个其他三角的旧残差均≥a，故φ(q)≥3a、Ψ(q,r)≥3a；另外20个全外点三角至少贡献20a。真实六外点于是还须满足

    Σ₆φ+Σ₁₅Ψ≤7(U−B₀)−21a。

这个增强条件由同一预算恒等式直接证明，无需驻点假设。尚未据此完成锚点参数域及六外点的全覆盖。

## 10. 新接触凸组合：真根精确化与十二个邻域

最初把首个PSD接触核与第三批第二个PSD核按有理权重112219/500000、387781/500000混合。这两个模型使用完全相同的约化基；距离接触集合平方归一化的有限样本LP用于选取权重。后来严格定位发现，这个权重仍漏掉一处内部窄负谷，距离最近CGF接触约0.0213。因此以下PSD、接触和十二邻域结论仍成立，但不能由这个核完成全Gram域非负证明。

具体地，取有理点

    u=−8251973256609811/11258999068426240+1/10¹²,
    v=−20600450512322599/28147497671065600,
    t=9812112633233291/28147497671065600。

三点积都在(−1,0.56)内，精确Gram行列式>0，约0.17964。用收紧到2⁻³⁵⁰根宽的真实系数包围，I384 Horner与独立Fraction逐项区间求和均严格给出R(u,v,t)<0，数值约−2.79094777×10⁻¹⁸。本线程又只读取807个系数端点，用纯Fraction独立重算并确认上端点严格为负。见[负点与梯度程序](</home/dsh/Thomson Problem/proof_work/narrowroot2026_pointcheck.py>)、[严格见证](</home/dsh/Thomson Problem/proof_work/narrowroot2026_pointcheck.json>)及[本线程分数重放](</home/dsh/Thomson Problem/proof_work/narrowroot2026_pointcheck_parent_replay.json>)。这否定当前辅助残差的全域非负性；它不是九个电荷的反例，不改变第1节25.75995的有效下界。

随后在真实驻点r_*上固定157个有理坐标、精确解33个接触方程，依靠既有秩33/12条兼容性恒等式证明全部45条接触条件。最大坐标修正约1.4403×10⁻¹²；全部10个非空约化块通过I384向外区间LDL正定检查。本线程又从保存的有理输入完整重放修正与PSD检查，通过逐项一致性断言。使用真正接触Hermite H27，令c=E_*/12+F111/8，因此新核的形式目标是精确E_*，而不是任意小数截断。

807项真实残差的代数系数已保存为严格区间；不能把端点代入后称为原多项式。九种内部接触已证明整个立方体内Hessian正定；三种边界接触则在扩展u盒上证明R_u>0，并证明下Gram图函数的二维Hessian正定。配合精确接触值与梯度，这严格给出十二个正宽度邻域上的R≥0，半宽从10⁻⁵至10⁻³。只允许使用证书列出的原box作局部终端，扩展u区间只是边界证明的辅助。

主要文件：[新精确核证书](</home/dsh/Thomson Problem/proof_work/d10_sharpconvex_exact2026_certificate.json>)、[本线程重放](</home/dsh/Thomson Problem/proof_work/d10_sharpconvex_exact2026_parent_replay.json>)、[真实系数区间](</home/dsh/Thomson Problem/proof_work/d10_sharpconvex_exact2026_coefficients.json>)、[十二个邻域](</home/dsh/Thomson Problem/proof_work/d10_sharpconvex_exact2026_local.json>)及[构造和拼接说明](</home/dsh/Thomson Problem/proof_work/d10_sharpconvex_exact2026_notes_zh.md>)。

有限闭合论证已由另一个研究线程核查：729项完整有序和分解为6×84个异点项、6×36个重复项及9个全等项，常数c=E_*/12+F111/8给出精确能量缺陷恒等式。若这组真实残差在Gram∩[-1,0.56]³全域非负，则仅凭点积上界域即可推出E_min=E_*；无需旧nonsharp下界、驻点反足界或先证明唯一性。见[闭合定理与有限依赖清单](</home/dsh/Thomson Problem/proof_work/d10_sharpconvex_exact2026_closure_checklist_zh.md>)。

新增[前置验证器](</home/dsh/Thomson Problem/proof_work/verify_sharp_prerequisites2026.py>)已经本线程在全新目录完整重跑，29.38秒通过：配对0.56排除、根区间细化至宽度小于2⁻³⁰⁰和E_*<U、真实H27数据、W的12阶子式−36r、真根接触修正及PSD、七组完整数学数组一致性、十二个正宽度邻域均重新认证。见[本线程前置重放报告](</home/dsh/Thomson Problem/proof_work/sharp_prerequisites2026_parent_replay2/prerequisites.json>)。其中WM=0及rhs兼容性仍依赖给出的几何恒等式证明，不能用区间残差包含零来替代。

首个[80位远区引擎](</home/dsh/Thomson Problem/proof_work/sharp_global_away2026_engine.py>)整根域尝试在180.03秒结束：7911节点、3962次细分、3949个终端、14个未决盒；1807个正值、2019个Gram排除、123个顺序域排除，尚未走到接触邻域。见[未完成结果](</home/dsh/Thomson Problem/proof_work/sharp_global_away2026_run1.json>)。它没有给出负点见证，也没有全域结论；未决盒仅供诊断，不能直接恢复为证明。

48/80位混合树第一轮600.04秒处理29837节点，保留18个完整pending；local终端3个、R−λg终端63个，已到达接触附近，但没有闭合。另一个保留80位尺度、仅在幅值安全时使用int64的版本运行600.12秒，处理25216节点，保留17个pending；仅两次安全转换，未改善大域瓶颈。两轮均由完整根域出发、没有恢复旧frontier，也均不是全域证书。见[混合树未完成结果](</home/dsh/Thomson Problem/proof_work/sharp_global_hybrid2026_run1.json>)和[安全转换版本未完成结果](</home/dsh/Thomson Problem/proof_work/sharp_global_fast80_2026_run1.json>)。

新增固定有理合同变换W，将每个完整盒上的Hessian包络变为WHWᵀ后作严格区间LDL，已扩大十二类邻域中的七类：CFF与DFF各扩大10倍，CGF、CBA、GAF、BFF、GDF各扩大3倍；其余没有缩小。W为精确单位下三角有理矩阵，故合同变换保持正定性。边界三类仍保留整个扩展u盒上的R_u>0。本线程已独立重放12.19秒全部通过。见[预条件局部检查器](</home/dsh/Thomson Problem/proof_work/local_precondition2026_verify.py>)、[本线程扩大盒证据](</home/dsh/Thomson Problem/proof_work/local_precondition2026_parent_boxes.json>)及[数学说明](</home/dsh/Thomson Problem/proof_work/local_precondition2026_notes_zh.md>)。

为消除Python大整数细分的开销，已独立实现[有范围保护的C128后端](</home/dsh/Thomson Problem/proof_work/exact128_2026.c>)与[Python包装](</home/dsh/Thomson Problem/proof_work/exact128_2026.py>)：保持原80位尺度，严格限制每个整数绝对值小于2^124，显式处理负数有向舍入。750次完整细分与原Python整数实现一致，450次独立Fraction舍入及15次拒绝检查通过。该后端本身没有证明远区非负；邻域之外的完整Gram域仍需严格覆盖。第1节可靠下界仍是25.75995。

原生整树尝试早期明显提速，但约131500节点后所有终端计数停止增长，待处理数每次细分增加1。最后日志为160000节点、349.83秒、28535个pending；没有正常退出结果或保存栈，后台注册随后不再识别该任务。仅这些pending的R张量已需约9.33GiB，资源问题可信但没有OS退出证据，不能写成已确认OOM或正常预算退出。见[诚实中断记录](</home/dsh/Thomson Problem/proof_work/sharp_global_native128_2026_interrupted2026.json>)。另行授权的深度护栏定位随后找到内部点，精确下降一步即给出真实负残差；这已在本节开头记录。因此当前权重的全域非负命题已被否定，继续增加树深度或仅收紧系数误差都不能修复它。

独立只读审稿逐项核对了45条接触的秩33兼容性、729项归一化、下Gram图的完整垂直路径、合同预条件、对称化误差下界、内接立方体及原生负整数舍入，未发现这些数学环节的阻断问题。该审稿没有执行任何根域重放，不能代替尚未完成的全覆盖。完整入口现会重新认证扩大邻域并冻结实际原生源码，见[完整复核管线](</home/dsh/Thomson Problem/proof_work/verify_sharp_pipeline2026.py>)；最终结论仍须以fresh完整运行的pending清零为前提。

针对误差问题，已另用纯I384二分214次将真根区间缩至宽度小于2⁻³⁵⁰，重新计算同一真根下的33条接触修正、PSD、H27和全部807项残差系数。系数总区间宽由1.02363×10⁻¹⁸降至3.88799×10⁻⁸³；原始及预条件各十二个物理盒的端点逐项与旧盒相同且重新通过。见[同步构建源程序](</home/dsh/Thomson Problem/proof_work/narrowroot2026_build.py>)、[构建结果](</home/dsh/Thomson Problem/proof_work/narrowroot2026_result.json>)及[新系数包围](</home/dsh/Thomson Problem/proof_work/narrowroot2026_coefficients.json>)。200位系数中点量化仍有约10⁻⁵⁸量级的附加误差，须在远区下界中另外计入；不能只引用代数系数区间宽。旧曲率诊断也表明其旧误差影响半径约10⁻⁸，远小于局部盒宽，故尚不能把原停滞简单归因于旧系数误差。

修改后的完整管线已作一次fresh集成检查：重跑全部前置和扩大邻域，远区预算刻意设为0秒，结果正确写为INCOMPLETE_GLOBAL_COVERAGE、global_energy_equality=false。见[衔接检查结果](</home/dsh/Thomson Problem/proof_work/sharp_pipeline_smoke2026_01/result.json>)。该检查确认实际使用原生引擎及新局部证据，没有开展新的全域覆盖。

## 11. 两点严格排除三个指定核的整个凸包

将同一接触基下的三个数值端点分别作真根接触修正，得到三个严格PSD端点。这些端点共有同一Hermite H27；它们的系数和证书已逐个保存，见[端点构造说明](</home/dsh/Thomson Problem/proof_work/d10_affinefamily2026_notes_archive.md>)。取合法Gram点

    P=(14/25,14/25,14/25),
    Q=(-0.7319927153030016,-0.7319927159082786,0.34931898965249153),
    λ=1/10000000。

以上小数均按精确十进制有理数解释，两点的Gram行列式严格为正。令R_j为第j个端点对实际势f(t)=(2−2t)^(-1/2)的残差。384位向外区间计算严格得到R_j(Q)+λR_j(P)的上界，三个端点依次为

    -5.714286260368041×10^-10,
    -4.490141244152932×10^-9,
    -2.864166714265712×10^-9。

这些显示值只是精确负区间端点的近似。原始整数端点、系数哈希、Gram有理值及Hermite残差的同样结论见[两点障碍](</home/dsh/Thomson Problem/proof_work/d10_sharpconvex2026_two_point_obstruction.json>)及[检查程序](</home/dsh/Thomson Problem/proof_work/d10_sharpconvex2026_two_point_obstruction.py>)。本线程另以纯Fraction逐项区间求和，并用isqrt独立构造势函数平方根的有理包围，得出同样的严格负上界，未导入原区间或多项式辅助程序；见[独立重放](</home/dsh/Thomson Problem/proof_work/d10_sharpconvex2026_two_point_parent_replay.json>)。

因为残差关于端点权重为仿射函数，对任意w_j≥0、Σw_j=1，均有Σw_j[R_j(Q)+λR_j(P)]<0。因此该凸组合的残差不可能在P、Q两点同时非负。**这严格排除了这三个指定端点的整个凸包；没有排除完整半正定核空间，也没有证伪九电荷候选解。** 在Q，旧混合核补回Hermite误差后的真实f残差也严格为负，约−2.35099675×10^-9，详见[窄谷审计](</home/dsh/Thomson Problem/proof_work/d10_sharpconvex2026_valleycenter_audit.json>)。

另将旧残差整体平移1/120000000，尝试证明E_min≥E_*−10^-7。一次完整根域检查240.46秒处理102083节点，保留22个未决盒，没有触发资源护栏。此尝试没有闭合，故不能报告新下界；当前可靠下界仍为25.75995。见[未完成树](</home/dsh/Thomson Problem/proof_work/sharp_global_bounded2026_run1.json>)、[平移目标说明](</home/dsh/Thomson Problem/proof_work/sharp_global_bounded2026_target.json>)及[独立平移验证](</home/dsh/Thomson Problem/proof_work/sharp_global_bounded2026_shift_replay.json>)。

已经在190坐标、33条独立接触约束的完整157维仿射空间内尝试新方向，三轮数值搜索修复了P、Q，所发现负残差由约−4.34×10^-4缩至−1.95×10^-6，但仍存在不同的内部负谷。该结果说明旧三端点障碍不适用于整个核空间；它不是全域证书，求解器也均返回optimal_inaccurate。见[有限三轮研究报告](</home/dsh/Thomson Problem/proof_work/d10_ridge_repair2026_report_zh.md>)。后继搜索还须使全域余量与接触Hessian一致：若R≥η·dist(·,接触集)^2，则内部接触必须满足Hessian≥2ηI，边界接触须满足校正切向Hessian≥2ηTᵀT。

## 12. 解析势认证闭合：距候选能量不超过10⁻⁷

本节结果取代上述历史段落中的“当前可靠下界仍为25.75995”。使用同一真实PSD核，但在远区直接下包真实势f(t)=(2−2t)^(-1/2)，已得到

\[
\boxed{E_* -10^{-7}\le E_{\min}(9)\le E_*.}
\]

因此严格十进制下界可取25.75998643126983。本线程由真实能量区间下端作精确Fraction减法验证了这个显示值，见[下界及精确端点](</home/dsh/Thomson Problem/proof_work/analytic10_2026_bound_parent.json>)。这将此前25.75995对应的能量缺口缩小约397倍，仍留下正缺口10⁻⁷。不是精确最优性定理，也未声称是文献最佳。

### 12.1 方法及数学恒等式

令d(t)=F(1,t,t)，c=E_*/12+F(1,1,1)/8，R_f=Σ_axis[f(t)−d(t)]−7F−c。九点完整有序三点和满足

    S=6Σ_84 F+6Σ_36 d+9F(1,1,1)≥0，
    (1/7)Σ_84(R_f+δ/12)+S/6=E−(E_*−δ)。

三点核的F每轴次数至多10，d次数至多20。以严格有理中点F_m和总误差ε构造K=−7F_m−c_upper+δ/12−10ε；对每个轴的当前区间，正系数Taylor截断给f的十次下界，d_m的向上Bernstein多项式转成精确幂基后，将11至20次项用正系数之和替代，给十次上界。因此整个三变量下界只需11³张量，而非原28³张量。全部舍入有明确方向，并在C128运算前后检查范围。详细推导见[数学说明](</home/dsh/Thomson Problem/proof_work/analytic10_2026_derivation.md>)。

### 12.2 实际闭合记录

[完整根域运行](</home/dsh/Thomson Problem/proof_work/analytic10_2026_run1.json>)从[-1,14/25]³出发，δ=1/10000000，含构建耗时45.897秒：110513个访问节点、55256次分割、55257个终端、pending=0、最大深度46、无护栏退出。终端包括直接判正23699、Gram不可行24117、对称顺序排除2452和非负Gram乘子判正4989。两个树计数恒等式成立。

**局部终端使用次数为零。** 因此实际证明不依赖旧局部盒、Hermite H27、45条接触兼容性或精确边界jets。边界λ只需是非负有理数；它们的具体近似精度无关证明。33个可逆方程定义代数B，严格区间LDL证明B正定，进而NBNᵀ给出所需PSD核即可。配对排除保证所有可能优于候选的构型都落在点积≤14/25的域内。

### 12.3 独立复核与信任边界

另一研究线程逐行审查[引擎](</home/dsh/Thomson Problem/proof_work/analytic10_2026_engine.py>)及[C求和程序](</home/dsh/Thomson Problem/proof_work/analytic10_2026_sum.c>)，重算真根端点导数、配对0.56排除、33维修正、I384 LDL和全部F/c/E_*包络，逐项与输入一致。两个C库重新编译后均与实际运行二进制逐字节相同。随后使用重建系数，以零遍历预算重建K、d、Gram根张量，全部数学数组和哈希一致。见[必要前提审计](</home/dsh/Thomson Problem/proof_work/analytic10_2026_audit_prerequisites.json>)及[根输入审计](</home/dsh/Thomson Problem/proof_work/analytic10_2026_audit_rootinputs.json>)。

另有250个精确Fraction单变量不等式检查及100次C128与Python任意精度求和比较通过，见[实现检查](</home/dsh/Thomson Problem/proof_work/analytic10_2026_smoke2.json>)。这些检查辅助发现实现错误；全域结论来自实际完整树及严格下包络。

独审没有另行遍历整棵树。随后本线程实际运行[完整验证入口](</home/dsh/Thomson Problem/proof_work/analytic10_2026_verify.py>)的--replay-root选项：重新计算所有必要前提，并传入空局部列表，从完整根域再次闭合110513节点。总耗时61.124秒，其中根域45.188秒；计数、最大深度及transcript哈希与首轮完全一致，运行前后依赖SHA检查均通过，见[本线程完整重放日志](</home/dsh/Thomson Problem/proof_work/analytic10_2026_parent_replay.log>)。此为同一树算法的重复执行，不能称为独立实现。入口另经[静态审查](</home/dsh/Thomson Problem/proof_work/analytic10_2026_audit_wrapper.json>)，冻结输入见[依赖清单](</home/dsh/Thomson Problem/proof_work/analytic10_2026_dependencies.json>)。

本结论仍依赖所述数学恒等式及Python/C正确执行，没有经过外部同行评议；Lean 工程已检查候选几何、族能量恒等式与域受限覆盖逻辑，但最终定理尚未形式化认证。

### 12.4 精确证明仍缺什么

当前旧混合核的真实f残差在合法Gram点Q严格为负约−2.351×10⁻⁹，因此不能把本节δ直接设为零。指定三个核的整个凸包亦已被两点分离证书排除。完整157维接触仿射空间的数值搜索尚未得到全域非负的新核；未收敛求解器输出不能当成不可行证明。可继续寻找新核、增加核次数或采用四点延拓；必须重新验证PSD、下界方向及完整根域覆盖。距候选能量10⁻⁷也不能自动推出构型接近候选，仍缺少把能量缺陷转成构型距离的全局稳定性定理。


## 13. 新核的精确全域闭合与完整证明候选

本节取代第12节末“尚未得到新核”的历史状态。加入三个Gram边界接触点的正法向条件后，完整157维接触仿射空间中的一次解析修复得到新核。它不是此前已被负点否定的混合权重，也没有沿用旧核的局部盒。

新核真根修正、严格PSD和全部十二类局部盒通过；随后直接认证真实势残差，δ=0，从完整[-1,14/25]³根域检查136125节点，pending=0。另一次从有理种子开始的整链重放重算配对排除、真根、Hermite、接触修正、系数、PSD、局部盒，再运行同一全根域树，结果与首轮完全一致。接触几何审查直接验证132个anchor矩分量，以rank33/W兼容性证明45个精确条件；总能量恒等式经有理枚举逐系数验证。

合并这些结果，得到会话内审查已闭合的计算机辅助证明候选 E_min(9)=E_D(r_*)，尚未经外部同行评议或独立实现；候选几何、九点互异、族能量恒等式、族能量一阶/二阶导数、驻点存在唯一性与族内严格全局极小性、逐对路径导数、能量梯度逐对和及其内积形式、多点路径导数、梯度零点等价、一阶最优性条件与能量置换不变性、全局极小元存在性、区间严格单调性、严格凸性、能量连续性、能量泛函的等距不变性与内积表示、逐对能量界、候选能量严格极小、精确距离谱与物理域 Gram 约束的几何必然性、有序内积三元组的排序不变性、候选能量 < 26 的有理上界、能量齐次性与 f(t) 内积 rpow 形式、Bachoc–Vallentin 三点正性、三点恒等式、见证式 SOS 三点界、叶证书语义与覆盖组装、PSD 证书语义、区间算术与 Bernstein 系数证书语义、带符号乘非负区间的 `mulMixed`、Bernstein 基区间包络、三元乘积包络与有限和包络、冻结命题到全局下界的等价归约、以及域受限覆盖逻辑已由 Lean 检查，但最终定理尚未形式化。最优构型的全局唯一性未证明。公开文献状态与本次新构造应分开表述。

- [完整证明候选稿](</home/dsh/Thomson Problem/proof_work/THOMSON_N9_PROOF_CANDIDATE_zh.md>)：PSD原理、接触兼容性、局部桥接、全域覆盖和总能量闭合。
- [最终恒等式与关联审计](</home/dsh/Thomson Problem/proof_work/sharp2026_final_linkage.json>)。
- [完整重放记录](</home/dsh/Thomson Problem/proof_work/relative_normal2026_replay2/prerequisites_and_root.json>)。
- [可指定新输出目录的复算入口](</home/dsh/Thomson Problem/proof_work/verify_thomson_n9_sharp.py>)。

旧失败记录仍保留，因为它们说明数值扫描无负点、接触点Hessian正定或极小能量缺口均不足以替代全域严格证明。真正使本轮结果不同的是新模型全部数学前提通过，并且零误差完整根域闭合。

### 13.1 Lean 具体局部 Hessian 证书的 2026-10-19 状态

上节列出的“新核”算术与几何论证本身没有改变；本节只记录把局部证书接入 Lean 的最新状态。`LocalSparseHessianAAABase`、`Chunk00`–`Chunk07` 和组装 `LocalSparseHessianAAA` 已全部编译；550 个非零项改用 `IntervalLocalOps.mem_mul_of_bounds` 的 8 个精确文字角点证明，绕开逐项 `norm_num` 展开 807 个系数区间的性能墙。2026-10-20 14:45，`python3 -B proof_work/publication_validation/verify_local_lean.py --adopt-build` 返回 `LOCAL_LEAN_COMPILER_AXIOMS_AND_KERNEL_PASS`：620 条 `#print axioms`、91 模块闭包、根入口与 `Axioms.lean` 均通过，`leanchecker ThomsonNine.LocalVerification` exit 0。复核包已按 PASS 报告和 stamp 重打；`TargetBinding`、`TwoSourceBindings`、`ChainBindings` 覆盖 87/807 个目标的区间绑定；`GatheredBinding` 对 `.t126` 覆盖完整 807 项展开后的 gathered coefficient；`GatheredTwoSource` 覆盖其余 32 个 two-source 目标，`GatheredChain` 覆盖 54 个 chain 目标；`SingleSourceBindings` 覆盖 19 个单源目标，`FiveSourceBindings` 覆盖 21 个五源单轴 chain 目标，`ChainRestBindings` 覆盖 21 个六源单轴 chain 目标，`MultiCornerBindings` 覆盖 15 个五源多轴 delta≤1 目标，`MultiCornerPowBindings` 覆盖 9 个 delta≥2 目标，累计 255/807 个目标有完整 807 项 gathered 绑定（含 `MultiCornerPBindings.lean` 的 13 个八源三轴目标）。但真实残差识别仍未完成。该 PASS 仍是本地、条件性的：AAA 定理以固定实系数族属于 `coefficientInterval`、点属于 `relativeBox` 为前提；真实残差/平移系数绑定、其余 11 类、45 个接触等式、68,063 叶覆盖实例化与最终 `ThomsonNineClaim` 仍是未形式化的桥梁，且没有外部同行评议。准确状态见 [AAA 状态](</home/dsh/Thomson Problem/proof_work/publication_validation/AAA_PARTIAL_STATUS_2026-10-19_zh.md>)。
