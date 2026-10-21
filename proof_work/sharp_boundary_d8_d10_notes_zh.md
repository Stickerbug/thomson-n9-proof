# Gram边界强化的八/十阶数值探索（进行中）

本记录仅为数值候选搜索，不是严格证书、数学不可行性证明或Thomson构型反例。
竞争域改为Gram PSD与[-1,.56]^3交集，依赖父线程独立的pair056_optimized_certificate.json；
这里没有自行证明或重复几何兼容性条件。

## 八阶边界探索

sharp_boundary_actualf_v2.py复用exact-feature零空间、QR、解析jets和SVD消等式；100未知、39方程rank32。
初始3009个训练三角，包括950随机、1300 Gram边界、700近反极、81个反极线点、候选和旧违例，排序去重。
实际f=(2-2t)^(-1/2)训练和验证，tracecap=1e5，目标1000tau+1e-8trace。
由旧模型x warmstart，追加worst samples/local minima/DE cuts。

独立验证不仅使用3D DE，还包括：
- 每轮18k新Gram条件随机、12k新Gram边界、8k近反极点；
- theta=pi边界的alpha+beta<=2pi-acos(.56)线性域；
- theta=0边界的alpha-beta>=acos(.56)与beta-alpha>=acos(.56)两个线性域；
- 每个2D边界分支12至16个SLSQP起点和独立seeded 2D DE；
- 26个3D SLSQP起点（解析梯度）和2次seeded 3D DE；
- 反极线端点等单点检测；独立原numeric kernel design交叉检查。
候选jets和优化梯度全部解析，未以有限差分构造jets。

|轮|训练数|solver|tau|minEig|接触最大误差|独立最低残差|
|---|---:|---|---:|---:|---:|---:|
|0|3009|SCS|9.32136424348e-05|-0.0066642818|9.437e-14|-0.0050181049484|
|1|3350|CLARABEL|0.00146954106327|-4.0382496e-07|1.22e-13|-0.00437398572478|
|2|3691|CLARABEL|0.00169960278826|-1.8531953e-07|1.282e-13|-0.00249653577469|
|3|4029|CLARABEL|0.00174175097595|-1.1007696e-07|8.094e-14|-0.00177412823925|
|4|4361|SCS|0.00012608829802|-0.0082492236|1.298e-13|-0.000631277920134|

第0和第4轮CLARABEL两次SolverError后fallback SCS，最小特征值约-.00666/-.00825，明显不满足PSD，
绝不能把这些轮较小tau或minR视为有效改善。
第1至3轮CLARABEL数值近似PSD（小负特征值约1e-7），tau趋于.0017。
第3轮最坏点约(-.82984069,-.25656209,.42659941)，Gram det约.2452，已经在Gram内部。
因此处理边界约束仍不能单独闭合当前d8缺口。
原设计最多10轮；五轮落盘后因重复低精度SCS fallback主动取消，bash186已收集SIGTERM。
最终JSON solution是第4轮SCS结果，不是可接受PSD模型；history保留前面各轮诊断。

## 十阶

新脚本sharp_boundary_actualf_v3.py，仅授权最多3轮，目标缩回tau+1e-8trace，tracecap=1e4，
SCS fallback最多5000 iterations；继承d8训练cuts，lift旧d8有效模型并投影到d10的contact仿射空间。
每轮保存x与全部模型，若minEig>=-1e-6则允许best_solution数值快照（仍不代表严格PSD）。

十阶三轮均CLARABEL，状态optimal（查看完整JSON），全部tau=0且浮点最小特征值为正。
但独立验证仍有负残差，不能据训练tau=0宣称成功。

|轮|训练数|tau|trace|minEig|接触最大误差|独立最低残差|
|---|---:|---:|---:|---:|---:|---:|
|0|7311|0|10.87662727|1.2584785e-08|5.135e-15|-0.0159168402043|
|1|7652|0|14.13183867|1.4128271e-08|6.661e-15|-6.02064072539e-05|
|2|7988|0|15.53609694|6.803849e-09|5.662e-15|-8.14418164023e-05|

首次独立SLSQP找到(.56,.56,.56)的R约-.01591684，该点不在原训练集；加入下一轮cuts后被修复。
父随后提供LP缺陷必要条件C>=0，也可以排除这个顶角，但本三轮未更改域或删点。
第1轮(第二次solve)是目前较好的模型，best_solution完整保存其原basis A、reduced B、x和c；
末轮solution不是best，应优先使用best_solution。
第1轮worst约(-.96128020,.48713132,-.46373563)，Gram det .0578994，数值R=-.00006020640725。
全程独立原numeric design与多项式的差小于5e-15量级。
十阶总耗时351.50秒，bash195 exit0，已收集，没有追加SDP轮次或升更高阶。

## 新竞争三角条件下的独立验证

父线程提供C=U-B-sum(h11-p24)>=0的竞争必要条件；
validate_boundary_competitive_v1.py只在该域独立搜索，没有构造/证明这个条件或新求解。
使用50k随机、18k边界、12k反极邻域、多起点3D/2D SLSQP、3次seeded3D DE和3支2D DE。
较好模型的最小残差仍约-6.020640726166e-05，worst处C≈+.0050129，故该必要条件未排除真正worst。
C域random、boundary、near-antipodal中分别保留48718、16758、9974点。
数据为sharp_boundary_d10_competitive_best_validation.json，bash210 exit0，已收集。
域限制判断包含-1e-10浮点容忍，所有这些搜索都非严格证明。

## 可复算与文件

- 八阶脚本sharp_boundary_actualf_v2.py，结果sharp_boundary_actualf_d8_v2.json；
- 十阶脚本sharp_boundary_actualf_v3.py，结果sharp_boundary_actualf_d10_v3.json；
- 竞争条件验证脚本validate_boundary_competitive_v1.py及上述结果；
- 复算例：PYTHONPATH=proof_work:proof_work/python_deps OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 proof_work/sharp_boundary_actualf_v3.py --degree 10 --rounds 3 --out proof_work/NEW_NAME.json。
- 输出文件须新名字，脚本拒绝覆盖已有JSON。所有新文件均通过relative Path.write_text真实写入。

## 有限exact export（已完成，非负性待认证）

按父追加授权，将best_solution原basis A按1e-13对称有理化并加1e-10 I，Fraction LDL检查全部11块。
替换父conditional_h19_certificate.json的h19（在[-1,.56]精确满足0<=f-h<2e-7），
目标25.758，exact c=(target+3/2F111)/12，重建全部F、d、R和归一化恒等式。
这些精确分量通过仍不等于R>=0；父线程负责后续exact Bernstein全域认证。
脚本export_d10_best_rational_v1.py，输出d10_best_rational_target25_758_v1.json。


导出已成功完成，bash214 exit0，6.41秒；全部11块Fraction LDL正定，F有756项，R有786项。
独立全Gram[-1,.56]数值验证最低R=+0.00010503626754，
点约(.48713134,-.96128018,-.46373557)，Gram det≈.05789943。
原kernel设计与exact残差多项式数值交叉差<9.7e-16。
这提供全域严格认证的数值候选与margin，不构成R>=0的证明。
原数据status=exact_components_prepared_global_positivity_UNPROVED；父线程负责进一步Bernstein认证。

所有自启后台任务均已收集：bash186取消（八阶第5轮后停止）；bash189角度Jacobian检查exit0；
bash195十阶3轮exit0；bash210新竞争域独立验证exit0；bash214有理导出及数值验证exit0。
本子任务没有活跃后台任务，没有超过3轮十阶，没有升更高阶。

## 追加严格复核

父线程对导出模型完成严格Bernstein认证后，本线程以70bit Python object大整数、
无对称性剪枝（只用Gram负盒剪枝）独立复核25.758，14965节点、pending0，148.51秒。
报告d10_target25_758_object70_replay.json；脚本verify_d10_object70_replay_v1.py。
全部PSD/minorant/核重建/归一化重新精确检查。静态审查记录见high_degree_checker_static_review_zh.md。
这个严格结论显式依赖父线程已认证pair056条件，并与全域三点缺陷恒等式结合。
更强25.7592模型由父认证，本线程按追加授权仅进行第二份严格replay，不做新数值发现。

25.7592追加无对称object70复核预算耗尽（601.17秒），38026节点、pending15，
报告明确budget_exhausted，不能称其独立通过；25.758完整复核仍成立。
停止旧target额外replay，等待父新free-contact模型；新快object+sym版本仅限120秒。

## 最终新矩阵模型复核

父线程提供新的nonsharp_d10_rational_target25_7598_v1.json，
本线程以70bit Python object整数+精确对称剪枝+exact-sum细分复核成功，
3155节点、pending0、maxdepth31、39.95秒；报告
nonsharp_d10_target25_7598_object70_sym_replay.json，脚本
verify_d10_object70_sym_fast_v2.py。所有LDL/minorant/F/R/normalization重验通过。
显式外部依赖pair056已由父main完整重验。该下界仍不证明候选全局最优。
更强同核目标由父负责，本线程不重复逐级认证。
