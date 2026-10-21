# d12 restricted必要域纯τ有限实验结果

三轮均正常结束，未获得全必要域非负残差。不是n9反例、不是SDP不可行证明，也不是全局证明。严格LB25.7599205未变。

域仅针对GLOBAL MINIMIZER：所有内积≥−.9957且≤.56、Gram≥0、当前旧残差R_old≤7(U−25.7599205)。下界限制依赖驻点性，不适用于所有竞争构型。旧模型来源为nonsharp_d10_root25_7599205_v10.json，target=51519841/2000000，残差807项，SHA256=6ebdebad61e4ba26f044b07b2ed56bcacdfe8c584b6007561bc17b2cd23b52d0。父另一个理论整理首版误读旧25.745残差；本数值驱动始终读取上述当前模型，不受来源误配影响。

目标纯min tau_scaled=1e6 tau，无trace罚，trace<=5000，各非空B>=1e-7I，正确内部/边界localjets。d12 322变量、39行rank32、45行rank33。seed frozen batch1 iter2。Dred/bred预计算；active4500，所有必要域内历史与新发现点永久保留。

|轮次|τ|trace|minEigB|搜索原A minR|CLARABEL秒|验证秒|
|---|---:|---:|---:|---:|---:|---:|
|1|4.69343e-18|756.16675|1.73888e-06|-0.145110134465|46.831|2.202|
|2|1.03328e-17|1189.3178|1.62968e-06|-0.00564286179176|40.110|1.623|
|3|1.57705e-17|1134.048|2.92261e-06|-0.00654595936958|38.019|1.199|

全部CLARABEL均optimal。build45.4897秒，总225.0199秒，未新增第四轮。最后接触误差7.7438e-14，原A/compiled值差6.3366e-14、directdesign差2.3981e-14。575个域内已发现/mandatory/固定点已逐轮原A交叉复核。旧字段independent_minimum只是兼容名称，随机/DE/SLSQP完全共享compiled，未声称独立搜索。

最后搜索点在LOW边界及旧预算边界。简单朝原点内推会越过旧预算，不能称严格域内；专门随机小方向找到并用Fraction精确检查的严格域内点如下。
- iteration0: [-0.9956999584876705, -0.04636892204153277, -0.04636753561144894], originalA R=-0.1451100316625551, Gram=3.237687065699902e-08, oldbudget slack=0.00021428834055968576，全部严格域不等式精确为真。
- iteration1: [-0.9902919524282854, -0.6002268060217666, 0.48322112011797674], originalA R=-0.0056428517025777225, Gram=3.012113450234251e-08, oldbudget slack=3.03885814853147e-09，全部严格域不等式精确为真。
- iteration2: [-0.9956998397982685, -0.0025253131091771534, -0.0025239243541001852], originalA R=-0.006545938331891321, Gram=0.008556389042597656, oldbudget slack=3.4730954457648265e-10，全部严格域不等式精确为真。

负值仍是浮点originalA数值复核；Fraction只认证有限小数点的域成员性，不将数值A当exact证书。所有originalA/N/B/x/c、原始cuts、rank、solverstats在results.json；audit.json与strict_negative_points.json保存交叉复核和精确域算术。results SHA256=c31e2ff1fbdc103eb8e7f8157c22299203c89e963e8e93767516abb59473f607；最终A canonicalJSON SHA256=d222671404297a204b136309fbec66a08eb8d03fc85b565d78787d597053c66a。

诊断：pureτ在训练点已几乎为0，未选择小trace解，trace约756→1189→1134；有限搜索最差值先改善后回落，可能体现欠采样及最优面选点造成的振荡，不足以推断有限维模型不可行。后续可设计lexicographic目标：先minτ，再固定τ<=1e-10 mintrace。本轮未启动该后继求解，不盲续相同batch。

后台状态：新restricted job895已job_output收齐exit0；准备893与audit900/901也已exit0收齐。旧fullGram job867仍unknown，未触碰、未伪称停止或完成。父继续全局证明目标，本有限实验结果仅供后续方向决策。

## 后继设计：对小盒的 affine Bernstein 系数施加线性约束

本节仅为设计，没有启动新求解。三轮有限采样失败不表示三点SDP方法不可行。一个实质不同的约束生成方式是：对多项式minorant h27形成 R_h=sum h27−7F−sum diagF−c。其单项式系数线性依赖A/c，因此任意固定小盒Q上的任意Bernstein系数 b_(Q,i) 也是这些变量的仿射函数。若一个盒上全部Bernstein系数非负，便控制整个盒上的R_h，而不是只控制有限采样点；由h27<=f可推出该盒上真实R>=0。

具体oracle：固定必要域的自适应盒划分，对当前数值A寻找最负的Bernstein系数；只把该盒及multiindex对应的一条仿射不等式加入SDP，永久保存box、multiindex、degree、归一化尺度和row来源。求解后重新检查已有盒的全部系数，负系数过多或过于保守时细分盒，而不是把一个负系数当作真实负残差或不可行证据。只有最终覆盖所需域且每盒全部系数非负，才具备覆盖证明的结构；少量选中系数非负本身不是全盒认证。

无需一次构建322×28³之类的全参数tensor。设Q第j轴为[a_j,a_j+w_j]，统一tensor degree为n_j；单项式x_j^alpha对第i_j个Bernstein系数的变换权重是 sum_(k=0..min(alpha,i_j)) binom(alpha,k) a_j^(alpha-k) w_j^k binom(i_j,k)/binom(n_j,k)。三轴权重相乘，对稀疏单项式线性row收缩即可导出所选(Q,i)的一行；n_j应由实际R_h逐轴次数决定，不盲假设为27。再以现有A=NBNᵀ、x=sol+Zfree消元形成真正求解器row，可缓存盒的一元变换及选中row，分块扫描oracle，避免完整高阶参数tensor的内存成本。

域覆盖与接触处理是关键限制。Gram或旧预算C=7gap−R_old的区间/Bernstein严格上界小于0时，才可排除整个域外盒；跨越可行边界的盒需细分或在更大盒上直接证明，不可凭中心点删盒。LOW和上界的轴盒约束可直接裁剪。为了让h27多项式约束保持可行，必须暂不对候选接触的邻域施加上述h27盒约束：真实sharp contact处R=0，而一般f−h27>0会使R_h<0，导致人为不相容。删去的接触邻域是待补证明区域，不能从全域目标中消失。最终应在true-root algebraic contact及正确法向/切向几何下构造contact适配的H或局部真实势能界，并以严格局部Hessian/边界曲率证书覆盖这些邻域，再与盒覆盖拼接；不得把近似r或浮点零误差当作exact contact。

Conditioning与volume成本需实测：高次power-to-Bernstein变换存在大二项式系数、相消及小w幂，trace约1000会放大row误差；可采用局部移位缩放、按row范数和可验证正尺度归一化、必要时高精度生成，再用有理/向外舍入重新验证。靠近Gram曲面、旧预算曲面和接触邻域的盒数量可能爆炸，tensor-product Bernstein也会在细长可行域外引入过强约束；可选各向异性细分、几何优先划分及保留严格域外排除证据。数值oracle只负责提案，最终所有系数正性、域外排除及接触邻域覆盖仍需严格算术。该方向与继续随机点或仅调trace目标不同，目的在于用体积控制约束高阶多项式振荡。

