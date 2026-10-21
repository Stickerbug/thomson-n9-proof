# 45 contact 行由33行推出的独立几何审查

结论：在下述已明确的解析基、非零pivot、驻点与非零33阶minor前提下，45行接触条件由所选33行严格推出。WM=0无需把45×190矩阵完整符号展开，也不依赖PSD；它来自固定核的圆谐矩消失。区间包含零仅是相容性核查，不能替代恒等式。

## 一、真实九点与features的精确含义

设0<r*<1，h=sqrt(1−r²)。六个prism点为(r cosθ,r sinθ,±h)，θ=0,2π/3,4π/3；三个cap点为(−cosθ,−sinθ,0)。两类anchor代表取a_p=(r,0,h)、a_c=(−1,0,0)。prism切平面正交基为e1=(h,0,−r)、e2=(0,1,0)；cap可取e1=(0,1,0)、e2=(0,0,1)。定义复矩向量

m_{a,k,i}(r)=Σ_{y∈X(r)}(y·e1+i y·e2)^k(a·y)^i，i=0,…,10−k。

自点在k>0时贡献0，在k=0时贡献1；不得丢掉k=0自点。prism关于xz平面反射使虚部矩为0，实部恰为h^(k mod2) p_hat；cap关于两个切平面坐标反射，虚部为0，奇k全矩为0，偶k实部恰为c。此处p_hat,c是candidate_low_rank.features的有理函数表达，而不是浮点anchor数据。附带小符号检查直接从九点坐标逐个求和，使用h²=1−r²化简，核对k=0..10的全部66个prism和66个cap分量。

候选的D3h正交对称群将每一类anchor互相映射。anchor切平面复坐标在正交变换下只多出单位相位或复共轭，因此矩消失可从两个代表推广到所有九个anchor。核列N_k满足p_hat(r*)ᵀN_k=c(r*)ᵀN_k=0；h≠0保证prism奇k缩放不引入异常。由此N_kᵀm_{a,k}(r*)=0对所有anchor成立。

精确构造依赖：singleendpoint kernel用QQ(r)的features行执行精确RREF以确定pivot模式，随后对同一有理运算在包含r*的区间上求值并认证所有除数非零。r0有理中点只用于选pivot，不能把N(r0)替代N(r*)。之后乘任何固定有理basis transform T1都保留两行湮灭性；浮点N相同的basischeck只支持数据坐标匹配，不单独证明代数湮灭。新certificate的真实保证来自该解析构造及pivot证据。

## 二、由圆谐矩到S=0与固定核的Sprime=0

固定A_k=N_k(r*) B_k N_k(r*)ᵀ，任意对称B_k即可，暂不需要PSD。原始circle kernel满足Q0=1，Q1=t−uv，Q(k+1)=2(t−uv)Qk−(1−u²)(1−v²)Q(k−1)；它是切平面复坐标k次幂乘积的实部。令F为六次置换平均后的三点多项式，则全有序和

S(r)=Σ_{a,y,z∈X(r)} F(a·y,a·z,y·z)

等于Σ_{a,k} Re[m_{a,k}(r)* A_k m_{a,k}(r)]。全有序求和对置换平均不变，故无需额外6因子。由于Nᵀm(r*)=0，S(r*)=0。更关键的是固定A、N、B在r*，只改变几何X(r)；对二次型求导得到两项，每项含A m(r*)或m(r*)* A，故Sprime(r*)=0。切平面基可在r*邻域平滑选择，r*∈(0,1)保证h光滑。这个论证不能替换为先令N=N(r)再微分的移动核论证。

## 三、84三角形、重复指标与7/6常数

记T_F=Σ_{无序互异三点}F，D_F=Σ_{无序点对}F(1,t,t)，J=F111。按三个指标的重复模式分解：

S=6T_F+6D_F+9J。

互异有序三点是6倍；恰两指标相同是每个无序点对6项；全同有9项。12个三角类型的multiplicity总和84，六个pair类型的multiplicity为(6,3,6,3,12,6)，三角边出现次数为其7倍(42,21,42,21,84,42)。

令M_value(x)对应7F(u,v,t)+F(1,u,u)+F(1,v,v)+F(1,t,t)+J/8，则

Σtypes w M_value =7T_F+7D_F+84J/8 =(7/6)S。

特别是84J/8=10.5J，与(7/6)·9J一致，没有遗漏常数。固定核、沿候选几何求导给Σw vel·grad M=(7/6)Sprime；J是固定F在(1,1,1)处的常数，导数0。

## 四、边界切向行与10个对称依赖

Gram g=1+2uvt−u²−v²−t²。三个恒等边界类型满足g(p(r))恒等为0，因此gradg·vel=0。脚本使用的两行是T_i=g0 ∂i−gi ∂0，i=1,2，其中g0是gradg第0分量。只要g0(r*)≠0，vel·grad M=Σ_{i=1,2}(vel_i/g0)T_iM。必须保留此非零分母条件；不能把所有Gram边界点都假定此坐标图有效。本候选三种边界的g0由小符号检查给出，均在root邻域非零。

完全对称的M和rhs在重复坐标处梯度分量相等；内部类型给出相应差行，DDD切向两行各自为0，另两个边界类型因后两坐标重复而两切向行相等。这给10个对称依赖。加上加权值、几何导数两行，组成W(12×45)。已存minor精确为−36r，r*>0故rank W=12。

## 五、右端兼容性与rank夹逼

rhs值行为Σ f−E*/12，内部梯度行为fprime，各边界按同一g0/gi转换。对称依赖消去rhs；加权值给7E*−84E*/12=0；加权梯度给7Eprime(r*)。最后一项严格为0需要已认证r*是候选能量的驻点，不是仅用狭窄区间把Eprime包住0。

旧geometry小脚本的5个独立势值表示使用f(D)=r f(A)，此式来自f(t)=1/sqrt(2−2t)、r>0及D=−1/2、A=1−3r²/2；不能不声明分支条件。该脚本精确验证first11=0、last=7Eprime。

因为WM=0且rank W=12，rank M≤45−12=33。新exact certificate的33个LU pivot均区间排除0，证明选出的33×33minor在r*非零，因此rank M≥33。于是im M=ker W。驻点保证Wb=0，故b∈im M；所选33行在im M上限制为单射。任何满足这33行的x都有Mx−b∈im M且其33个选中分量为0，因而Mx=b全部45行成立。无需另假设未选12行可由W某个固定方阵直接求解。

## 六、明确的证明边界

本审查补足的是接触行依赖与rhs兼容性。它依赖已认证根r*的驻点性、解析features核及非零pivot、正确84/36计数、W的非零minor、选中33阶minor的非零LU；不从interval residual包含0推出exact identity。不证明global R≥0，不证明候选能量全局最小。PSD、局部Hessian、远离contact全域覆盖是独立后续条件。新certificate的scope在此前提链下成立；basischeck的PREPARED标识不能误读为其本身已完成exactification。
