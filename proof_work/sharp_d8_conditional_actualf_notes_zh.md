# 八阶条件Gram域、解析接触与实际Coulomb rhs实验

本文件记录六阶实验完成后父线程明确授权的最后一组八阶测试，最多3轮，未升十阶。所有结果为NONRIGOROUS数值诊断，尚无最优性证明或Thomson反例。

## 范围与构造

范围为Gram PSD与[-1,.57]^3的交集。它作为完整证明的一部分，必须另接父线程已严格证明的竞争构型pair-exclusion，脚本不自行证明此前提。
Nk来自Fraction候选r近似的精确feature nullspace，再QR数值正交化；八阶零空间维数[7,7,5,5,3,3,1,1,0]，100个独立对称矩阵变量。
与旧eigenbasis投影的交叉误差小于3.6e-12。39条候选接触值与9个Gram内部三角梯度方程数值rank32，留下68维自由参数。
使用精确有理原始核多项式字典，数值投影，按单项式解析求导；禁止有限差分，确实未使用。
候选rhs与训练/验证rhs都采用实际f(t)=(2-2t)^(-1/2)，候选梯度采用f'(t)=(2-2t)^(-3/2)。这不是多项式minorant证书。
trace<=10000是附加实验限制。

## 初始求解器故障与修复

sharp_d8_conditional_actualf.py第一次启动时，PSD接触mintrace解trace3.51480686、contact误差3.06e-11、minEig=-2.79e-10；但第0轮采样问题CLARABEL抛SolverError。原始JSON保留，history为空，不能当作采样结果。
新独立脚本sharp_d8_conditional_actualf_eliminated.py使用x=x0+Zz消去39条等式（SVD rcond1e-10），从而避免冗余等式导致的数值故障；没有覆盖初次结果。
该脚本mintrace解trace3.51480693、contact误差3.77e-15；它与各round均数值落在PSD边界附近，有小负特征值，不是严格PSD认证。
脚本设置CLARABEL失败时有限SCS fallback；这次3轮实际均由CLARABEL完成，status均optimal_inaccurate，没有进入SCS。

## 三轮结果

初始1000个条件随机点，加条件Gram边界、7x7x7 cube的Gram可行子集及候选点，合计1360训练点。
每轮30k新条件随机点，取worst80加入下一轮，再两次DE。DE用random worst和条件角点播种，惩罚第三坐标>.57，另记录真实残差和可行标志。

|轮|训练数|tau|trace|contact最大误差|PSD最小特征值|random最低|DE最低|
|---|---:|---:|---:|---:|---:|---:|---:|
|0|1360|.001211563556|270.16896|8.89e-14|-6.45e-9|-.00488358066|-.00604558297|
|1|1442|.001577716357|429.74691|1.16e-13|-1.33e-8|-.00223441195|-.00226980450|
|2|1524|.001728222306|489.84724|1.37e-13|-1.52e-8|-.00189454137|-.00194063169|

第0轮DE明确找到(.1875804686,.57,.1875789790)，R=-.00604558297。
最终DE明确找到(.4654922366,.2188732080,-.7617086021)，R=-.001940631691，theta≈3.141591316，属于Gram近退化边界且各坐标<=.57。
最终另一盆地(-.2154064377,.2078907056,.2078902869)，R=-.001871809016。
独立原numeric kernel/design与字典计算交叉差至多9.37e-14，远小负残差。
条件测试点(-1,0,0)最终R=-.001728175979，故这个点本身已经否定该数值核的全域非负性；(−.5,−.5,−.5)候选接触误差约5e-14。

## 解释与限制

相较六阶h11条件模型tau约.809，八阶actual-f模型明显增强，但仍没有达到tau=0，也不是数学不可行性证明。
父线程已另外精确证明在[-1,.57]原有有理h11误差f-h<.0003，从而每三角改善小于.0009；固定六阶核的约-.809违例不可能仅靠改善h修复。
八阶当前固定核的最终actual-f残差仍为负；任何h<=f只会让同一核的残差更低，故提高minorant阶数也无法修复该固定核。新的核或新模型仍可能成功，当前实验未排除。
未自动追加轮数、没有条件h11八阶重复运行、没有full域八阶或十阶运行。

## 文件、复算与job

脚本sharp_d8_conditional_actualf_eliminated.py，完整模型和所有round数据sharp_d8_conditional_actualf_eliminated.json。
初始失败但保留接触feasibility结果：sharp_d8_conditional_actualf.py及sharp_d8_conditional_actualf.json。
复算环境：OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONPATH=proof_work:proof_work/python_deps python3 proof_work/sharp_d8_conditional_actualf_eliminated.py。
为避免覆盖，脚本遇已存在同名JSON会assert；复算需在新副本改输出名或由用户自行保管旧输出后另行运行。
bash-140 exit1（已调查求解器错误），bash-144 exit0，总耗时48.79秒；两者已job_output收齐，无此子任务活跃job。
