# 高阶条件三点验证程序静态审查

审查对象：verify_high_degree_conditional.py、exact_tensor_bernstein.py，及其调用的
certify_three_point_d4.py的diag/ldl、certify_d4_int64.py的safe_array/split64、
certify_conditional_h19.py的check和pair056_optimized_certificate.json。
未重复父线程40bit认证、未运行更强target、未新增SDP。

## 结论

未发现本次25.758模型的数学归一化、域变换、剪枝比较或int64溢出漏洞。
下面结论依赖普通Python非优化模式（assert有效）与明确的pair056外部证书。
静态审查本身不是独立实现形式化证明。

## 核与计数

Q0=1，Q1=t-uv，Q(k+1)=2(t-uv)Qk-(1-u²)(1-v²)Q(k-1)，
对应S²横向二维的rho^k Chebyshev T_k核，按anchor求和给半正定矩块；
原basis A全部Fraction LDL严格正定，故总有序三指标核和S>=0。
程序逐k/i/j重构原basis核，六排列平均，验证保存的F多项式相等。
diag正确把F(u,v,t)映成F(1,z,z)：指数为原第二与第三指数之和。
若T是全部无序异点三角F之和，D是无序点对d之和，则
S=6T+6D+9F111。R=sum h-7F-sum d-c，因此
E-B=sum_pairs(f-h)+(1/7)sum_tri R+(1/6)S，B=12c-(3/2)F111。
验证程序的-7F、三个-d以及target归一化均正确。

## 域与外部条件

域固定[-1,14/25]^3；其2x2 Gram主子式已非负，det>=0等价完整3x3 Gram PSD。
每个满足E<=U的九点构型，由已认证pair056条件必落入该域；
E>U时由target<U自动有E>target。这个逻辑不需要U本身是候选能量的严格上界，
只需要pair056对完全相同的有理U成立。
当前checker U与pair056证书U完全相同。
建议checker读取pair056证书并显式比对U、报告外部依赖，不只输出字符串宣称无条件。
本检查器本身未重验pair056的Legendre/Bernstein部分。

## 精确张量变换

第k个Bernstein系数对输入x^i的精确变换为
T[k,i]=sum(j=0..min(i,k)) binom(i,j) lo^(i-j) width^j binom(k,j)/binom(n,j)。
这是先x=lo+width*z，再单项式z^j转Bernstein的正确公式。
每轴取共同分母、转Python int object张量收缩，分母逐轴相乘，全程无float。
最终floor(v*2^bits/denom)给下界；-floor(-v*2^bits/denom)给上界，对负数也正确。
代码的reshape/moveaxis保持轴对应，Gram与R可用不同次数但按同轴分割同一盒。

## 整数盒与溢出

每轴box端点表示为integer/2^ds，起始[-1,1]，分割端点(2l,l+r)/(2^(ds+1))等正确。
共同正仿射变换到[-1,.56]保持坐标顺序，因此可在归一化盒上做对称性剪枝。
比较l0<<ds1与r1<<ds0是精确交叉乘法，负端点也正确，Python整型无移位溢出。
R对排列对称，域也对称；仅覆盖u<=v<=t的区域足够。
只在Gram上界系数全负时剪掉盒，保留det=0边界，逻辑保守。

safe_array验证初始所有整数系数abs<2^60。
整数floor/ceil平均均不超出参与平均整数的最小最大值，所以所有后代仍在初始整数极值内。
于是两数相加abs<2^61，取负也不触及-2^63，split64在int64内安全。
下界用floor平均、上界用ceil平均，逐层舍入维持正确包含。
70bit object独立replay取消int64与对称剪枝，可额外交叉核查这两处实现选择。

## 加固建议（非当前证书发现的反例）

1. 入口显式拒绝__debug__为False，防止python -O/PYTHONOPTIMIZE静默移除所有assert。
2. 将pair056的status/U和路径纳入验证报告，或提供一键串联其exact重验。
3. 通用coefficients可增加box lo<hi、bits非负、指数非负且不超degree的输入检查；
   当前调用由固定精确重构的多项式生成，因此不影响本模型结果。
4. 真正独立实现仍比同一exact tensor helper的复跑更强，报告应明确共享依赖。

70bit object/no symmetry复算已成功：d10_target25_758_object70_replay.json status=certified，
14965 nodes、3876非负叶、3607 Gram负叶、pending0、maxdepth27，耗时148.51秒。
本次用70bit Python object大整数、没有任何对称性剪枝，也没有int64转换，
复算全部Fraction LDL、h minorant、原basis核、F/R与归一化恒等式。
与父40bit int64+symmetry版本相比，这独立核查了不同整数载体/精度/剪枝选择；
它仍共享exact_tensor_bernstein变换与若干多项式辅助函数，不是完全独立实现。
随后按父追加授权，对已认证的25.7592模型进行相同复算（新report名），不探索更高目标。

## 追加复核与有限预算

25.7592无对称object70 replay达到600秒预算，status=budget_exhausted，
38026 nodes、9635非负叶、9371 Gram负叶、pending15、maxdepth34，601.17秒。
报告d10_target25_7592_object70_replay.json。该复核不完整，不能称通过，未重跑该昂贵任务。
25.758完整无对称独立复核继续有效。
父最高25.75925是父int64验证结果，本子线程未独立复核其全域残差。

父main已实现__debug__guard、pair证书U相等检查和runpy执行完整pair056 checker，
且verify_pair056_saved.py是顶层执行，不存在__main__ guard跳过验证问题。
先前两项安全加固建议已确认修补。

准备的新verify_d10_object70_sym_fast_v2.py在object70中保留精确对称剪枝，
用整数deCasteljau直接相加，直到每层输出边界系数时才除2^j向外舍入。
单变量半区Bernstein显式公式为
L_j=2^-j sum(k=0..j)binom(j,k)b_k，
R_j=2^-(n-j)sum(k=0..n-j)binom(n-j,k)b_(j+k)。
任意已外向包含的输入Bernstein整数向量经这些非负系数矩阵仍外向包含，
所以不需要中间每个row元素除2，而最终边界系数floor/ceil仍安全并更紧。
随机正负90bit整数、shape(3,4,5)、全部3轴和上下界共17280系数，
与独立Fraction显式二项式公式完全一致。
该快版本尚未运行新的全域认证，等父新模型，只授权最多120秒。

## 新矩阵模型25.7598的完整object70复核

按父线程追加授权，使用新模型nonsharp_d10_rational_target25_7598_v1.json，
只运行一个新target，不跟逐级目标、不增加SDP。
verify_d10_object70_sym_fast_v2.py在39.95秒完整认证：
3155节点、798非负叶、549 Gram负叶、231对称排除叶、pending0、maxdepth31。
节点计数与叶计数满足3155=2*(798+549+231)-1，完成整个二叉分割树。
报告nonsharp_d10_target25_7598_object70_sym_replay.json。

此路线使用70bit Python object整数、精确Fractions重构和新exact-sum细分；
取消父int64载体，以正确的精确对称剪枝完成有限复核。
所有11块原basis A、h minorant、F/R重构、target归一化均重新检查。
独立显式Fraction二项式参考测试已扩充至20304系数，含20次Bernstein轴；
可执行测试脚本check_object70_fast_split.py。
它仍共享exact_tensor_bernstein及部分代数辅助函数；不应描述为完全独立代码实现。
pair056是明确外部证书依赖，父main已串联完整重验。

复现命令：
PYTHONPATH=proof_work:proof_work/python_deps OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
python3 proof_work/verify_d10_object70_sym_fast_v2.py \
--model proof_work/nonsharp_d10_rational_target25_7598_v1.json \
--out proof_work/nonsharp_d10_target25_7598_object70_new_replay.json --seconds 120 --budget 100000

脚本拒绝覆盖已有report，复算请使用新的输出名字。
所有本线程后台任务均收集完成。最终独立复核范围：旧模型25.758无对称成功；
旧25.7592无对称预算耗尽；新模型25.7598有对称大整数成功。
较高目标若由父同核int64认证，应明确与本线程复核范围区分。
