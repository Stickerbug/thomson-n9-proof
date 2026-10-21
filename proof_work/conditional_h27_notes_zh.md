# 条件Coulomb势的27次有理minorant

已严格证明，对每个 t∈[-1,14/25]，f(t)=(2-2t)^(-1/2)，
0<=f(t)-h27(t)<1/100000000000=1e-11。
全部28个单项式系数为精确有理数，保存于conditional_h27_certificate.json。
这是势函数逼近证书，不是新的九点全局最优性证明。

## 发现与信任边界

certify_conditional_h27_decimal.py使用100位Decimal算术，在28个Chebyshev零点插值。
cos由Taylor级数计算，DCT及Chebyshev到t单项式转换都不经过double。
区间变换z=(50t+11)/39。最终系数向最近分母1e55有理数量化，并将常数下移5e-12。
Decimal、pi常量、插值误差估计都不是证明所信任的假设：只有最终有理系数进入精确验证。
27次已经超过要求，因此没有继续升至31次，也没有新增SDP。

## 精确证明

令s=2-2t>0、eps=1e-11。全Fraction Bernstein细分严格证明：
1. h27>0，1节点；
2. 1-s*h27²>0，5节点；
3. s*(h27+eps)²-1>0，5节点。
第一、二项推出0<h27<f，第一、三项及eps>0推出h27+eps>f。
三个严格不等式均覆盖整个闭区间，包括端点。
生成时精确认证耗时0.477秒；只读取保存系数的exact-only verifier再次复核0.478秒，
节点数完全一致；结果conditional_h27_verified.json。
该复核共享简短Fraction Bernstein函数，但不运行任何插值/Decimal发现。

## 可复现命令

PYTHONPATH=proof_work:proof_work/python_deps OPENBLAS_NUM_THREADS=1 \
python3 proof_work/verify_conditional_high_degree_saved.py \
proof_work/conditional_h27_certificate.json --out proof_work/conditional_h27_new_verified.json

脚本拒绝覆盖已有输出，因此重验时使用新report名字。
生成器certify_conditional_h27_decimal.py --degree 27默认拒绝覆盖证书；无需为复核重跑发现。

## 后续使用范围

九点的36个无序点对因势函数替换造成的总误差小于36e-11=3.6e-10，
比旧h19的2e-7单对误差上界小20000倍。
这不自动提升原三点证书的全局下界；替换h后必须重建并严格验证残差。
父线程的当前主模型可继续使用h19，h27供更小缺口时使用。
