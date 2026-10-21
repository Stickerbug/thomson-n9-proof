# Hermite minorant的纯代数商证书

结果：Q(t)在整个[-1,14/25]上的28个初始Bernstein系数均严格为正，单叶完整覆盖，pending=0。无需Hermite余项的28阶导数符号定理。

设真实14个互异节点为xi，所有xi<1；fi为正平方根(2−2xi)^(−1/2)。独立Hermite插值定义次数至多27的H，数据为H(xi)=fi、Hprime(xi)=fi³。导数数据是代数指定值，不要求从微积分导出fprime。令G=1−(2−2t)H²，W=Π(t−xi)²；G次数至多55，W次数28且monic。

在每个节点，G(xi)=1−(2−2xi)fi²=0。形式多项式导数给Gprime=2H²−2(2−2t)H Hprime；代入得到2fi²−2(2−2xi)fi⁴=0。因此每个(t−xi)²精确整除G，且各因子两两互素，故W精确整除G，存在唯一次数至多27的实系数商Q。此处系数域可取包含r*、14个fi及所有非零节点差逆元的实代数扩张。

实现使用publication_validation自身的640bit signed-integer outward Box，未import旧I384/helper/native。重新从根区间和6candidate+8rational节点构造confluent Hermite并检查全部H包围包含于已绑定H包围。构造W与G后进行monic长除：最高项系数就是商项，减去该项乘W，次数严格下降。最高项设为精确0来自monic同项代数抵消，余下系数按独立interval运算包围。保存的最终28项余项包含0只作一致性检查；精确余项为0的证明是上面的多项式整除论证。

将t=−1+(39/25)s代入Q，转换到degree27 Bernstein基。系数公式b_i=Σ_{j<=i} a_j binom(i,j)/binom(27,j)，其中a_j是Q的仿射代入后power系数。每个真实b_i包含于独立区间。初始28个系数下界均为正，因此Q>=0于全域。完整domain tree只有空地址root叶，深度0，精确dyadic测度1，无pending。实现也支持de Casteljau二分，完整保存每叶Bernstein系数及pending；未完成时状态不可能PASS。

W>=0由平方因子，故G=WQ>=0。域内2−2t>0，于是( sqrt(2−2t) H(t) )²<=1，从而sqrt(2−2t) H(t)<=1；除以正平方根得H(t)<=f(t)。不需要H>=0，不需要高阶Hermite余项calculus。

独立控制样例：Q=−1和有负内部谷的(t−1/8)²−1/100均被拒绝且保存严格负点；(t−1/8)²+1/100接受。controls.json保存结果哈希及Bernstein系数全局界。result.json保存28项H、29项W、56项G、28项Q、长除余项包围、完整单叶证书、节点、sourcehash和selfhash。结果未证明R_H非负、局部或远域树，也未单独证明Thomson全局最优。

本证书仍依赖独立Hermite插值存在唯一性/指定导数数据的代数定理、真实r*与节点定义、互异节点差非零、Box运算正确性及Bernstein基非负性；这些依赖均是有限代数/序域论证，不以区间包含零替代精确等式。

结果SHA256：6f9c1a1356fd30e612a2581522ba929c3592f790267abd8b131c20ac2ed22ebc
