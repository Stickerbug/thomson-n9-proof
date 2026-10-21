# 精确接触 Hermite 下界与 Stieltjes 余项因子

本结果构造势函数的下界多项式，并不证明任何九点全局最优性。与此前只逼近 f 的有理多项式不同，这里的系数是由真实驻点 r_* 及正平方根定义的代数数；程序保存这些系数的严格区间，而不是将端点当作精确接触系数。

取不同节点 t_j<1，每个匹配 f(t_j)、f'(t_j)，得到 2m−1 次 Hermite 多项式 H。f(t)=(2−2t)^(-1/2)，f'(t)=(2−2t)^(-3/2)。令 ω(t)=∏_j(t−t_j)²。以下等式给出精确非负余项：

\[
f(t)-H(t)=\omega(t)K(t),\qquad
K(t)=\frac1{\pi\sqrt2}\int_0^\infty
\frac{a^{-1/2}}{(a+1-t)\,\omega(a+1)}\,da>0,\quad t<1.
\]

证明：f(t)=1/(π√2)∫₀∞ a^(−1/2)/(a+1−t) da。对固定 s=a+1，函数 1/(s−t) 的 Hermite 插值为 [1−ω(t)/ω(s)]/(s−t)，因为右侧是 2m−1 次多项式，且在节点上匹配函数与导数。插值是有限个节点值与导数的线性组合，可在积分下交换，由此得到公式。分母均正，且 K 随 t 严格递增。

令区间为 [-1,14/25]。取区间外端点 L=−101/100、V=57/100，则

\[
0<K(L)\le K(t)\le K(V),\qquad
K(L)=\frac{f(L)-H(L)}{\omega(L)},\quad
K(V)=\frac{f(V)-H(V)}{\omega(V)}.
\]

即使节点包括竞争区间端点，这两个区间外评价也不会出现 0/0。K 的端点值用精确向外区间 Newton-Hermite 求值；节点分离也用区间证明。

实现 [contact_minorant_factor_v1.py](</home/dsh/Thomson Problem/proof_work/contact_minorant_factor_v1.py>) 使用 384 位 dyadic 区间，不依赖浮点求解器。它在 4096 个覆盖整个竞争区间的小区间上计算 ω 的上界，再乘 K(V) 的上界。

- 六个候选节点给出 11 次 H，认证一致误差上界约 0.000218754455。
- 六个候选节点，加上明确有理节点 −1,−9/10,−2/5,−1/5,1/10,9/20,13/25,14/25，给出 27 次 H。精确整数比较认证

\[
0\le f(t)-H(t)<\frac3{2\cdot10^9}=1.5\times10^{-9}
\]

覆盖全部 [-1,14/25]，实际保存上界显示约 1.485646778×10⁻⁹。H 在全部六个真实候选内积处精确接触 f,f'，候选接触等号来自 Hermite 定义，不能通过区间端点相等来检验。

结果见 [contact_minorant_factor_v1.json](</home/dsh/Thomson Problem/proof_work/contact_minorant_factor_v1.json>)。从项目根目录运行 `python3 proof_work/contact_minorant_factor_v1.py` 可复算。

后续仍需找到与 H 配合、全竞争 Gram 域非负的 R。即使 R_f 使用真实 f 的 Hessian 在接触点半正定，也不能直接推断 R_H：需减去 Σ(f−H) 的二阶项。在节点 t_j 上，f−H 的二阶导数为 2 K(t_j)∏_{i≠j}(t_j−t_i)²，这给出可精确界定的曲率修正。这里只认证势函数插值，不认证任何新的全局能量下界。
