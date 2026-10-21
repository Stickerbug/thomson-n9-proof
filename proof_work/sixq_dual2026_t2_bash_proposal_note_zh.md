# T2 有限样本 pair PSD proposal：失败归档

本次没有得到连续域下界，没有新增 Thomson 全局证书。只运行一次数值 SDP，结果明确在独立样本上失败，因此停止该分支。

取 v(q)=(x,y,z,xy,xz,yz,x²−y²,3z²−1)，d(q)=v(q)ᵀAv(q)，α=0。样本约束为 W(q,r)≥v(q)ᵀAv(r)+(d(q)+d(r))/10+β，A⪰0。程序将 W、A、β统一乘以100000。

对六点，Σ(i<j)[viᵀAvj+(di+dj)/10]=½(Σvi)ᵀA(Σvi)≥0。故只有当 pair 不等式在完整允许连续域上成立并严格认证 A⪰0时，才能推出 Σ15W≥15β。有限样本优化不满足这个前提。

2201训练pair（包含原T2极小见证），CLARABEL optimal_inaccurate，20iter，总2.215098958秒。训练最小残差scaled为+1.875648579e−6；beta=.0005402453478625353。A的scaled trace=999.9999854546336，触及上限1000；scaled最小特征值为−2.4073893166873134e−8，PSD也没有严格认证。

5000独立允许pair中53个违反，最差scaled残差−152.5475479746364，即真实残差−.001525475479746364。完整矩阵和最差见证保存在sixq_dual2026_t2_bash_proposal.json。这是过拟合的proposal，不是global bound，不是Thomson反例，也不证明此dual族不可行。没有追加cut或重新求解。

实际脚本：sixq_dual2026_t2_bash_proposal.py。bash-800 exit0且已收齐；此前bash-782 exit127（python不存在）、bash-784 exit2（write backend ghost文件不存在），都未进行优化。没有未收job。实际脚本由bash open(x)落盘并确认，原sixq_dual2026_t2_sample_psd.py的write回执不可作为成果依据。

纯静态审查：t2_unary_screen2026.py的D^27齐次化、threshold upper系数扣除、lower Bernstein向下split、anchor坐标扰动18 deriv/Q及保留low_pending的方向一致；t2_unary_leaf_pair2026.py对负b使用D_min给phi≥TAU+b/(2^bits D_min^27)的方向正确，clipping到0依赖旧R几何非负证书。后者仅收集low_pending而跳过budget_pending；在任何完整覆盖用途前，应断言源文件无budget_pending，否则超时未处理域会漏掉。未重跑这些验证器。
