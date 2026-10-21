# T2/T3 两外点场 W 的有限数值策略审查

本轮不运行 SDP，只评估固定 T2/T3 下旧全局证书的807项精确有理残差多项式。有限搜索没有找到 W<K/15 的可行点。两例均显得值得做严格化试探，但所报最小值都是 inf W 的数值上界，不能当作全域下界。

设固定锚点 a,b,c，外点 q,r∈S²；要求所有锚点—外点内积及q·r均<=0.56。锚点使用固定三角的代数单位向量嵌入。数值实现以球面角参数保证外点单位长度。

φ(q)=R(a·b,a·q,b·q)+R(a·c,a·q,c·q)+R(b·c,b·q,c·q)。

ψ(q,r)=Σ_{x∈{a,b,c}} R(x·q,x·r,q·r)，W(q,r)=(φ(q)+φ(r))/5+ψ(q,r)。

六个外点共有15对，每点出现在5对中，因此 **Σ₁₅W=Σ₆φ+Σ₄₅R**。旧84个三角残差预算在扣除锚三角后为K；20个全外点三角残差非负。若能严格证明W>=m且15m>K，即可排除该固定T。仅有15m=K时还需额外严格正项。

| T | 最小已见可行 W（longdouble复算） | K/15 | 差 W−K/15 | 比值 | 累计数值秒数 |
|---|---:|---:|---:|---:|---:|
| T2 | 7.8053715942608e-05 | 3.0060029039018e-05 | 4.79936869036e-05 | 2.59659483 | 25.02067 |
| T3 | 3.5585437406128e-05 | 3.0294539840894e-05 | 5.29089756523e-06 | 1.17464855 | 16.61596 |

以下是最终保存的可行点。最小分离余量为0.56减去七个锚点—外点/外点—外点内积的最大值，均离边界有明显余量。

- T2：q=(-0.6566493494106734, 0.6252948997518299, 0.4216846218003313)，r=(0.3590463678817005, -0.8326269266782423, 0.4216848428403651)；φ(q)=0.00012871604186，φ(r)=0.000128716087023，ψ=2.65672901659e-05，最小分离余量 0.200953632118；float与longdouble的W差 2.53e-17。
- T3：q=(0.261879722069442, -0.7363518167644375, 0.6238629762348012)，r=(-0.7542824187464141, 0.2185623501871951, -0.6191030058485495)；φ(q)=3.31945418811e-05，φ(r)=3.78393653133e-05，ψ=2.13786559672e-05，最小分离余量 0.198453649124；float与longdouble的W差 5.87e-17。

数值过程：复用既有单点φ井作为初始外点对，再加入随机可行对，做SLSQP和有限DE；最后只对已得最优可行点用较小目标尺度局部精修。若SLSQP返回不满足分离约束的点，即使其W很低也不纳入最优值。原始history中有负到约−1的不可行返回值，不能误当成W反例；那是在pair>0.56、旧多项式无需非负的区域。

首次T2运行在结果打包阶段发生 `KeyError: W_longdouble`，原因是梯度有限差分检查更新了best并替换掉先前附加的验证字段；已冻结best后验证。首次20.864秒计入T2预算，修复运行只允许T2再8秒，T3最多30秒；最终连同现有点精修的累计数值时间分别见表，均小于30秒。失败日志保留，未把失败当作核障碍。

这些数值不保证搜索充分：T3的DE在80迭代未收敛，其已有最优点的局部精修成功；T2修复归档阶段使用剩余预算，保留其局部可行最优。float/longdouble一致只检查评价误差，不构成区间证明。

建议优先做小预算严格化试探，而非继续加数值SDP。T2观察余量约4.80e−5/对较大，T3约5.29e−6/对较小。可先严格定位低φ区域：若已知全域φ>=M，当φ(q)>=K/3−M时，凭ψ>=0即有W>=K/15，因而只需细查两个点都处于低φ区域的外点对。注意M必须是严格全域下界；本轮没有提供这样的M。

若uniform W下界最终被新反例否定，可保留空间势α与容量，而不丢回六点独立φ松弛。乘数匹配方式：

> 若对每个可行外点对 W(q,r)>=β+(α(q)+α(r))/5，并另有六点容量证书 Σ₆α>=Lα，则 Σ₁₅W>=15β+Lα。需15β+Lα>K。

等价地，对φ(q)+φ(r)+5ψ(q,r)建立α(q)+α(r)+5β下界。α可取分区/帽上的有理常数；容量条件必须另行证明。另一形式是对分区P_i×P_j分别证W>=w_ij，再对Σn_i=6和严格容量约束最小化Σ_i C(n_i,2)w_ii+Σ_{i<j}n_in_jw_ij。分区必须覆盖可行球面，不能仅使用有限φ井。

本轮仅提供策略建议，没有证明任何W下界、九点延拓排除或新的Thomson能量下界。

文件与复现：

- [有限probe源程序](</home/dsh/Thomson Problem/proof_work/external_pair_field2026_probe.py>)。
- [剩余预算内现有点精修源程序](</home/dsh/Thomson Problem/proof_work/external_pair_field2026_polish.py>)。
- [修复后的原始搜索记录](</home/dsh/Thomson Problem/proof_work/external_pair_field2026_data.json>)。
- [最终可行点与预算记录](</home/dsh/Thomson Problem/proof_work/external_pair_field2026_polish.json>)。
- [紧凑策略摘要](</home/dsh/Thomson Problem/proof_work/external_pair_field2026_summary.json>)。
- [初次失败日志](</home/dsh/Thomson Problem/proof_work/external_pair_field2026_probe.log>)。
- [修复运行日志](</home/dsh/Thomson Problem/proof_work/external_pair_field2026_retry.log>)。

模型及三角来源：

- [旧807项R精确模型](</home/dsh/Thomson Problem/proof_work/nonsharp_d10_root25_7599205_v10.json>)，SHA256 `6ebdebad61e4ba26f044b07b2ed56bcacdfe8c584b6007561bc17b2cd23b52d0`。
- [T2/T3与φ井](</home/dsh/Thomson Problem/proof_work/two_other_valleys2026_probe.json>)，SHA256 `c8f1d7b62403ca80de6698c2855efc50345581ec383b571260a6502c529642c2`。

在工作区 /home/dsh/Thomson Problem 下，复现数值probe可换新PREFIX以保留旧输出：

```bash
PYTHONPATH=proof_work:proof_work/python_deps OPENBLAS_NUM_THREADS=1 python3 -c "import external_pair_field2026_probe as m; m.PREFIX='external_pair_field2026_replay_'; m.main()"
```

当前源程序保留修复后预算配置：T2使用8秒、T3使用30秒，并记录历史T2失败用时。重放不会生成精确下界。两个后台job均已收齐：711 exit1、715 exit0；现无活跃job。
