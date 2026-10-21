# 第二有限批次：竞争域 cuts 与低 trace，discovery only

父线程在第一批归档后明确授权本批：degree10不变，rank33接触/边界切向等式不变，正确局部jets不变，仅约束C>=−1e−10，活跃点<=3500，每轮CLARABEL time_limit90，至多3轮，目标tau+1e−8trace。此后父线程给出更强C_kernel条件时三轮已经全部结束，故本批未用C_kernel筛选；原始数据保持其历史含义。本批所有模型仍是近似有理r0处浮点发现，不能当真r*的精确证书。

主脚本[sharp_contact_refinement2026_competitive_batch2.py](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_competitive_batch2.py>)；完整模型/活跃点/precision/验证在[batch2_results.json](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_batch2_results.json>)；便于精确化取用的原始包[batch2_best_original_data.json](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_batch2_best_original_data.json>)同时保存第一批PSD模型及第二批三个A/x/N/B/c。紧凑指标见[batch2_summary_metrics.json](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_batch2_summary_metrics.json>)。

|轮|solve秒/iter|trace|min eig B|独立竞争域最小R|primal/dual/gap|
|---|---:|---:|---:|---:|---|
|0|23.1453/41|14.50348772|−2.29108e−8|−.00156751958|1.07e−11/2.57e−10/1.71e−6|
|1|24.5834/38|15.39979548|−5.35858e−8|−1.53073945e−5|2.71e−11/1.50e−9/4.04e−6|
|2|27.2242/41|15.48546057|−9.15824e−9|−9.83486732e−6|4.55e−12/9.56e−11/6.89e−7|

三轮均AlmostSolved/optimal_inaccurate，tau报告0但不能据此当约束精确成立。没有任何第二批模型达到PSD>=−1e−9；也没有达到minR>−1e−7。末轮c=2.7224287243023917,F111=4.606105440239247,B=12c−1.5F111≈25.75998653126983；接触最大误差3.83e−15、切向误差2.11e−15，internal Hess min−6.50e−9，三边界lambda最小−9.85e−9、曲率更正后tangent Hess min−1.17e−8。迹正则使PSD和localjets落在数值边界，不能取代第一批minB=+2.34437e−6的trace660.66488464模型。

全部14031旧训练点被保留审计，其中C>=−1e−10有12851点，1180点仅诊断。末轮旧竞争训练minR=−9.86328e−7，非竞争minR=−.01844635仅诊断。初始总pool23248，末尾58978。每轮重新生成10000个竞争随机Gram点用original A recurrence全部重算，另1500 Gram边界点、79个多起点种子、一个DE与最多5个original-A梯度polish。独立compiled/original误差最大约1.55e−14，末轮随机minR=+3.88682e−7但局部搜索仍找到明显负点，说明随机通过不足以验非负。

末轮严格内扰负点p=(−.9932727408102706,−.5711472561258527,.4722521849123732)，有限JSON十进制解释的80位数值R=−.00000983486692404675139687543339085625726865954105637，Gram=+.0000000000228128291242，C=+.0000000000034345819583；此高精度数值不是区间证明。未扰最小点在Gram=C≈0交线上。round1另有明显内部负点p=(−.9001413555587214,−.2518322268922315,.4626190714027071)，R=−.0000153073945034773895，Gram=.1220469045245，C=.0170299020758。

## 新严格必要条件及精确点检查

父已有全域证书的nonsharp模型满足B=25.7599205、R_old>=0、A_k PSD、h<=f。对n=9有恒等式

E−B=Σ_{i<j}(f−h)+(1/7)Σ_{i<j<k}R_old+(1/6)Σ_{i,j,k=1}^9F_old。

每个pair defect、每个distinct-triple R_old及完整ordered F总和均非负；这里不宣称单个F值非负。因此E<=U蕴含每个R_old<=Σ84R_old<=7(E−B)<=7(U−B)，即每个竞争三角还必须C_kernel=7(U−B)−R_old>=0。U取已认证的候选能量有理上界，B取已认证模型target。

可复现精确检查脚本[kernel_budget_checks.py](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_kernel_budget_checks.py>)与完整精确Fraction数据/依赖hash[kernel_budget_certificate.json](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_kernel_budget_certificate.json>)。本脚本没有重跑global verifier；其依赖全域报告status=certified,pending0,nodes202923,bits48，并核对model_sha256一致。模型hash为6ebdebad61e4ba26f044b07b2ed56bcacdfe8c584b6007561bc17b2cd23b52d0；报告和minorant/pair-exclusion文件hash也全部保存。旧模型JSON自身status仍标未证明，是早期prepare状态；其对应全域result报告才是已完成认证的依赖。

精确Fraction点值：首批PSD谷C_kernel=+.0004411936503893693；第二批round0正坐标谷C_kernel=−.001552253457182197而被排除；round1内部谷C_kernel=+.0002966580967158251；末轮严格内扰点C_kernel=+.0003685343734866960，仍存活。因此该新必要条件没有排除首批PSD模型和末轮模型的全部已知负谷。这里只检查必要条件，未证明这些三角能扩展为竞争九点配置；负残差不是Thomson反例，也不是模型族无解证明。

## 复现和job

在工作目录`/home/dsh/Thomson Problem`：

```sh
PYTHONPATH=proof_work:proof_work/python_deps OPENBLAS_NUM_THREADS=1 python3 -c 'import sharp_contact_refinement2026_competitive_batch2 as m; m.PREFIX="sharp_contact_refinement2026_batch2_replay_"; m.run()'
```

原脚本拒绝覆盖已存在输出；使用新的前缀。整个batch2 job bash-569已收齐(exit0)，总144.6103秒。所有旧job亦已收齐。没有修改父验证器、主报告、manifest。后续父线程又明确授权第三有限批：沿真正PSD第一批seed，强化C与C_kernel共同过滤，PSD和internal Hess各1e−6 margin，trace<=2000、tau+1e−9trace、至多3轮90秒；本报告保留第二批历史状态。
