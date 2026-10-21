# sharp d10 接触核 refinement 最终记录（discovery only）

本独立任务已按有限预算结束：第一批3轮，父线程另行授权第二批3轮与第三批至多3轮；第三批实际完成2轮，并按“连续2轮无改善”停止。没有得到目标 minR>−1e−7 的核，没有新增全局下界，也没有完成 Thomson n=9 的严格全局证明。r0=.71054833409295381132770417927279124 仅为有理近似；本文所有优化模型都不能充当真驻点r*的精确证书。

可直接取用的完整原始包是[batch3_best_original_data.json](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_batch3_best_original_data.json>)，同时含第一批最强PSD seed、第二批三个模型、第三批两个模型的完整original A/x/N/B/c；含190个unknown的indices、全部QR后的N、候选exact Fraction三角数据、接触诊断、solverprecision、严格固定模型负残差见证、运行版本和job回执。紧凑指标见[batch3_summary_metrics.json](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_batch3_summary_metrics.json>)。第一批原始[results.json](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_results.json>)、第二批[batch2_results.json](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_batch2_results.json>)、第三批[batch3_results.json](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_batch3_results.json>)保持各次运行历史，未改父验证器、主报告或manifest。

|模型|trace|min eig B|内Hess最小值|已发现竞争域最差R|c|
|---|---:|---:|---:|---:|---:|
|第一批round2，保留的最强PSD seed|660.6648846376025|+2.3443695733e−6|+2.0037571184e−5|−7.7376542507e−6|4.161069114792391|
|第二批round2，不达PSD容差|15.48546057|−9.15824e−9|−6.50448e−9|−9.8348669240e−6|2.7224287243023917|
|第三批round0|14.957977195875976|+9.9561391737e−7|+9.9731041698e−7|−1.1937226322e−5|2.7368685955222625|
|第三批round1|15.435858233645215|+9.9491923384e−7|+3.0555445567e−4|−4.0717695905e−5|2.789787409757307|

第一批seed的F111=16.11522856415924，sharp归一化 B=12c−1.5F111≈25.75998653126983；39接触等式最大误差6.18e−14，边界切向误差4.27e−14。14031训练点original-A独立重算最小R约−3.82e−14，但竞争域全局搜索找到内部负点 p=(−.759220762336624,−.29211600772137486,.32931701954562287)。其Gram=.3758745842903280841，旧竞争预算C=.0303671911625989048，新预算Ckernel=.0004411936503893693；三个量都严格正，因此新必要条件未排除它。这里“最强”只指已保存的浮点PSD/localjets余量及已观测竞争残差，不主张最优。

用户指定关键点p0=(−.29693709,.4225354,.4225354)的真实Gram=.4487280179298211925912。原PSD-contact投影在该点R≈−1.23366120835e−5；第一批round2在该点R≈+.000773956487194874，第三批round0/1则约+2.10867e−6/+1.25141e−6。点及1e−3/1e−2邻域已加入训练候选。旧核的负R是该核目标失败，与Thomson反例无关。

## 接触rank与Gram边界条件

采用正确Q0=1,Q1=t−uv,Q[k+1]=2(t−uv)Q[k]−(1−u²)(1−v²)Q[k−1]，S=6permavg，F=Σtr(AkSk)，R=Σf−7F−Σ_s F(1,s,s)−c。所有验证用actual Coulomb f；未用旧h11。候选零空间由exact Fraction features后QR构建，Ak=NkBkNkᵀ。degree10的非零块尺寸是[9,9,7,7,5,5,3,3,1,1]，unknown190。浮点39eq rank32；再加三边界的两个切向等式形成45eq后rank33、affine维157。这些在本线程仅为数值rank标签，不把r0或浮点SVD当真r*的严格代数证明。

g=1+2uvt−u²−v²−t²。边界必要条件为∇R=λ∇g、λ>=0及 Tᵀ(H_R−λH_g)T PSD，H_g=[[-2,2t,2v],[2t,−2,2u],[2v,2u,−2]]。三个全梯度不能错误置零，TᵀH_R T>=0也不能替代曲率更正。

令C_r=r²/2−1,B_r=2r²−1。CFF型(C_r,r/2,r/2)因重复坐标自动满足一个反对称切向条件，剩 L_C=rR_u+R_v=0，λ=R_u/(1−C_r)。BGG型(−r,−r,B_r)剩 L_B=R_u−2rR_t=0，λ=R_t/(1−B_r)。等边(−1/2)^3的两切向条件由完全对称自动成立，但λ符号仍是额外必要条件。对true stationary root，用候选零空间的一阶消失、9个内部梯度零以及三角类型multiplicity 6/3，可得6L_C−6L_B=7E'_D3h(r)=0；所以39eq一般只给L_C=L_B，仍缺一个独立零切向条件。所有有限批均加了该条件及正确曲率localjets。

第三批有正B/internal-Hess margin，但边界曲率更正Hess最小特征值分别约−3.78e−9/−3.87e−9；因此也不能据solver状态宣称全部localjets严格成立。更直接的失败是下述明显负残差。

## 最后一批设置、负点和solverprecision

第三批沿第一批PSD seed启动，C>=0且Ckernel>=0联合过滤；仅在生成cuts时容忍−1e−12，Gram容忍约−2e−12，最后负点另精确复核。继承全部旧数据及第二批幸存负谷，active每轮3500；B>=1e−6I，9内Hess>=1e−6I，三边界λ和曲率jets维持必要LMI；trace<=2000，目标tau+1e−9trace。每轮CLARABEL time_limit90,tol_gap_abs/rel/feas=1e−10,max_iter350,warm_start=True，未用SCS。第一批无tracepenalty，第二批用1e−8；低trace解在有限cuts下容易可行，却未改善全域R。

|第三批轮|solve秒/iter|CLARABEL状态|primal|dual|gap_abs|active minR|
|---|---:|---|---:|---:|---:|---:|
|0|22.474721873/38|AlmostSolved / optimal_inaccurate|9.42972e−12|1.19766e−9|5.69720e−7|−1.12489e−9|
|1|23.900855212/37|AlmostSolved / optimal_inaccurate|1.14067e−11|1.32290e−9|7.04485e−7|−3.82955e−10|

第一批最佳轮同样AlmostSolved，配置time_limit90而实际reported solve94.728739048s；primal2.04413e−12,dual1.71338e−12,gap3.51338e−9，35iter。第二批三轮均AlmostSolved且minB负；完整precision均保存，不能把tau=0或optimal_inaccurate视作证明。

第三批round0严格内扰点 p=(−.9655589353845775,−.4069479195173,.5089797406978045)，Gram=.0430180151191394049，C=+8.89499540510e−13，Ckernel=+.0002535405086445911，R≈−.00001193722632200706。

第三批round1严格内扰点 p=(−.9993574670431118,−.017923913623535643,−.017923901694124156)，Gram=+5.07110584395e−11，C=+.0031542749946841090，Ckernel=+.0003443649520889260，R≈−.00004071769590462288。

两轮各重新用original A recurrence核验10000个联合竞争随机Gram点，加1500边界点、多起点SLSQP、一个DE、最多5个original-A梯度polish。compiled/original最大差分别约5.00e−15、8.60e−15。全部14031旧点继续审计，联合竞争5796点，排除8235点仅供诊断；旧联合竞争最小值分别−7.82517e−6/−3.99647e−5，说明active子集可行并不代表旧训练全集或全域可行。

## 精确的有限模型障碍和新预算依赖

[fixed_model_obstructions.py](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_fixed_model_obstructions.py>)用exact Fraction计算saved decimal A/c下的多项式F，并对三个1/sqrt(2−2s)用整数isqrt构造2^−160宽有理包围。第一批PSD模型和第二批末轮的R<0区间在[fixed_model_obstructions.json](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_fixed_model_obstructions.json>)；第三批两个模型的同类严格区间在[batch3_fixed_model_obstructions.json](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_batch3_fixed_model_obstructions.json>)，其有理上界分别约−1.1937226322007057e−5、−4.0717695904622885e−5。见证点的Gram/C/Ckernel都以Fraction严格检查为正。该严格小结只否定这些有限十进制模型的全域非负性；总体数学工作仍是discovery only，不证明true-root模型失败、整个核族无解或Thomson有反例。

新必要条件依赖父线程已有认证模型B=25.7599205。精确恒等式 E−B=Σpair(f−h)+(1/7)Σ84 R_old+(1/6)Σ729 F_old，其中pair defect、每个R_old和完整ordered F总和非负（不声称单个F值非负）。因此竞争E<=U时每个R_old<=7(U−B)，即Ckernel=7(U−B)−R_old>=0。[kernel_budget_checks.py](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_kernel_budget_checks.py>)和[kernel_budget_certificate.json](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_kernel_budget_certificate.json>)保存lemma、exact Fraction点值与四个依赖文件SHA256；核对global report的model_sha256一致，status certified,pending0,nodes202923。没有重跑global verifier。已有严格LB25.7599205保持为依赖，本研究没有改进它。

## 复现、停止差异与job回执

数值版本：Python3.10.12,Numpy2.2.6,Scipy1.15.3,CVXPY1.7.5,CLARABEL0.11.1,Sympy1.14.0；详见[runtime_versions.json](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_runtime_versions.json>)。从工作目录运行现有第三批脚本应设置全新输出前缀：

```sh
PYTHONPATH=proof_work:proof_work/python_deps OPENBLAS_NUM_THREADS=1 python3 -c 'import sharp_contact_refinement2026_competitive_batch3 as m; m.PREFIX="sharp_contact_refinement2026_batch3_replay_"; m.run()'
```

此命令只是复现说明，没有追加运行。当前[competitive_batch3.py](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_competitive_batch3.py>)已更正stagnation初始基准为第一PSD模型的竞争残差−7.73765e−6。已运行进程启动时误读旧fullbox残差−.000404807，故原JSON里的stagnation计数是0/1；我按正确竞争基准1/2手工停止，未修改原始JSON。启动版本另保存为[batch3_runtime_snapshot.py](</home/dsh/Thomson Problem/proof_work/sharp_contact_refinement2026_batch3_runtime_snapshot.py>)。这个差异只影响停止判断，不改变任何已保存的约束、目标、随机种子、iterate或验证结果。两轮original models、all active_points与pool_count完整；取消后的未落盘大pool没有补造。

bash-602已取消并job_output收齐，终态SIGTERM；仅两轮完整solve/validation，没有第三返回iterate。bash-516是初始写文件工具symlink问题导致exit2，已诊断并以独立脚本正常运行替代；bash-524/534/539/546/550/556/569/606/608/620全部exit0且已收齐。620仅为归档导出，没有新SDP。最后没有任何活跃background job。父线程已明确停止进一步研究，本线程未追加SDP。所有新产物均在规定前缀下。
