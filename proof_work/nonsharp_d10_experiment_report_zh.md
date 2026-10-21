# d10候选零空间的非sharp下界探索

全部数值结果本身不是严格下界证书。模型使用原exactfeature Nk与QR基，移除所有39条接触/梯度等式，令sol=0、Z=I190；190个上三角变量B PSD，总trace<=10000，tau>=0。目标tau+1e-8 trace。cstar=(E*+1.5F111)/12，R=sum f−7F−sum d−cstar，训练R>=−tau。域Gram PSD交[-1,.56]^3，不启用额外C filter。

继承原d10全部7988cuts，补旧worst、300随机200边界点，去重后8503。各轮均检查18000随机、12000边界、8000近反足，以及三分支2D边界SLSQP/DE、3D多起点SLSQP/DE。compiled与原design交叉误差<=9e-15。

|轮次|cuts|tau|trace|minEig|独立最差R|观察值推算下界|
|---|---:|---:|---:|---:|---:|---:|
|0|8503|2.998881310262055e-08|141.4717650023954|2.401826846970722e-06|-0.0009570438336074516|25.74850200526654|
|1|8844|4.062860779161135e-08|90.41898831906033|2.0857970079951035e-06|-0.0005198157335577769|25.75374874246714|
|2|9185|4.519281519696224e-08|86.24533816560302|1.1053120607477793e-06|-7.843871611762365e-06|25.75989240481049|

三轮状态均optimal_inaccurate。观察值推算下界不是严格下界。最终worst约(-.524928432483,-.705899636655,.351877322883)，Gramdet .363112218149。最终contact诊断误差.00174293138，说明未施加接触等式。第3轮达到>25.7595交接门槛，456.72s提前停止。bash249 exit0已收集。

浮点原basis A/c保存nonsharp_nullspace_actualf_d10_best_export.json。export_nonsharp_d10_rational_v1.py输出nonsharp_d10_rational_target25_7598_v1.json：A对称1e13量化+1e-10I，11块FractionLDL通过，父h19，精确c=(target+1.5F111)/12，F756项/R786项。这是exact组件，不是全域残差证书；由父verify_high_degree_conditional.py检查。bash275 exit0已收集。

父追加授权第二batch最多3轮，new script nonsharp_nullspace_actualf_d10_batch2.py、新JSON nonsharp_nullspace_actualf_d10_run2.json；继承全部保存cuts与worst，并加候选12三角1e-3/1e-2邻域扰动，不加等式。目标独立minR>-1e-6，目前运行中。

本报告采用实际Path.write_text保存；先前工具write报告创建的nonsharp_nullspace_actualf_d10_notes_zh.md在实际FS无法读取且路径操作异常，本报告使用新名字，未改动异常路径。

第二batch首轮（iteration0）实测：10959cuts，tau2.00216327e-9，trace22.76292653，minEig+4.03238535e-8，contact误差2.56430436e-5。独立最差R=-6.163570106e-6 at(-.151721845984,.310567250786,.310567017004)，Gramdet .754808857956，数值建议下界25.7599125684（不是严格下界）。总286.80秒；继续第2轮。

第二batch第2轮（iteration1）：11294cuts，tau2.084464922e-9，trace21.88525926，minEig+3.13012177e-8，contact误差2.64345519e-5。独立最差R=-2.200534478e-6 at(-.620965367101,-.620964266914,.368355264920)，Gramdet .377193384988，数值建议25.7599601249（非严格）；总517.86秒。继续本batch最后第3轮。

## 第二batch最终结果

|iteration|cuts|tau|trace|minEig|独立minR|观察值推算下界|
|---|---:|---:|---:|---:|---:|---:|
|0|10959|2.002163270394829e-09|22.762926527810315|4.032385353401287e-08|-6.16357010596591e-06|25.75991256842856|
|1|11294|2.0844649219705027e-09|21.885259263726393|3.130121769254313e-08|-2.2005344782194403e-06|25.759960124856093|
|2|11632|5.9353065683719105e-09|27.08680596899214|8.263236147104331e-08|-2.8973614800142933e-06|25.759951762932072|

全部状态optimal_inaccurate。独立搜索最佳为iteration1，minR约−2.200534478e−6，未达到−1e−6目标；最后一轮略变差，故使用best_solution而不是solution。全部3轮完成，总708.21秒，bash283 exit0已收集，无额外batch。

父线程新增conditional_h27_certificate.json，严格误差<1e−11。最终export_nonsharp_d10_batch2_rational_v1.py改用此h27，目标25.75995，输出nonsharp_d10_batch2_h27_target25_75995_v1.json；仍对称1e13量化+1e-10I、11块FractionLDL、exact F/c/R重建，不在子任务验证全域。父负责verify_high_degree_conditional.py全域认证与复算。

建议下一步等号/稳定性研究，不自动继续数值下界batch。解除39eq后本模型通过cuts逐渐恢复很小的接触误差；可考虑以最终A为近sharp warmstart，再加入解析contactjets，而不从旧较差强制接触解起步。h27不在候选节点精确接触，真正sharp证书仍需候选接触minorant或真实势的直接认证。
