# 无SDP解析修复：相对PSD代价小，法向斜率被破坏

3patch共57.662秒，无cvxpy Problem/solve。只用线性代数、最多Q和1个新谷的解析active-set最小相对范数修复，以及原A局部验证；未启第4patch。原A随机10000+边界2000+旧mandatory5478扫描，每次最低64原A核验，13秒以内原A局部搜索，原始scan_i.npz保存。

基准oldref在contact affine空间正交投影。Q目标增量3.35101091373e-9，ΠgQ范数6.24995997e-5。Euclidean dx范数5.36165181e-5；相对度量由oldBref Cholesky L映射Y的Frobenius单位坐标（offdiag1/√2）到δB=LYLᵀ，T为190×190，null(C@T)数值rank33。C@T@Zrel最大误差1.52345e-14。T/Zrel/N/indices及源hash均保存，不假设兼容后伪逆隐藏接触残差。

|patch|模式|dx范数|relative y范数|minEig B|minR原A|index7 λ|
|---|---|---:|---:|---:|---:|---:|
|0|Euclidean|5.36165181e-05|nan|-6.9779663e-06|-3.12312797845e-09|-2.43156306e-05|
|1|relative|0.00869227523|0.00152410834|1.42233923e-06|-7.54409269499e-08|-0.000120670824|
|2|relative|0.0101313527|0.00155298348|1.42233923e-06|-1.83094249762e-08|-5.93635796e-05|

欧氏patch失PSD；相对patch y范数小于.002，相对PSD理论界||Y_k||₂<=||y||₂<1成立于精确Cholesky模型，但当前计算仍浮点，需要exact化才能作严格证书。数值minB保留1.422339e-6，Q修至约+1e-9，P约+2e-5，所有contact误差<=2.22e-14、原A/compiled误差<=6.33e-15。

真正失败原因：边界contact index7=(-.5,-.5,-.5)法向lambda原+1.2669e-5，被三个patch分别改为负；corrected切向Hessian仍正，因此问题不是切向曲率，而是朝Gram内部的一阶斜率。后两次原A局部谷分别接近(-.4997217)^3和(-.4998628)^3，Gram真正为正；其中最后Gram=.000617222884。Fraction只确认域成员，不把float residual当exact certificate。

这解释了为什么单独Q最小范数方向虽便宜且相对PSD可保，却不保全域非负。下一种有针对性的解析诊断可将lambda>=1e-8加入相对active set，不宜继续追逐同一边界周围的新谷；本批未自行实施下一步。

所有原始A/N/B/x/c及cutscan、T/Zrel保存在results.json/scan_i.npz，audit.json冻结driver依赖原文和结果SHA。results SHA256=4850f93b71a59de33bb9c3e3067e69321de1460044028feca3502f3e60b76d59；finalA canonicalJSON SHA256=27ad7391c5bca59db39896527da0f6bfa3d518bd04d99485c52c826d9a860b1a。严格LB25.7599205未改变，全局证明仍开放。
