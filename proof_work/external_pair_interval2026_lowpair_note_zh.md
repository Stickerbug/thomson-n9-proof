# T2 低 φ 盒对：有限严格 prefix 与独立重播

本次只访问完整 894 低盒全集中的 lexicographic 无序盒对 prefix，没有闭合 T2，也没有新 Thomson 能量下界。模型、旧全局 R 非负证明、unary φ 下界和 capacity 分组均为注明 hash 的依赖；只对固定有理 T2 成立。

一次 batch（bash-806，exit0，已收齐）含准备共 90.002368736 秒。初始全集为 400065 无序盒对：152032 个由 φ 下界接受、18741 个由 capacity-one 分组排除、229292 个未决。依次访问487个未决盒对，369个严格得到 W≥1/25000，117个由I384七个cap之一排除，1个仍未决；228805个未访问盒对完整保留，最终未决228806。下一未访问为(2,342)。这里不能把visited以外的盒对当作通过。

独立 data-only audit（bash-810，exit0）用了11.4774秒，复核ID连续prefix、完整计数、1110个query的有理覆盖及最终Fraction算术，不重建系数。随后额外授权的独立strict replay（bash-813，exit0）用31.318671871秒全部通过：重建48bit精确根张量，13293次split64，重新取得7284个terminal coefficient minima，完整重播1110个query；487组I384 chart/anchors/7dots亦全部重算。每个query检查分割路径、固定坐标包含、投影交集的精确体积和、不重叠内部，及cap和W精确比较。未借用浮点W作接受判定。旧202923节点证明和unary degree54根未重跑。这里的“独立重播”复用同一底层 coefficients/split64 和 I384 代码，属于重建输入、重新执行和逐记录核对，不能称为完全独立的第二套实现。

3D根张量shape=28³，48bit整数系数范围[-44180265718002115,1066518328158214]，绝对值小于2^60，所以外向midpoint和的绝对值小于2^61，int64安全。查询最多30次split、8个cover叶子；各ψ下界取max(0,lower)依赖旧几何R≥0证书。

最小已接受下界出现在(1,275)，W_lower≈0.00004072054113667818，比1/25000多7.20541136678e-7。唯一未决为(1,265)，W_lower≈0.000038244037958395604；其三query都做了30split，cover叶数5/6/5，因此这是当前oracle宽度问题，不能解释为W的负点或阈值反例，亦不是deadline截断。

主要文件：

- [result](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_lowpair_result.json>)：总计数、预算、依赖hash。
- [universe](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_lowpair_universe.json>)：894个明确编号、位置、φ下界及capacity标签；完整0≤i≤j<894规则。
- [records](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_lowpair_records.json>)：487条i/j、动作、精确下界、query terminal paths及I384七点积；约11.9MB。
- [replay result](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_lowpair_replay.json>)：全部独立重播通过，仍有228806全局未决盒对。
- [batch source](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_lowpair_batch.py>)、[replay source](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_lowpair_replay.py>)、[data audit](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_lowpair_verify.py>)。

下一实现的设计已评估：每个chart的IDs建二叉partition树；node显式存IDs、φmin和所有叶子I384坐标/anchor-dot区间的union bounding。集合不必连通，bounding包住全体即可。四个ordered chart-product根覆盖全部894²有序盒对；每次仅沿一端node的互斥IDs子集分裂，保存parent/children。只有整个block的φmin之和达到5m、整个block同一capacity标签、I384 dot严格违反cap或整个block的ψ oracle使下界≥m时，才可终止接受/排除；否则分裂到singlecell或保留整个budget frontier。最终用894×894 bitmap复核每个有序盒对恰计1次。不能把逐cell已经通过的count当作未经检查的coarse block cut。

此设计可以让一次严格oracle接受多个leafpairs；实际压缩率尚未测量，不能预先声称数千倍。父线程已经另行授权一次≤120秒/3000blocks层级试验；本prefix不会重复运行。
