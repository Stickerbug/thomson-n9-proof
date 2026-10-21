# T2 低盒层级试验、覆盖审计与精确对称聚合

固定有理 T2 的试验未闭合；没有新能量下界，父线程严格全球下界保持 **25.7599205**。阈值为 W≥1/25000。这里只处理依赖 unary 覆盖后的894个低φ盒，不能把低盒局部进展写成T2已证。

第一层级批次（bash-816，exit0，job_output已收齐）从四个完整有序chart产品根出发，含准备共118.456638524秒，处理2012/3000个block；生成1786个低集合树node及3862个product block。40个ψ接受终端覆盖51689对，40个cap排除终端覆盖78683对，3个capacity排除终端覆盖2352对；1850个budget-pending终端覆盖666512对。每个终端，包括所有pending，都写出明确IDs；原运行与数据审计均验证整个894²=799236有序pair全集的mask最小值=最大值=1。只用pending文件无法重建这些覆盖结论。

[独立数据审计](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_hierarchy_audit.json>)（bash-818，exit0，已收齐）用5.286934374秒复核全部树ID partition、union bbox、φmin、capacity标签、3862个product block、1933个终端、38个query cover以及18次对称memo复用。该审计没有重建新query的terminal coefficient minima；这些仍为原运行oracle记录。此前[prefix重播](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_lowpair_replay.json>)已对487条prefix记录、1110个query及7284个terminal coefficient minima完整重建，使用31.318671871秒。所有这些“独立重播”共享底层coefficients/split64和I384代码，不能称为完全独立的第二套实现。

[仅数据聚合](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_aggregation.json>)依父线程指令完成，不调用oracle/solver，不遍历树：initialmask OR hierarchy resolved terminal products OR prefix486个resolved singleton的双向，再 C|=C.T。旧R精确全排列对称已经source断言验证，W及cap/capacity谓词均有q/r对称性。

| 阶段 | 已解决有序pair | 未决有序pair |
|---|---:|---:|
| unary φ / capacity 初剪 | 340652 | 458584 |
| 加hierarchy终端 | 398001 | 401235 |
| 加prefix双向singleton | 398783 | 400453 |
| 精确转置对称闭包 | **399788** | **399448** |

净增加59136对，其中prefix在前两者union之外增加782对，对称闭包再增加1005对。不能直接把hierarchy的666512个pending与初剪458584比较，前者含原已解决的个别pair。聚合结果的row-major 894×894 uint8 mask（resolved=1,pending=0）SHA256为`f82c1ef49eec190c071ad23ce193cd3706d34621fdf21c6e4b3dc2bfa3f54816`。聚合只计并集，不修改任何原proof结果。

- [层级结果](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_hierarchy_result.json>)保存预算、终端计数、底层依赖hash；[树](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_hierarchy_tree.json>)、[blocks](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_hierarchy_blocks.json>)与[frontier](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_hierarchy_frontier.json>)共同保留全域覆盖及未决块。
- [层级source](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_hierarchy.py>)和[审计source](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_hierarchy_verify.py>)可复现本次有限运行及数据审计；不应覆盖原输出。
- [prefix说明](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_lowpair_note_zh.md>)列出先前有限prefix、系数重播和宽度障碍。

父线程在本次归档后另行授权一次明确不同的v2有限批次：继承上述完整对称mask、整块继承接受、粗盒不调用无效root oracle、细盒60split/16leaf；新prefix保存，不改本批source/artifacts。此授权不能追溯改变本批未闭合状态。
