# T2 低盒层级 v2：继承完整掩码，有限批次无新增关闭

v2 未新增已解决盒对。父线程严格全球下界保持 **25.7599205**；固定有理 T2 的 W≥1/25000 全域证书仍未闭合。本批按新授权运行一次后停止，没有追加第三批、SDP或物理subcell细化。

v2 使用新source和独立输出prefix；静态准备与复核在180秒限制内完成。唯一proof job为bash-824，exit0，job_output已收齐。循环留出落盘余量设178秒，实测含准备及完整mask收尾178.104351015秒；block上限10000，实际处理1067个。准备含继承mask重建用6.534244791秒。

具体改变为：从四个完整有序chart产品根起步，载入并重建先前的399788-entry对称resolved mask，验证row-major uint8 SHA256为`f82c1ef49eec190c071ad23ce193cd3706d34621fdf21c6e4b3dc2bfa3f54816`。只有整个node IDs Cartesian product满足mask.all()才可accept_inherited。所有输入聚合依赖hash均核对。粗盒maxwidth>1/2时，已知root Bernstein min<0，而旧几何R≥0使每个ψ项的下界可取0，因此直接partition并跳过无效root query；这里没有断言实际ψ=0。细盒query上限提高到60split/16leaf，保留完整有理cover。

| v2 terminal action | blocks | 覆盖有序pair |
|---|---:|---:|
| accept_inherited | 40 | 106124 |
| pending_budget | 991 | 693112 |
| 合计 | 1031 | 799236 |

1027次product分裂生成2058个product block。1786个低集合树node、全部parent/child、明确terminal IDs和budget frontier均保留。原运行assert整个894²有序全集每个entry恰好计1，mask_min=mask_max=1。693112是本批terminal pending计数，其中仍含大量旧mask已经解决的单独条目，不能拿它替换实际聚合未决数。

本批跳过511个coarse oracle triples，实际执行549个细query、21518次split，缓存重置20次。预算终止前没有新增accept_psi、cap排除或capacity排除。提升query精度显著增加了在早期较大block上的工作，未在本预算内达到可新增终端接受的小集合；这只是本次算法/预算的障碍，不是W阈值反例或方法不存在的结论。

[完整数据审计](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_hierarchy_v2_audit.json>)（bash-829，exit0，job_output已收齐，8.669502603秒）复核输入mask、整块all谓词、union bbox、φmin、完整ID partition、四根产品、parent/children及所有terminal（包括pending）的894²覆盖。query cover判据允许至多16叶/60split；coarse skip单独检查其零下界逻辑，不套用需要psi_lower_scaled的旧分支。实际本批全部已解决终端都是inherited，因此query_covers_checked=0；内部split记录中的549次细query没有产生新的终端接受。数据审计不重建多项式系数。所有低层coefficients/split64与I384代码共享；“独立重播”不是完全独立的第二套实现。本批没有新的ψ终端接受，所有新增列出的accept_inherited只引用已经存在的聚合条目。

[仅数据聚合](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_hierarchy_v2_aggregation.json>)将inherited mask OR 本批resolved terminal产品，再取精确转置闭包。结果保持399788个resolved、399448个pending，新增0；mask checksum保持上述值。旧聚合依赖initial unary/capacity、prefix完整重播和第一hierarchy的记录/覆盖审计；不能把三套依赖称作全局T2证明。

主要文件：

- [v2结果](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_hierarchy_v2_result.json>)、[准备记录](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_hierarchy_v2_preparation.json>)、[运行日志](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_hierarchy_v2.log>)。
- [v2完整低集合树](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_hierarchy_v2_tree.json>)、[product blocks](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_hierarchy_v2_blocks.json>)、[完整frontier](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_hierarchy_v2_frontier.json>)。
- [v2 source](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_hierarchy_v2.py>)、[v2数据审计source](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_hierarchy_v2_verify.py>)。
- [第一层级及最终对称聚合说明](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_hierarchy_note_zh.md>)、[第一层级聚合](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_aggregation.json>)、[prefix及其完整重播说明](</home/dsh/Thomson Problem/proof_work/external_pair_interval2026_lowpair_note_zh.md>)。

为保留原artifact，重运行必须选择新的输出prefix；仅重做数据审计可以读取现有完整文件，但其输出同样应选择新prefix。旧global R的202923节点证明、unary degree54根和父验证器未重跑或编辑。
