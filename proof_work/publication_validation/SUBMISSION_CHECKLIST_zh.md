# 当前复核提交清单

更新：2026-10-23。2390 模块、1507 项公理审计、807/807 个不同归档系数目标；完整 fresh 重放 13228.2 秒。

- [x] 冻结 `Statement.lean` 保持不变。
- [x] `ThomsonNine.thomsonNineClaim_proved : ThomsonNine.ThomsonNineClaim` 正式导入根入口。
- [x] 全部实际残差绑定、45 条接触方程、12 个局部邻域与完整 68063 叶覆盖接入。
- [x] 正式根入口、公理输出顺序、允许公理和源码禁用项检查通过。
- [x] 单次完整 `leanchecker --fresh ThomsonNine.LocalVerification` 通过，覆盖最终定理与整个正式根入口。
- [x] 导出模板、输入、源码、产物与日志哈希由统一报告绑定。
- [x] 复核包由当前 PASS 报告经打包门控生成，并复核每项归档负载哈希。
- [x] 英文论文初稿已编译为 5 页 PDF：`paper/main.tex`、`paper/main.pdf`；源码与 PDF SHA-256 写在 `paper/README.md`。
- [x] 已生成紧凑投稿源包 `paper/THOMSON_N9_MANUSCRIPT_SOURCE.zip`，包含源码和 PDF，并纳入复核包清单。
- [x] 论文明确写出 Lean fresh replay、条件式 Python 检查器和未声称的全等唯一性范围。
- [x] 当前 canonical 复核包包含 5637 条目，含紧凑投稿源包。
- [x] 作者 Jingxing Huang、Qian Xuesen College、Xi'an Jiaotong University、ORCID、通讯邮箱、无资助和无利益冲突声明已写入论文。
- [ ] 提交前补充代码许可证、DOI 和正式 release version（若尚未归档）。
- [ ] 若目标是 n=7 级别的独立性，再增加第二证明内核并闭合独立检查器的条件前提。
- [ ] 外部独立实现验证及同行评审：尚未进行，不作完成声明。

最终命题证明候选达到全局最低能量，不包含所有最优构型的全等唯一性。详见 [完整记录](GLOBAL_THEOREM_2026-10-22_zh.md)。
