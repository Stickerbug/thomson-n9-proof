# n=10 形式化证明先例筛查（2026-10-23）

## 查询结果

截至 2026-10-23，本次公开仓库 API 初筛对以下关键词没有返回专门的 Lean n=10 Thomson 仓库：

- `thomson n=10 lean`
- `thomson n10 lean`
- `Thomson problem ten points formal proof`
- `Thomson n 10 proof`

这是 GitHub 仓库名和描述的初筛，不是完整数学文献检索，也不能据此直接宣称 n=10 没有先例。投稿前还应检索 MathSciNet、zbMATH、Google Scholar、arXiv、Zenodo 和相关作者主页。

## 当前本地证据

本仓库包含若干 `analytic10`、`d10_*` 和 `sharp_*d10*` 文件。这些文件记录了 n=9 证明中使用的十阶多项式、局部数值试验和候选证书探索；其中多处明确标记为 discovery、numerical only 或不构成全局定理。它们没有接入 `ThomsonNine.LocalVerification`，也没有形成 n=10 的 Lean 根定理。

因此，当前仓库不能对外写成 n=10 证明。若继续推进，必须重新定义十点候选构型、证明相应能量表达式和物理域归约，并完成局部证书、全域覆盖、轴公理审计和 fresh replay。

## 可发表的首创性条件

只有同时满足下面条件，才可以使用类似“first Lean-verified proof for n=10”的表述：

1. 完成公开文献、预印本、代码仓库和 DOI 的优先权检索；
2. 固定十点定理陈述，并把候选构型、能量和唯一性范围写入冻结声明；
3. 所有具体证书接入 Lean 根入口，禁止 discovery-only 数据充当证明；
4. 完成无 `sorryAx` 的公理审计、完整 fresh replay 和可重复发布包；
5. 在论文中明确 AI 使用、先例检索范围和证明边界。

在这些条件完成前，最准确的表述是“n=10 certificate exploration”或“a planned n=10 formalization”。
