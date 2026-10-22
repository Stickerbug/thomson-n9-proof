# Thomson n=9 投稿准备评估（2026-10-22）

这份文件把当前九点成果与已公开的 n=7、n=8 项目对照，区分“已经完成的证明证据”和“投稿前仍应补齐的外部证据”。它不改变冻结陈述、Lean 源码或验证器。

## 对照基准

七点项目 `huwngtran/thomson-n7-lean` 的公开复现入口包含固定挑战陈述、Lean 构建脚本、主检查脚本、第二内核 `nanoda` 检查、声明映射、哈希清单和负向测试。其主结论还包括模正交变换与点重标号的唯一性。复核快照和链接保存在 [THOMSON_N9_PUBLICATION_VALIDATION_zh.md](../THOMSON_N9_PUBLICATION_VALIDATION_zh.md)。

八点项目的论文是 arXiv:2609.22077v1（2026-09-18），主文给出数学证明和 Theorems 1.1–1.3，明确说明计算机辅助部分由 Lean 验证；伴随仓库提供有限证书和只使用 Python 标准库的精确检查器。其 Theorem 1.1 对对数和 Coulomb 能量同时给出全局最优与全等唯一性。论文把更大的 Riesz 参数范围和部分更精细的证书留在 companion repository，并在文中披露 Lean 验证和 LLM 使用情况。

这两个项目的共同发表结构是：主论文讲清楚可读的数学归约和定理，仓库保存精确证书、脚本、版本锁和复现命令；形式化验证是证据链的一部分，不能代替定理陈述的人工审查、独立实现或同行评审。

## 九点目前已经达到的层次

当前正式结果是

```lean
ThomsonNine.thomsonNineClaim_proved : ThomsonNine.ThomsonNineClaim
```

它在原样冻结的 `Statement.lean` 中证明指定三层候选在唯一驻点半径处达到所有互异九点球面构型的全局最低 Coulomb 能量。正式闭包为 2390 个模块、1507 项公理审计、807/807 个不同系数目标；`leanchecker --fresh ThomsonNine.LocalVerification` 用时 13228.2 秒并通过，允许公理只有 `propext`、`Classical.choice` 和 `Quot.sound`。

这已经超过“只证明对称族最优”或“只做数值搜索”的层次，也满足 n=8 论文所采用的“数学陈述 + Lean 证书”主结构。45 条接触方程、12 个局部邻域、实际残差绑定和 136125 节点/68063 叶覆盖树均已连接到最终 Lean 定理。

独立 Python 检查器也已完成一次全树分片重算：154 个分片、50 组测试、完整树结构和叶理由通过，状态为 `PASS_INDEPENDENT_CONDITIONAL_COVERAGE`。它的条件边界必须原样保留：独立程序仍把原始系数模型、局部非负性、PSD、pair reduction 以及到物理域的归约作为前提，因此不能写成“独立完成了整个九点证明”。

## 仍然缺少的发表证据

与 n=7 相比，当前最明显的缺口是第二证明内核。九点已有 Lean 自身 fresh replay 和独立 Python 算术检查，但还没有把最终证明对象交给 `nanoda` 或同等独立内核检查。第二个缺口是独立 Python 链条尚未把所有条件前提都重新证明；尤其 exact-45 接触兼容性和完整物理归约仍应由独立实现或第二内核覆盖。

与 n=8 的主论文相比，当前英文稿还需要一次面向读者的重写：把 2390 个模块和数值树放到可引用的附录/仓库，把主文集中在三变量归约、实际残差、局部证书、全局覆盖和最终定理；同时补齐作者、单位、参考文献、代码许可证、版本锁、贡献说明和 AI 使用披露。当前仓库中的历史阶段文档保留了旧状态，投稿稿件必须明确以最终验证记录为准。

如果论文标题或摘要使用“唯一最优构型”，还缺少一个数学定理：现有 `ThomsonNineClaim` 没有断言所有最小构型与候选构型全等。可以把它作为后续工作，也可以先把投稿主张限定为“候选达到全局最小值”。

还应在投稿前完成一次独立机器的干净复现，核对 Lean/Mathlib 版本、源码清单、复核包 SHA-256 和从零恢复依赖的命令。当前构建采用了已审计的现有产物并记录为 `adopt`；这已通过完整 fresh 重放，但论文应如实说明这一点。

## 哪些优化值得做

最值得投入的是验证独立性，而不是继续压缩 13228 秒的 fresh 时间。当前 fresh 内核重放基本串行，增加 CPU 不会线性加速；内存优化已经把大树块峰值从超过 12 GiB 降到约 3.9 GiB。继续优化运行时间对审稿价值有限。

建议按以下顺序推进：

1. 先把独立 Python 检查器从“conditional coverage”扩展到 exact-45 接触兼容性和物理归约，或明确把这些部分交给第二内核。
2. 导出最终 Lean 证明对象，运行 `nanoda` 或另一套独立 kernel，并加入篡改整数、删叶、漏域、错误根区间和错误公理的自动失败测试。
3. 建立干净 CI：固定工具链和依赖哈希，分别执行源码检查、1507 项公理审计、完整 fresh replay、独立检查器和负向测试。
4. 重写英文主文和补充材料，给每个主要数学引理对应的 Lean 名称、证书格式和复现命令；把历史进度文件放入归档而不是主叙述。
5. 通过 DOI 归档（例如 Zenodo）发布源代码和复核包，再提交 arXiv 预印本；之后选择球面能量、计算机辅助证明或形式化数学方向的期刊送外审。

## 发布判断

现在可以发布一个措辞严格的 arXiv/技术预印本，标题应强调“Lean-verified computer-assisted proof”或“formal proof of the frozen nine-point claim”，并明确 Lean fresh replay 不是外部独立验证、没有全等唯一性定理。

如果目标是声称“达到 n=7 的完整验证标准”，建议先完成第二内核和独立前提闭合，再投稿期刊。这个顺序能显著降低审稿人最可能提出的质疑，也比继续增加模块数量或重复同一 Lean 重放更有效。

当前核心材料：

- [完整 Lean 证明记录](GLOBAL_THEOREM_2026-10-22_zh.md)
- [正式复现说明](README_local_lean.md)
- [独立检查器说明](README_independent_checker.md)
- [当前复核包](../THOMSON_N9_REVIEW_BUNDLE.zip)
- [英文论文 PDF](../../paper/main.pdf)
- [英文论文 LaTeX 源码](../../paper/main.tex)
- [紧凑投稿源包](../../paper/THOMSON_N9_MANUSCRIPT_SOURCE.zip)
- [论文编译与投稿备注](../../paper/README.md)

论文初稿已经用 `latexmk -pdf -interaction=nonstopmode -halt-on-error` 编译为 5 页 PDF，日志没有 `Overfull`、`Fatal` 或错误诊断。提交前仍需替换作者占位符，并补充单位、ORCID、基金信息、代码许可证和 DOI/版本号。
