# n=7 / n=8 跨实例适配审计（2026-10-24）

本记录基于只读克隆和公开源文件检查，不把外部仓库的代码复制进本项目，也不把 README 声明当成本项目的验证结果。

| 实例 | 只读提交 | 公开最终接口 | 许可证边界 | 当前结论 |
|---|---|---|---|---|
| n=7 | `huwngtran/thomson-n7-lean` @ `25f2fa53119273458cfbb3c4230904bffdd61e53` | `ThomsonN7.thomson_seven`、`ThomsonN7.thomson_seven_unique`，位于 `formal/lean/ThomsonN7/Solution.lean` | 仓库没有 LICENSE 文件；不能直接复制源代码 | 可以设计声明级 adapter；复用代码前需取得许可 |
| n=8 | `jstoobysmith/Thomson-N-8-Warrant` @ `2c35d62e07d72686931da4bc3e062d668e858eda` | `thomson_eight_lower`、`thomson_eight_unique`，位于 `Solution.lean`，并由 `Thomson.Complete` 提供实现 | README 写明 Apache 2.0，但仓库没有被 GitHub API 识别的 LICENSE 文件；需确认许可文本 | 可先做声明级 adapter；复制实现前需确认 Apache 许可 |
| n=9 | 本项目当前 `ThomsonNineAdapter` / `ThomsonNineStructuredAdapter` | `n9_certificate_sound`、`n9_structured_certificate_sound` | 本项目代码 | 语义和结构化 adapter 已通过 |

## 公开接口形状

n=7 的核心目标是：对 `SphereConfig 7` 中的配置证明候选 pentagonal bipyramid 的能量下界，并给出正交变换和置换意义下的等号唯一性。n=8 的 `Solution.lean` 暴露 `thomson_eight_lower` 和 `thomson_eight_unique`；其证明仓库 README 自称是 “warrant”，作者对传统数学证明地位作了保留说明。

这两个接口与本项目的 `Certificate n` 在“实例编号、候选构型、全局下界、等号分类”层面可建立声明映射，但它们的内部坐标、能量定义、证书树和 PSD 数据结构不同。跨实例复用不能通过简单改名完成。

## 适配策略

第一步只建立不复制外部实现的声明级桥接：记录各实例的候选、能量和唯一性命题，并证明它们可以被一个统一的 `InstanceClaim n` 接口引用。第二步在取得许可证确认后，才考虑复用具体证书模块。第三步再报告真正复用的 Lean 定理、模块和代码行数。

本审计没有运行 n=7 或 n=8 的完整构建，也没有声称它们已经被本项目的 Lean 内核重新验证；公开仓库的构建和 Nanoda 状态仍应由独立复核者在各自仓库中重放。
