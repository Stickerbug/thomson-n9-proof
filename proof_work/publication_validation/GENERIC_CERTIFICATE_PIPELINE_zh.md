# 面向任意实例的证书流水线（阶段 A，2026-10-24）

## 目标

目标是提供一个“输入实例编号、搜索并验证证书”的半自动流水线。对给定的 `n`，外部程序可以寻找候选构型和精确证书；Lean 只接受通过通用检查器的证书。成功运行输出正式定理，失败运行输出 `unknown` 或生成失败记录。

这一区分很重要：证书检查器可以是通用的，但目前没有定理保证任意 `n` 都存在可搜索到的候选构型、低维约化或有限覆盖证书。因此当前目标是“找到就证明”，不是声称已经有任意 `n` 的完备自动求解器。

## Lean 内核接口

`ThomsonCertificate.Certificate n` 和 `ThomsonCertificate.CertificateFamily` 位于
`formal/ThomsonCertificate/GenericCertificate.lean`，包含：

`CertificateFamily` 则按 `n` 提供一族这样的对象，并有 `CertificateFamily.sound`。

`GenericLowerBound.lean` 的 `LowerBoundBridge.sound` 再把证书目标连接回原始配置的能量下界；配置空间、约化映射和能量恒等式仍由每个 n 的 adapter 提供。

- 实例专用的盒类型和点类型；
- `Spec`：域、目标、叶证书和分裂关系；
- 有限覆盖树；
- `Checked` 证明。

核心定理是：

```lean
ThomsonCertificate.Certificate.sound
```

它把 `Checked` 证书转换成整个覆盖域上的目标命题。Bernstein、PSD 和覆盖树模块都可以作为实例适配器的组成部分。

## 外部生成器和可信边界

建议的运行阶段如下：

1. `discover(n)`：数值搜索候选构型、对称性和低维参数；
2. `exactify(n, candidate)`：求解接触方程，生成有理数或代数数数据；
3. `certify(n, exact_data)`：生成 PSD 块、局部区间证书、Bernstein 系数和覆盖树；
4. `export(n, certificate)`：输出 JSON 数据和生成的 Lean 适配器；
5. `check(n, adapter)`：编译并运行 Lean 内核检查器；
6. 只有第 5 步成功，流水线才报告 `proved`。

搜索、数值优化和证书生成器属于不可信输入；它们可以出错，但错误必须在 Lean 检查阶段被拒绝。外部生成器不应把浮点结果直接当成定理前提。

## 可执行调度器

`run_certificate_pipeline.py` 读取 `schema = thomson-certificate-v1` 的清单，拒绝路径穿越和缺失源文件，然后调用 `lake env lean` 编译指定 adapter。n=9 清单 `certificate_manifests/n9_structured.json` 已运行通过，记录为 `status = PASS`；一个含 `../` 路径的负向清单返回 `UNKNOWN`。该脚本只负责证书验证调度，尚未实现候选构型搜索。

n=10 清单 `certificate_manifests/n10_candidate_only.json` 明确使用 `candidate_only` 模式，引用现有数值/条件性审计并返回 `UNKNOWN`，因为当前没有 n=10 Lean certificate adapter。它不会把 `analytic10` 的非形式化或非尖锐下界记录误报为证明。

n=9 清单 `certificate_manifests/n9_global_claim.json` 进一步编译 `GlobalMinimumContract` 适配器，统一暴露候选可行性、候选能量恒等式和全局下界；它运行结果为 `PASS`，但仍复用现有冻结 n=9 定理，不改变根入口。

`GenericUniqueness.lean` 提供可选的 `EqualityClassification` 层。n=7/n=8 的等号唯一性可以填充该层；n=9 当前合同不填充它，因此不会产生未经证明的唯一性声明。

## 建议的证书数据分层

```text
candidate.json       候选构型和参数的精确表示
model.json           Thomson 能量到低维残差的约化数据
contact.json         接触方程、秩和兼容性证书
psd_blocks.json      PSD 块及其精确 LDL/合同数据
local.json           局部 Hessian、边界和 Hermite 证书
tree.json            Bernstein 覆盖树和叶终止原因
generated/Instance.lean 由上述数据生成的 Lean 适配器
```

## 可验证的阶段目标

1. 用 `Certificate 9` 包装现有 n=9 覆盖证明，不改变冻结定理（语义和结构化 `CutTree` 适配器均已通过）；
2. 选取 n=7 或 n=8 建立第二个适配器，报告真正复用的模块和许可证；
3. 将证书生成器从 n=9 的固定脚本抽象为参数化导出器；
4. 用相同接口对 n=10 做候选搜索和小规模证书试验；
5. 只有完成完整模型约化、覆盖和审计后，才报告 n=10 的正式证明。

当前 `GenericCertificate`、`GenericBernstein`、`GenericCoverage`、`GenericPSD` 和 `GenericFramework` 已构成阶段 A 的 Lean 原型；n=9 适配器和外部证书生成器仍是后续工作。
