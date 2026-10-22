# 冻结 Thomson n=9 全局定理已通过 Lean 统一验证

完成时间：2026-10-22T14:31:45.644413+08:00。

正式结论是原样保留的 `ThomsonNineClaim`，证明入口为
[MainCoverage/Final.lean](formal/MainCoverage/Final.lean)：

```lean
theorem ThomsonNine.thomsonNineClaim_proved : ThomsonNine.ThomsonNineClaim
```

[Statement.lean](formal/ThomsonNine/Statement.lean) 与先前规范复核包逐字节相同，SHA-256 为
`df6bdb11de5904cbcbb6b8cd3b68a1a41e5cecc8343e23c9d266d981d0f5f073`。没有缩小定义域或增加证书前提。

该命题断言存在唯一驻点半径 `r ∈ (0,1)`；给定三层候选构型的九个点互异且在单位球面上；其能量等于明示的 `familyEnergy r`；任意互异九点球面构型的能量均不低于它。
命题没有断言所有最优构型均与候选构型全等。

## 统一验证证据

- 2390 模块、1507 项公理审计、807/807 个不同归档系数目标；完整 fresh 重放 13228.2 秒。
- 公理只允许 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx`。
- 正式根入口、公理输出和源码禁用项检查全部通过。
- `leanchecker --fresh ThomsonNine.LocalVerification` exit 0；完整导入闭包包含正式根入口和最终定理。
- 源码、编译产物、导出模板、输入和验证日志均由报告记录哈希。验证模式是显式采用已有构建 `adopt`，随后完整 fresh 重放；没有把缓存采用称为从零编译。

权威报告：[local_lean_verification.json](local_lean_verification.json)。
最终结果：[global_theorem_result.json](global_theorem_result.json)。
导入登记：[packed_coverage_manifest.json](packed_coverage_manifest.json)。

## 证明链

1. 从冻结半径、Hermite 数据、405 项有效 N 数据、33 行接触系统及 190 个参数构造实际 F/c，证明 PSD、45 条接触方程和实际残差绑定。
2. 精确整数区间和共享分组算法处理全部 807 个不同源系数；完整 Hessian/Gram 边界分析证明 12 个实际局部邻域的残差非负。
3. 球面多项式加法公式与正矩证书给出逐对截断：只需处理内积不超过 `14/25` 的低能量构型；候选能量严格低于采用的有理阈值。
4. 证明真实 F 与中点对称多项式的误差、4816 个对角缓存区间及 4810 个一维 Coulomb 下界，连接根张量和真实 Coulomb 残差。
5. 通用有向舍入、128 位打包和 Bernstein 二分正确性定理复核原始 136125 节点、68063 叶的树。498 个前沿子树及完整前缀覆盖均由 Lean 证书连接。
6. 将物理 Gram 约束与三坐标排序代入全域覆盖，再由三点能量恒等式推出冻结全局命题。

主要接口是 `PackedMain.actual_root_frame`、`actual_axes_lower`、`actual_local_lower`、`claim_from_certified_frontier` 和最终定理；完整名称均以 `ThomsonNine.` 开头。

## 本轮优化与统计

807 项使用共享算法批量处理，避免逐个手工定制。大树块通过已验证的入口状态缓存和小片段证明拼接控制内存；某块峰值从超过 12 GiB 降至约 3.9 GiB。保留原模块名、逐字节登记源码与已有编译产物，避免仅为更改导入前缀重编数千份证书。以前的 `ThomsonNine/Construction` 副本作为历史重现资料保留，不与当前原名模块同时导入。

历史基线实际为 272 个不同目标；七个目标加入后为 279；最终去重统计为 807/807。814 条 gathered 审计声明中的重复目标没有多算。
当前总模块数按最终实际导入闭包计算，含自动分段辅助模块；不能与之前 183/433/577 模块阶段直接比较。

## 复现与验证边界

固定 Lean 4.34.1，Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`。保留 `formal/.lake`。

```bash
export LEAN_BIN_DIR=/path/to/lean-4.34.1/bin
python3 -B proof_work/publication_validation/verify_local_lean.py
```

匹配先前 PASS 哈希戳时可用 `--reuse-local-build`；明确采用已有编译产物用 `--adopt-build`。三种模式都必须完成一次完整 fresh 重放，不能用旧 PASS 代替新闭包。

`leanchecker` 调用 Lean 自己的内核。这不是外部独立实现验证，也不是同行评审。历史独立 Python 精确算术检查保留原有证据范围，本轮完整 Lean 证明不将其冒称为外部独立验证。
复核包由 `build_review_bundle.py` 校验当前报告、源码、产物和日志哈希后生成，不包含编译缓存或工具链。
