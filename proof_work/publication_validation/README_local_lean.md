# 完整 Lean 证明与统一验证

冻结 `ThomsonNineClaim` 已由 `ThomsonNine.thomsonNineClaim_proved` 证明。当前统一结果：**2390 模块、1507 项公理审计、807/807 个不同归档系数目标；完整 fresh 重放 13228.2 秒**。详情见 [最终证明记录](GLOBAL_THEOREM_2026-10-22_zh.md)。

```bash
export LEAN_BIN_DIR=/path/to/lean-4.34.1/bin
python3 -B proof_work/publication_validation/verify_local_lean.py
```

固定 Lean 4.34.1 与 Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`；保留 `formal/.lake`。验证器按依赖编译显式登记的源码，再检查正式 root、LocalVerification、公理输出和所有导出输入，最后运行单次完整 `leanchecker --fresh ThomsonNine.LocalVerification`。

匹配 PASS 戳后可用 `--reuse-local-build`；采用已有产物用 `--adopt-build`。本轮通过保留原模块名采用已有编译结果，再做完整 fresh 重放。`packed_coverage_manifest.json` 登记原名模块及源码哈希；未登记的本地导入会被拒绝。历史 Construction 副本不参与当前导入闭包。

公理仅允许 `propext`、`Classical.choice`、`Quot.sound`。全部实际 F/c、807 源系数、45 条接触方程、12 局部邻域、根张量、一维下界和 68063 叶覆盖均已接入最终定理。

内置 Lean 内核重放不等于外部独立验证。冻结命题证明全局最小能量，没有证明所有最优构型的全等唯一性。历史阶段的“待证明”描述应按其日期和范围理解。
