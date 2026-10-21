# Thomson n=9 投稿包清单与外部评审交接

本清单记录提交一份"计算机辅助证明"论文所需材料、当前完成度，以及必须由外部作者/审稿人完成的事项。当前状态：**证明候选在本地闭合、独立算术复核通过；尚未外部同行评议，最终定理尚未形式化。**

## 1. 已可随投稿提交的材料

| 材料 | 位置 | 状态 |
|---|---|---|
| 英文论文稿（候选稿） | `proof_work/publication_validation/SUBMISSION_MANUSCRIPT_en.md` | 初稿，作者/单位/参考文献需补全 |
| 中文证明候选稿 | `proof_work/THOMSON_N9_PROOF_CANDIDATE_zh.md` | 完整论证，11 KB |
| 完整技术记录 | `proof_work/THOMSON_N9_CURRENT_zh.md` §13 | 70 KB，含历史失败记录 |
| 验证状态分层表 | `proof_work/publication_validation/VALIDATION_STATUS_zh.md` | 逐层 PASS/未形式化 |
| 独立检查器说明 | `README_independent_checker.md` 等六份 | 英文/中文，含负测 |
| 审稿包 | `proof_work/THOMSON_N9_REVIEW_BUNDLE.zip` | 202 条目、约 7.71 MB、逐文件 SHA-256 |
| Lean 工程源码 | `proof_work/publication_validation/formal/` | 部分形式化，见 README_build.md |
| 复算入口 | `proof_work/verify_thomson_n9_sharp.py` | 同实现重放，非独立实现 |

## 2. 投稿前必须由作者完成

1. **题目与作者信息**：论文稿中的作者、单位、通讯作者、基金信息均为占位。
2. **参考文献**：至少补齐 n≤8 的已知结果、区间/Bernstein 证书方法、Lean/Mathlib 形式化文献；当前仅列 5 条。
3. **期刊选择**：建议投向接受计算机辅助证明的期刊（如 *Experimental Mathematics*、*Mathematics of Computation*、*Journal of Symbolic Computation* 或 *Discrete & Computational Geometry*），并按目标期刊模板排版（LaTeX）。
4. **英文润色**：当前稿件为技术性初稿，需母语或专业润色。
5. **补充材料打包**：以审稿包 zip 为基础，按期刊要求补充 `README_REVIEW.txt` 与许可声明。
6. **作者声明**：明确"external review not yet performed; no claim of published solution"。

## 3. 审稿人最可能攻击的四个逻辑桥

这些是本地记录中已识别、尚未独立形式化的步骤。论文与审稿包必须把它们明确标出，不能藏在"验证通过"后面。

1. **45 个接触等式的推导**：33 个独立方程 + rank33/W 兼容性 ⇒ 45 个条件为零；需要逐行核对 12 个左关系与 132 个 anchor 矩分量。
2. **算术证书到实数不等式的语义**：每个 Bernstein/LDL/Hermite 证书如何对应精确的实数命题（区间包含、向外舍入、符号约定）。
3. **Hermite 次函数到局部边界图**：H≤f 的余项符号、27 次插值的节点区间、`u=b(v,t)` 图扩张与 ∂u R_H>0 的单调性传递。
4. **全域覆盖引理实例化**：`ordered_disjoint`/`gram_negative` 叶只排除可行域；必须把 `inside box x` 与 `x∈D` 绑定，边界乘子需 λ≥0 且 `R−λg≥0`、`g≥0`。

## 4. 已形式化 / 未形式化（Lean 4.34.1）

- 已形式化并通过第二内核（`leanchecker` exit 0）：`CoverageSoundness`、`DomainCoverage`（域受限覆盖，纯归纳无公理）、`Family`（候选坐标、36 距离引理、`energy_candidate`）、`CandidateMem`（单位范数、互异、`candidate_mem_sphere`）、`Derivative`（`familyEnergyDeriv`、`hasDerivAt_familyEnergy`）、`Stationary`（端点符号、连续性、介值定理、`exists_stationary_point`）、`SecondDerivative`（E''、`hasDerivAt_familyEnergyDeriv`、`familyEnergyDeriv2_pos`、Rolle 唯一性 `stationary_point_unique`/`exists_unique_stationary_point`）、`Minimum`（E' 严格单调 `strictMonoOn_familyEnergyDeriv`、唯一驻点为 (0,1) 上唯一严格全局极小点 `exists_unique_familyEnergy_min`、候选能量版 `energy_candidate_min`、合并命题 `exists_candidate_with_family_min`、区间严格单调 `familyEnergy_strictAntiOn_Ioo`/`familyEnergy_strictMonoOn_Ioo`）、`StrictConvex`（族能量严格凸 `strictConvexOn_familyEnergy`）、`EnergyContinuity`（互异构型上能量连续 `continuousOn_energy_injective`）、`Applications`（等距不变性 `energy_comp_isometry`、内积表示 `energy_eq_inner`、粗下界 `energy_ge_eighteen`、候选曲线导数 `hasDerivAt_energy_candidate`）、`ContactInner`（候选族六类内积 `A/B/C/D/F/G`）、`EnergyBounds`（直径界、逐对能量控制、`E≤U ⇒ 距离≥U⁻¹`、候选构型严格能量极小）、`DistanceValues`（候选族六类精确距离与距离-内积关系）、`GramBound`（物理域 Gram 约束的几何必然性、内积 `[-1,1]` 界）、`DomainChamber`（有序内积三元组的排序不变性）、`EnergyValue`（候选能量 `< 26` 的完全有理证书）、`EnergyForms`（能量齐次性 `energy_smul`、缩放导数 `hasDerivAt_energy_scale`、内积 rpow 形式 `energy_eq_sum_rpow`）、`PairDeriv`（直线路径上平方距离、范数与逆距离的导数 `hasDerivAt_norm_sq_affine`/`hasDerivAt_norm_affine`/`hasDerivAt_inv_norm_affine`，能量梯度的逐对求导入口）、`EnergyGradient`（`gradAt`、`inner_gradAt`、`energy_translate`、逐对和形式的 `hasDerivAt_energy_update`，以及组合恒等式 `sum_Ioi_ite_eq`、`pairSum_eq_inner_gradAt` 与梯度形式 `hasDerivAt_energy_update_gradAt`）。`EnergyPath`（`hasDerivAt_pair_inv_dist_path`、`sum_Iio_swap` 等重组引理与多点路径导数 `hasDerivAt_energy_path`）。`GradientZero`（`gradient_zero_iff_directional`、`hasDerivAt_energy_path_zero` 与 `stationary_iff_gradient_zero`）、`EnergyOptimality`（`inner_le_of_energy_le`、`local_min_gradient_zero`、`isLocalMin_gradient_zero`）、`EnergySymmetry`（`two_mul_energy`、`energy_perm`、`sphereConfig_perm`）、`Minimizer`（`feasibleShell` 紧性、非空性、能量连续性、`exists_global_minimizer` 与 `exists_global_minimizer_lt_26`）、`ThreePoint`（改编自 N=7 项目的 Bachoc–Vallentin 三点正性 `quad_Y3_nonneg`/`bv_positivity`）、`ThreePointBound`（约化核组合 `Rs`/`dsum_Rs`/`dsum_H`、矩阵核 `Rk`、`sum4_swap` 与精确三点恒等式 `three_point_identity`、以及见证式 SOS 三点界 `matDot_moment_nonneg_sos`/`three_point_bound_sos`、叶证书语义与覆盖组装 `terminal_sound`/`bisect_sound`/`covered_sound`、PSD 证书语义 `reduced_quadform_nonneg`/`reduced_sum_quadform_nonneg`）、`FinalAssembly`（冻结命题到全局下界的等价归约 `thomsonNineClaim_iff_global_lower_bound` 与 `thomsonNineClaim_of_pointwise`）、`Interval`/`IntervalMul`/`IntervalEval`/`IntervalTensor`（ℚ 端点区间算术 `RatInterval`/`add`/`mulNonneg`/`powNonneg` 的可靠性定理、带符号乘非负区间的 `mulMixed`、Bernstein 基函数区间包络 `bernInterval`/`mem_bernInterval`/`bernInterval_lo_nonneg`、三元乘积包络 `mem_mulMixed3`、有限和包络 `sumIntervals`/`mem_sumIntervals`、整张量求值 `evalTensor`/`evalTensor_sound`，以及 Bernstein 系数区间 ⇒ 张量非负的叶证书语义 `tensor_nonneg_of_coeff_intervals`）。
- 未形式化：45 个接触等式、PSD/局部证书到实数不等式的语义、68063 叶覆盖树实例化、最终命题 `ThomsonNineClaim`。

## 5. 外部复核建议流程

1. 从 zip 解压到全新目录，按 `README_REVIEW.txt` 先跑独立精确检查器（纯 Python）。
2. 复核 `sharp_root_tree.jsonl` 的节点/叶计数与 `pending=0`，并抽查 100 个叶子的证书语义。
3. 独立重实现 signed-128 Bernstein 引擎的一个子集，交叉验证若干盒。
4. 逐条核对四个逻辑桥；任何一条不通过即否定证明候选。
5. 若需证伪候选构型，需给出显式九点构型，其严格能量上界小于 E_* 的下界。

## 6. 一句话结论

材料层面已经可以送审；学术层面仍缺外部评议与形式化收尾。在获得外部评审之前，正确表述是"**locally rigorously verified proof candidate**"，不是"Thomson n=9 solved"。
