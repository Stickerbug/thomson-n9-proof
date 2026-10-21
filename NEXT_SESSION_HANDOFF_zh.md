# Thomson n=9 研究：会话交接（2026-10-17）

> 原会话 `session-ca65a138`（cwd `/home/dsh/Thomson Problem`）累积 12,502 条记录、32 轮，最后一次请求达 1,884,989 tokens（1,628,989 消息 + 256,000 回复），超过 deepseek-flash 的窗口 1,048,576；2026-10-17 13:36 起每轮重试约 23 分钟后返回 HTTP 400，无法继续。
> 本文件把该会话的进展、产物、未完成工作整理成可接手的材料。新会话的第一件事应是读本文件与 `proof_work/publication_validation/VALIDATION_STATUS_zh.md`。
>
> **2026-10-19 续跑**：上一会话 `session-345db606` 因上下文超限中断；接手状态与统一复核命令见 [`proof_work/publication_validation/CONTINUATION_2026-10-19_zh.md`](proof_work/publication_validation/CONTINUATION_2026-10-19_zh.md)。截至 2026-10-20 14:45 UTC，AAA `Base`、`Chunk00`–`Chunk07` 和组装 `LocalSparseHessianAAA` 全部编译；统一 `verify_local_lean.py --adopt-build` 返回 `LOCAL_LEAN_COMPILER_AXIOMS_AND_KERNEL_PASS`（620 条公理审计、91 模块闭包、`leanchecker` exit 0），复核包已重打（280 条目，约 16.5 MB）。该结果仍是本地、条件性的证明候选，不是最终定理，也无外审；真实残差/平移系数绑定、其余 11 类、45 个接触、68,063 叶覆盖与最终 `ThomsonNineClaim` 仍未形式化。状态见 [`proof_work/publication_validation/AAA_PARTIAL_STATUS_2026-10-19_zh.md`](proof_work/publication_validation/AAA_PARTIAL_STATUS_2026-10-19_zh.md)。

## 1. 用户目标（按时间，原话）

- 2026-10-16 09:11 建立 goal：「核实经典 Thomson 问题 n=9 的严格求解状态，调查关键文献和候选构型，研究证明或证伪现有候选解的可行方法，并形成有来源依据的中文研究报告。」
- 2026-10-16 09:35 修订：「持续研究经典 Thomson n=9 的严格全局证明：独立核验候选与文献，构建可复算的严格局部证书，探索全局能量下界与区域排除，尽可能推进到完整证明；严格区分数值证据、子族结论与全局证明。」
- 2026-10-17 08:34 修订（**当前 active 的目标**）：「推进 Thomson n=9 证明候选的发表级验证：冻结定理，导出完整覆盖证书，独立实现精确检查器和负向测试，开展 Lean 最终定理与第二内核验证；发现问题先修正，准确记录完成范围。」
- 2026-10-17 08:16 用户原话：「为了将这个学术成果能够得到发表，是否需要经过更加严格的验证，对于 n=7 这类的计算机辅助证明，他们是怎么做的，我们是否能做到跟他们相同或更好。」

## 2. 一句话现状

本地计算机辅助证明链已闭合、独立精确算术复核全部通过；Lean 工程已形式化候选几何、九点互异、族能量恒等式、族能量导数、驻点存在唯一性与族内严格全局极小性、以及域受限覆盖逻辑（Family/CandidateMem/Derivative/Stationary/SecondDerivative/Minimum/StrictConvex/EnergyContinuity/Applications/ContactInner/EnergyBounds/DistanceValues/GramBound/DomainChamber/EnergyValue/EnergyForms/PairDeriv/EnergyGradient/EnergyPath/GradientZero/EnergyOptimality/EnergySymmetry/Minimizer/ThreePoint/ThreePointBound/TreeSemantics/PSDSemantics/FinalAssembly/DomainCoverage，均通过第二内核 leanchecker），但**最终定理尚未 Lean 形式化**、**尚无外部同行评议**，因此只能表述为「本地严格验证的证明候选」，不能写成「Thomson n=9 已被解决」。

核心结论（来自 `THOMSON_N9_CURRENT_zh.md` §1）：

- 候选能量：`E_min(9) = E_D(r*) ≈ 25.75998653126983156407570227376049402864`（本次研究产物，待外审）。
- D3h 一参数族内唯一最优：已由严格凸性证明。
- 候选在完整构型空间严格局部最优：已有区间 Hessian 证书。
- 候选的全局最小能量：本地计算机辅助证明链闭合（136,125 节点全域认证 δ=0、pending=0），待外审。
- **最优构型的全局唯一性：未证明**，不要与最优性一起宣称。
- 公开资料仍将 n=9 严格全局问题列为未解；本次未找到已发表可核验的九点证明。

## 3. 权威文档（按阅读顺序）

1. `proof_work/publication_validation/VALIDATION_STATUS_zh.md`（11:34，最新）——分层验证状态表、覆盖结论的准确范围、仍需外部审查的 5 个数学桥梁。
2. `proof_work/THOMSON_N9_CURRENT_zh.md`（70 KB，08:03）——完整研究状态；§4–12 是研究历史，§13 是最终状态。
3. `proof_work/THOMSON_N9_PROOF_CANDIDATE_zh.md`（11 KB，08:03）——完整证明候选稿。
4. `proof_work/publication_validation/README_independent_checker.md`（18.8 KB，11:18）——独立检查器说明。
5. `proof_work/publication_validation/README_independent_contact_construction.md`、`README_independent_hermite_RH.md`、`README_independent_local_arithmetic.md`——分项独立核验说明。

## 4. 本会话最后阶段完成的工作（2026-10-17）

这些进展主要记录在会话消息里，部分已写入磁盘文档：

- **08:18–08:29 发表级验证差距分析**：对照 n=7 Lean 项目（`thomson-n7-lean`，commit `25f2fa5`）的六层验证做法——冻结数学陈述、精确数值证书、完整推导、公理依赖审查、第二内核（nanoda）、负向测试；结论是我们需要更严格验证，最大缺口是「独立实现的检查器」与「可审阅的完整数学证明」。另指出：八点仓库只对 Coulomb 情形做了 Lean 验证，不能整体称「已形式化」。
- **08:31「开始」**：冻结九点最终命题（`FrozenStatement.lean`：只有陈述，无占位证明），导出完整覆盖树：136,125 节点、68,062 分裂、68,063 叶。
- **08:31 turn 29 曾因 `preflight_compress_failed: context ~443244.69618479436 tokens` 失败一次**（当时仍在 OpenAI 模型上）。
- **10:09**：旧后台任务句柄丢失、整树检查未出结果，改为分片独立检查（154 个子域、4 个进程）。
- **10:23**：33 维接触方程独立重建区间偏宽，无法证明包含关系 → 收紧驻点区间重算。
- **10:55**：收紧后通过——190 个解坐标、756 个 F 系数、c、E*、F(1,1,1)、Hermite H27（28 个系数）与 807 个 R_H 系数逐项包含于原证书包围内。
- **11:21**：独立全树复核完成——136,125 节点、68,063 叶、pending=0（纯 Python 标准库 int/Fraction，不导入原 Bernstein/区间/C/signed128；约 47 分 34 秒）；50 组负向/失败传播测试通过；12 类局部算术独立通过；新 Hermite 纯代数证书成功（G=1−(2−2t)H²=WQ，Q 的 28 个 Bernstein 系数严格为正）。
- **11:34**：`VALIDATION_STATUS_zh.md` 落盘。
- **11:51**：中途切换到 deepseek-flash；turn 31（09:52 开始，历时 8,670 秒）与 turn 32（13:13–13:36）均以 HTTP 400 结束。
- **15:47–16:35**：`Family.lean`（显式候选坐标、36 个距离引理、`energy_candidate`）、`CandidateMem.lean`（单位范数、互异、`candidate_mem_sphere`）与 `DomainCoverage.lean`（域受限覆盖）编译通过；`#print axioms` 仅标准三公理；`leanchecker` 对 CoverageSoundness、DomainCoverage、Family、CandidateMem 四个模块 exit 0。
- **16:44–16:50**：Mathlib 缓存缺少 `Deriv/Support`、`Deriv/Mul`、`Deriv/Add`、`Deriv/Inv` 四个 olean，按固定源码就地补齐，`HasDerivAt` 的 sub/add/inv 组合子恢复可用。
- **17:03**：`Derivative.lean` 编译通过：`familyEnergyDeriv` 显式公式与 `hasDerivAt_familyEnergy : HasDerivAt familyEnergy (familyEnergyDeriv r) r`（0<r<1）；`Axioms.lean` 扩充后 `#print axioms` 仍只有标准三公理（17:07）。
- **17:05**：按 11:21 之后全部独立结果重打审稿包（含完整覆盖树导出、独立检查器及测试、154 片结果、六份复核说明、Lean 源码与逐文件 SHA-256）；旧包保留为 `.v0809.bak`。
- **17:13**：`leanchecker ThomsonNine.Derivative` exit 0（第二内核重放导数公式）。
- **17:20–18:49**：`Stationary.lean` 编译通过：`familyEnergyDeriv (1/2) < 0`、`familyEnergyDeriv (9/10) > 0`、`familyEnergyDeriv` 在 `[1/2,9/10]` 上连续、`exists_familyEnergyDeriv_zero`（介值定理）与 `exists_stationary_point`（存在 r∈(0,1) 使 HasDerivAt 且导数为零）；`#print axioms` 仍只有标准三公理；`Axioms.lean` 与根模块已扩充并重编译通过。
- **17:46–17:52**：补齐 Mathlib 缓存缺失的 oleans 以支持 Rolle 定理：
  `Analysis/Calculus/LocalExtr/Basic`、`Analysis/Calculus/LocalExtr/Rolle`、
  `Topology/ExtendFrom`、`Topology/Order/ExtendFrom`、`Topology/Order/Rolle`，均以直接 `lean` 从源码编译。
- **17:59**：`SecondDerivative.lean` 编译通过：`familyEnergyDeriv2`（E'' 显式式）、
  `hasDerivAt_familyEnergyDeriv`、`familyEnergyDeriv2_pos`（`0<r<1` 时 E''>0）、
  `continuousOn_familyEnergyDeriv_Ioo`、`stationary_point_unique`、`stationary_point_unique'`、
  `exists_unique_stationary_point`（族驻点存在且唯一）；18:01 `Axioms.lean` 重编译，
  `#print axioms` 只含标准三公理；根模块重编译 `ROOT_OK`。
- **18:12**：`leanchecker ThomsonNine.SecondDerivative` exit 0（E'' 正性与 Rolle 唯一性重放）；
- **18:20–18:40**：为 `Minimum.lean` 从源码补编译 Mathlib 的 `Deriv/Linear`、`Deriv/AffineMap`、`Deriv/Slope`、`LinearAlgebra/AffineSpace/Slope`、`Topology/Perfect`、`Topology/Algebra/Module/PerfectSpace`、`Deriv/MeanValue`；
- **18:47–18:50**：`Minimum.lean` 编译通过：E' 在 (0,1) 严格单调、`familyEnergy_strictAntiOn`/`familyEnergy_strictMonoOn`、`familyEnergy_min`、`exists_unique_familyEnergy_min`（唯一驻点是唯一严格全局极小点）、`energy_candidate_min`；18:51 `Axioms.lean` 重编译（标准三公理）、根模块 `ROOT_OK`；
- **01:14–01:21**：`StrictConvex.lean` 以 `strictConvexOn_of_deriv2_pos` 证明 `strictConvexOn_familyEnergy`（族能量在 (0,1) 上严格凸，需从源码补编译 `Analysis/Convex/Deriv`）；`EnergyContinuity.lean` 证明 `continuousAt_energy_of_injective` 与 `continuousOn_energy_injective`（互异构型上能量连续）；`Axioms.lean` 增至 30 条审计，根模块 `ROOT_OK`；`leanchecker` 对 StrictConvex 与 EnergyContinuity 均 exit 0；01:29 审稿包重打为 178 条目；
- **01:50–02:15**：`Applications.lean`（能量等距不变性 `energy_comp_isometry`、`SphereConfig` 等距闭包、粗下界 `energy_ge_eighteen`、内积表示 `energy_eq_inner`、候选曲线导数 `hasDerivAt_energy_candidate`、非空性）与 `ContactInner.lean`（候选族六类内积 A/B/C/D/F/G）编译通过；`Axioms.lean` 增至 44 条审计、根模块 `ROOT_OK`；`leanchecker` 对 Applications 与 ContactInner 均 exit 0；02:21 审稿包重打为 180 条目、约 7.64 MB；
- **02:34–02:37**：`EnergyBounds.lean` 编译通过（直径界、逐对能量控制、`E≤U ⇒ 距离≥U⁻¹`、候选构型严格能量极小、合并存在命题）；`Axioms.lean` 增至 50 条审计、根模块 `ROOT_OK`、`leanchecker` 对 EnergyBounds exit 0；02:43 审稿包重打为 181 条目、约 7.65 MB；
- **02:47–02:52**：`DistanceValues.lean` 编译通过（六类精确距离、距离-内积关系）；`Axioms.lean` 增至 59 条审计、根模块 `ROOT_OK`、`leanchecker` 对 DistanceValues exit 0；03:02 审稿包重打为 182 条目、约 7.65 MB；03:40 增至 183 条目；04:40 增至 184 条目；06:35–07:19：`EnergyGradient.lean` 编译通过（`gradAt`、`inner_gradAt`、`energy_translate`、逐对和形式 `hasDerivAt_energy_update`，以及组合恒等式 `sum_Ioi_ite_eq`、`pairSum_eq_inner_gradAt` 与梯度形式 `hasDerivAt_energy_update_gradAt`），`Axioms.lean` 增至 80 条审计，根模块 `ROOT_OK`，`leanchecker` 对 EnergyGradient exit 0；
- 07:55–08:03：`EnergyPath.lean` 编译通过（`hasDerivAt_pair_inv_dist_path`、`sum_Iio_swap`、`sum_univ_ite_eq_sum_erase`、`sum_erase_eq_sum_Iio_add_Ioi`、`hasDerivAt_energy_path`），`Axioms.lean` 增至 85 条审计，根模块 `ROOT_OK`，`leanchecker` 对 EnergyPath exit 0；
- 09:15–09:22：`EnergySymmetry.lean` 编译通过；`two_mul_energy`、`energy_perm`、`sphereConfig_perm` 通过公理审计与第二内核重放。
- 09:40–09:55：`Minimizer.lean` 编译通过（`feasibleShell` 紧性、非空性、能量连续性、`exists_global_minimizer`、`exists_global_minimizer_lt_26`），`Axioms.lean` 审计通过（标准三公理），根模块导入并经 `leanchecker` 重放。
- 10:46–10:52：`DomainChamber.lean` 编译通过（`gram_swap12/23/13`、`exists_ordered_domain_triple`、`exists_ordered_gram_constraint_of_mem`），证明有序腔排序不改变 Gram 约束；
- 10:25–10:30：`FinalAssembly.lean` 编译通过（`thomsonNineClaim_iff_global_lower_bound`、`thomsonNineClaim_of_pointwise`），把冻结命题等价归约为“存在驻点 r，其族能量为全空间下界”；Axioms 审计、根模块与 `leanchecker` 重放通过。
- 15:39–15:48：新增 `IntervalEval.lean`：`oneMinus`/`oneMinus_lo_nonneg`、`bernInterval`（`[0,1]` 子区间上 Bernstein 基函数的区间包络）与 `mem_bernInterval`；编译通过，`Axioms.lean` 137 条依赖（标准三公理），根模块 `ROOT_OK`，`leanchecker ThomsonNine.IntervalEval` exit 0；15:48 审稿包重打为 202 条目、约 7.71 MB；16:00–16:07 为 `IntervalEval.lean` 增补 `bernInterval_lo_nonneg` 与 `mem_mulMixed3`（三元乘积包络），`Axioms.lean` 139 条依赖、根模块 `ROOT_OK`、`leanchecker` exit 0，审稿包 16:07 重打；16:24–16:35 新增 `IntervalSum.lean`（`sumIntervals`/`mem_sumIntervals` 有限和包络），`Axioms.lean` 140 条依赖、根模块 `ROOT_OK`、`leanchecker` exit 0，审稿包 16:35 重打为 203 条目；17:20–17:40 新增 `IntervalTensorEval.lean`（`evalTensor`/`evalTensor_sound` 整张量区间求值），`Axioms.lean` 142 条依赖、根模块 `ROOT_OK`、`leanchecker` exit 0，审稿包 17:40 重打为 204 条目。
- 15:23–15:33：新增 `IntervalMul.lean`：`mulMixed`（任意区间 × 非负区间的三分支角点乘法）与 `mem_mulMixed` 可靠性定理，编译通过；`Axioms.lean` 审计只含标准三公理，根模块 `ROOT_OK`，`leanchecker ThomsonNine.IntervalMul` exit 0；15:33 审稿包重打为 201 条目、约 7.70 MB。
- 13:38–13:57：新增 `Interval.lean`（ℚ 端点区间 `RatInterval`、`mem`、`const`/`add`/`neg`/`sub`/`scale`/`mulNonneg`/`powNonneg` 及逐运算可靠性定理）与 `IntervalTensor.lean`（`tensor_nonneg_of_coeff_intervals`：每个 Bernstein 系数落在下界非负的有理区间 ⇒ 张量在单位立方非负，即逐叶证书判据）；两者编译通过，`Axioms.lean` 审计均为标准三公理、无 `sorryAx`，根模块 `ROOT_OK`，`leanchecker` 对两模块均 exit 0；13:57 审稿包重打为 200 条目、约 7.69 MB（逐文件 SHA-256 复验 0 不匹配，旧包 `.v1355.bak`）。
- 13:20–13:35：新增 `PSDSemantics.lean`：`dotProduct_mulVec_nonneg_real`、`reduced_quadform_nonneg`、`sum_quadform_nonneg`、`reduced_sum_quadform_nonneg`（PSD 块 ⇒ 非负二次型；有限块组装），编译通过并进入 Axioms/root/leanchecker。
- 13:05–13:20：`TreeSemantics.lean` 增加锐根盒 `rootBox = [-1,14/25]³`、`physicalOrdered_mem_rootBox`（物理域含于根盒）与收尾 `covered_sound_root`（根盒上的检查树 ⇒ 全物理域 `0 ≤ R`）。编译通过。
- 12:45–13:05：新增 `TreeSemantics.lean`：`Box3`/`inBox`/`Bisect`/`Terminal`（Bernstein 证书或域排除）、`terminal_sound`、`bisect_sound`、`covered_sound`（任意有限二分树 + 叶证书 ⇒ 物理域上 `0 ≤ R`）。编译通过，进入 Axioms/root/leanchecker 验证。
- 12:30–12:45：`ThreePointBound.lean` 增加见证式 SOS 版本 `matDot_moment_nonneg_sos` 与 `three_point_bound_sos`（PSD 假设换成显式秩一平方和分解），编译通过并进入 Axioms/root/leanchecker 验证。
- 11:00–11:25：`ThreePointBound.lean` 编译通过（`dsum` 组合、约化核 `Rs`/`dsum_Rs`/`dsum_H`、Gram OK、矩阵核 `Rk`、`sum4_swap`、精确三点恒等式 `three_point_identity`；改编自 N=7 项目，`three_point_bound` 以见证式 SOS 形式补齐：`matDot_moment_nonneg_sos`/`three_point_bound_sos`），Axioms 117 条审计只含标准三公理，root 与 leanchecker 通过。
- 10:08–10:22：`Minimizer` 与 `ThreePoint` 均通过第二内核 `leanchecker`（exit 0）；`ThreePoint` 相关 Axioms 审计（`quad_Y3_nonneg`/`sum_S3_eq_sum_Y3`/`bv_positivity`/`exists_tangent_frame`/`Q3_eq_re`）只含标准三公理；审稿包 10:22 重打。
- 09:57–10:04：`ThreePoint.lean` 编译通过（改编自 N=7 Lean 项目的 Bachoc–Vallentin 三点正性：`quad_Y3_nonneg`、`bv_positivity`）；`matDot_moment_nonneg` 因 `Mathlib.Analysis.InnerProductSpace.Positive` 依赖闭包过深而显式延后。
- 08:58–09:08：`EnergyOptimality.lean` 编译通过；`inner_le_of_energy_le`、`local_min_gradient_zero`、`isLocalMin_gradient_zero` 通过公理审计与第二内核重放。
- 08:40–08:47：`stationary_iff_gradient_zero`（驻点 ⇔ 梯度为零）加入 `GradientZero.lean` 并编译通过，Axioms 审计通过，根模块重建成功。
- 08:14–08:29：`GradientZero.lean` 编译通过（`gradient_zero_iff_directional`、`hasDerivAt_energy_path_zero`），`Axioms.lean` 增至 87 条审计，根模块 `ROOT_OK`；06:13 增至 186 条目（含 EnergyForms、PairDeriv）；07:02 增至 187 条目（含 EnergyGradient）；
- **03:33–03:36**：`GramBound.lean` 编译通过（`gram_inner_nonneg`、`inner_mem_Icc_of_unit/mem`、`gram_constraint_of_mem`）；`Axioms.lean` 增至 63 条审计、根模块 `ROOT_OK`、`leanchecker` 对 GramBound exit 0；
- **04:28–04:35**：`EnergyValue.lean` 编译通过（`familyEnergy (7/10) < 26`、`familyEnergy r* < 26`、`energy (candidate r*) < 26`）；`Axioms.lean` 增至 66 条审计、根模块 `ROOT_OK`、`leanchecker` 对 EnergyValue exit 0；
- **05:00–05:24**：`EnergyForms.lean` 编译通过（能量齐次性 `energy_smul`、缩放导数 `hasDerivAt_energy_scale`、内积 rpow 形式 `energy_eq_sum_rpow`）；`Axioms.lean` 增至 69 条审计、根模块 `ROOT_OK`、`leanchecker` 对 EnergyForms exit 0；
- **05:37–06:13**：`PairDeriv.lean` 编译通过（直线路径导数 `hasDerivAt_affine`、平方距离导数 `hasDerivAt_norm_sq_affine`、范数导数 `hasDerivAt_norm_affine`、逆距离导数 `hasDerivAt_inv_norm_affine`；需从源码补编译 Mathlib `Analysis/InnerProductSpace/Calculus` 及其依赖 `Normed/Module/Ball/Homeomorph`、`Topology/OpenPartialHomeomorph/Composition`、`Calculus/ContDiff/WithLp`、`Calculus/FDeriv/WithLp`）；`Axioms.lean` 增至 73 条审计、根模块 `ROOT_OK`、`leanchecker` 对 PairDeriv exit 0；06:13 审稿包重打为 186 条目、约 7.66 MB；

- **00:16–00:18**：`Minimum.lean` 增补区间严格单调 `familyEnergy_strictAntiOn_Ioo`（(0,r*) 严格递减）与 `familyEnergy_strictMonoOn_Ioo`（(r*,1) 严格递增）；`Axioms.lean` 增至 27 条审计、根模块 `ROOT_OK`、`leanchecker` 重放；
  复核包重打为 175 条目、约 7.63 MB，逐文件 SHA-256 复验通过；`VALIDATION_STATUS_zh.md`、
  英文论文初稿、投稿清单与根模块均已更新。
- **17:16**：审稿包加入英文论文初稿 `SUBMISSION_MANUSCRIPT_en.md` 与投稿清单 `SUBMISSION_CHECKLIST_zh.md`，173 个文件、7.63 MB，逐文件 SHA-256 复验通过。

## 5. 未完成 / 下一步

1. **Lean 最终定理**（最大缺口）
   - 已完成：`formal/ThomsonNine/Family.lean` 用显式柱坐标 `p r` 形式化候选九点，36 个距离倒数引理、`candidate_eq_p`、`familyEnergy_alt`、`energy_p`、`energy_candidate` 编译通过；`CandidateMem.lean` 证明 `norm_p_eq_one`、`injective_p`、`candidate_mem_sphere`；`DomainCoverage.lean` 给出域受限覆盖引理 `coverage_sound_on_domain`；`Derivative.lean` 给出 `familyEnergyDeriv` 与 `hasDerivAt_familyEnergy`；`Stationary.lean` 给出端点符号、连续性与 `exists_stationary_point`；`SecondDerivative.lean` 给出 E''、`hasDerivAt_familyEnergyDeriv`、E''>0 与 Rolle 唯一性 `stationary_point_unique`/`exists_unique_stationary_point`；`Minimum.lean` 给出 E' 严格单调、`familyEnergy_min`、`exists_unique_familyEnergy_min` 与候选能量版 `energy_candidate_min`、区间严格单调 `familyEnergy_strictAntiOn_Ioo`/`familyEnergy_strictMonoOn_Ioo`、族能量严格凸性 `strictConvexOn_familyEnergy`、以及互异构型上能量连续性 `continuousOn_energy_injective`、能量等距不变性与内积表示（`energy_comp_isometry`、`energy_eq_inner`、`energy_ge_eighteen`）和候选族六类内积（`ContactInner` 的 `A/B/C/D/F/G`）、逐对路径导数（`PairDeriv`）、`EnergyPath`（多点路径导数）、`GradientZero`（梯度-驻点等价）、`EnergyOptimality`（一阶最优性）、`EnergySymmetry`（置换不变性）、`Minimizer`（`feasibleShell` 紧性与全局极小元存在性）、`ThreePoint`（改编自 N=7 项目的 Bachoc–Vallentin 三点正性，一般 PSD 配对延后）、`ThreePointBound`（`dsum` 组合、约化核 `Rs`/`dsum_Rs`/`dsum_H`、Gram OK、矩阵核 `Rk`、`sum4_swap` 与精确三点恒等式 `three_point_identity`）与单点移动的能量梯度逐对和及其梯度形式（`EnergyGradient` 的 `gradAt`、`inner_gradAt`、`energy_translate`、`hasDerivAt_energy_update`、`sum_Ioi_ite_eq`、`pairSum_eq_inner_gradAt`、`hasDerivAt_energy_update_gradAt`），以及 `FinalAssembly`（冻结命题到全局下界的等价归约 `thomsonNineClaim_iff_global_lower_bound`/`thomsonNineClaim_of_pointwise`）与 `DomainChamber`（有序内积三元组的排序不变性）。`#print axioms` 只含 `propext, Classical.choice, Quot.sound`。
   - 缺：45 个接触等式、实际 PSD 块/局部 Hessian 区间与真实残差的绑定、68063 叶全域证书实例化（局部通用语义、解析接口和 12 类具体条件 LDL 递推已补充，见文末最新进展），以及 `ThomsonNineClaim` 本身；最优构型的全局唯一性同样未证明。（族驻点及族内唯一严格极小点已形式化；r*≈0.7105483340929538 的数值定位未形式化；逐对路径导数、单点移动的能量梯度逐对和及其内积形式已形式化（`PairDeriv`、`EnergyGradient` 的 `hasDerivAt_energy_update`、`sum_Ioi_ite_eq`、`pairSum_eq_inner_gradAt`、`hasDerivAt_energy_update_gradAt`），45 个接触等式现在可写成 `⟪v, gradAt (candidate r) i⟫ = 0` 的零点条件，下一步是实例化这 45 个方向与相应对。）
   - 固定版本：Lean 4.34.1，Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`；工程在 `proof_work/publication_validation/formal/`；构建方式见 `formal/README_build.md`（lake 在容器内不可用，用 `build_direct.sh` 直接调用 lean）。
2. **第二内核**：`leanchecker` 已独立重放 CoverageSoundness、DomainCoverage、Family、CandidateMem、Derivative、Stationary、SecondDerivative、Minimum、StrictConvex、EnergyContinuity、Applications、ContactInner、EnergyBounds、DistanceValues、GramBound、DomainChamber、EnergyValue、EnergyForms、PairDeriv、EnergyGradient、EnergyPath、GradientZero、EnergyOptimality、EnergySymmetry、Minimizer、ThreePoint、ThreePointBound、FinalAssembly（exit 0）；仍需把 68063 叶证书与最终定理导出后交独立实现（如 nanoda）复核。
3. **45 个接触等式的逻辑桥**：33 个方程的独立算术通过 ≠ 逻辑蕴含；需要 rank33/W 兼容性与真驻点条件的严格论证（这是外部审查桥梁第 3 条）。
4. **重打审稿包**：已于 06:13 完成（186 条目、约 7.66 MB、逐文件 SHA-256、`build_review_bundle.py` 可重跑）；13:25 重打为 198 条目（含 TreeSemantics、PSDSemantics 与 13:00 后的文档修订）；13:55 重打为 200 条目（新增 Interval、IntervalTensor）；15:33 重打为 201 条目（新增 IntervalMul）；15:48 重打为 202 条目（新增 IntervalEval）；旧包保留为 `.v0809.bak`、`.v1736.bak`、`.v1738.bak`、`.v1740.bak`、`.v1744.bak`、`.v1922.bak`、`.v0023.bak`、`.v0129.bak`、`.v0131.bak`、`.v0130.bak`、`.v0221.bak`、`.v0243.bak`、`.v0302.bak`、`.v0340.bak` 、`.v0640.bak`、`.v0613.bak`、`.v1040.bak`、`.v1100.bak` 与 `.v1135.bak`。
5. **全局唯一性**：单独研究，不能与最优性一起宣称。
6. **外部评审**：数学证明、语义桥、题目陈述都需要外部专家复核。

## 6. 关键产物

| 产物 | 位置 | 说明 |
|---|---|---|
| 最终状态 | `proof_work/THOMSON_N9_CURRENT_zh.md` §13 | 70 KB，08:03 |
| 证明候选稿 | `proof_work/THOMSON_N9_PROOF_CANDIDATE_zh.md` | 11 KB，08:03 |
| 英文论文初稿 | `proof_work/publication_validation/SUBMISSION_MANUSCRIPT_en.md` | 17:10，作者/文献待补 |
| 投稿清单 | `proof_work/publication_validation/SUBMISSION_CHECKLIST_zh.md` | 17:10，含四个待审逻辑桥 |
| 验证状态 | `proof_work/publication_validation/VALIDATION_STATUS_zh.md` | 01:29，含 Minimum/StrictConvex/EnergyContinuity 与复核包 |
| 独立检查最终结果 | `proof_work/publication_validation/independent_publication_final.json` | 11:17，含各组件 sha256 绑定 |
| 独立检查器文档 | `proof_work/publication_validation/README_independent_checker.md` | 11:18 |
| 冻结命题 | `proof_work/publication_validation/FrozenStatement.lean` | 09:27 |
| Lean 覆盖引理 | `proof_work/publication_validation/CoverageSoundness.lean`（及 `.olean`） | 09:18 |
| Lean 工程 | `proof_work/publication_validation/formal/` | Lean 4.34.1 + 固定 Mathlib |
| 审稿包 | `proof_work/THOMSON_N9_REVIEW_BUNDLE.zip` | 约 16.5 MB，2026-10-20 14:45 重打，280 条目；含 620 条审计/90 模块的 PASS 报告/stamp、AAA 全部模块与 255/807 条件绑定；旧包归档为 `THOMSON_N9_REVIEW_BUNDLE_2026-10-20_1408.zip` |
| 审计清单 | `proof_work/SHARP_N9_REVIEW_MANIFEST.json` | 15:48，逐文件 SHA-256（202 条目）|

## 7. 文件完整性与已知问题

写工具在这个环境会留下坏的 l2s 符号链接（指向已被清理的 `.tmpdir`）。注意本机 `find . -xtype l` 会漏报（返回 0），且对这些条目 `os.path.islink`/`test -L` 也返回假（lstat 被拦截），只能用 `readlink` 拿到路径、用 `head -c1` 判断内容是否可读。**新会话写文件请用 bash heredoc，不要用 write 工具。**

### 已于 2026-10-17 14:14 就地恢复（12 个，替换坏链，权限 590）

| 文件 | 大小 | 来源 |
|---|---|---|
| `proof_work/three_point_defect_identity_zh.md` | 2,050 B | 会话语料 write |
| `proof_work/two_cap_capacity_lemma_zh.md` | 1,648 B | 会话语料 write |
| `proof_work/external_pair_field_normalization_zh.md` | 2,290 B | 会话语料 write |
| `proof_work/sixq_two_cap_lemma_zh.md` | 2,917 B | 会话语料 write |
| `proof_work/competitive_kernel_constraint_v1.py` | 2,255 B | 会话语料 write，py_compile 通过 |
| `proof_work/certify_uniform_pair_lp_gap.py` | 2,045 B | 会话语料 write，py_compile 通过 |
| `proof_work/fixed_triangle_analytic_neighborhood_parent_v1.py` | 4,344 B | 会话语料 write，py_compile 通过 |
| `proof_work/verify_sharp_global2026.py` | 6,725 B | 会话语料 write，py_compile 通过 |
| `proof_work/analytic10_2026_mathematics_zh.md` | 4,315 B | 会话语料 write |
| `proof_work/THOMSON_N9_PUBLICATION_VALIDATION_zh.md` | 9,952 B | 残留 tmpdir（比会话版长，应为最终版） |
| `proof_work/explore_fixed_triangle_q_min_v1.py` | 3,734 B | 残留 tmpdir，py_compile 通过（但 import numpy/scipy，当前环境无此依赖） |
| `proof_work/d10_candidate_moment_identity_v1.py` | 7,397 B | 残留 tmpdir，py_compile 通过 |

恢复内容来自 2026-10-17 旧会话的 write 调用或 tmpdir 残留；除 `py_compile` 外**未重新运行验证**，引用其数值结论前请先复核。

### 仍损坏（约 20 处）

- 需关注（17 个）：`proof_work/publication_validation/independent_checker.py`（lstat EPERM）、`d12_contact2026_run.py`、`d12_fourpoint_screen2026_probe.py`、`sharp_contact_refinement2026_diagnostics.py`、`d12_contact2026_batch2_design_note_zh.md`、`certify_d4_sharp_obstruction.py`、`fixed_anchor_moment2026_probe.py`、`sixq_two_cap_discovery_v1.py`、`sixq_dual2026_t2_sample_psd.py`、`external_pair_interval2026_attempt.py`、`d10_ridge_repair2026_b2_solver.py`、`narrowroot2026_notes.md`、`nonsharp_nullspace_actualf_d10_notes_zh.md`、`t1_neighborhood_sensitivity2026_proof_zh.md`、顶层 `n9_literature.md`、顶层 `Thomson_n9_research_zh.md`（其 write 内容只是 41 字符占位）。
- 仅是残留（3 处，可忽略/可删）：`d10_candidate_moment_identity_v1.py encoding`（重名残留）、`.sharp_contact_refinement2026_diagnostics.py.*.tmpdir/*.tmp`、`.d12_fourpoint_screen2026_probe.py.*.tmpdir/*.tmp`。
- 这些多由子代理或 bash heredoc 写入；内容可能还在子会话日志里（36 个子会话目录），需要时可解码查找。

### 不受影响的关键产物（均为真实文件）

`THOMSON_N9_CURRENT_zh.md` 70,142 B、`THOMSON_N9_PROOF_CANDIDATE_zh.md` 11,315 B、`VALIDATION_STATUS_zh.md` 4,985 B、`CoverageSoundness.lean` 1,341 B、`independent_publication_final.json` 4,786 B；`publication_validation/` 下 `checker_exact.py`（9,720 B）、`sharded_checker.py`（15,574 B）、`independent_*.py` 系列、33 MB 的 `sharp_root_tree.jsonl` 与各 `independent_*_result.json` 都在。`independent_checker.py` 缺失不等于没有检查器，`checker_exact.py` + `sharded_checker.py` 是实际实现。

### 其他

- `n9_explore.py` 已于 2026-10-17 从旧会话恢复为普通文件（5,745 B，`py_compile` 通过）；它是浮点探索脚本，不是证书；运行会在当前目录写 `n9_numerics.json`。
- 原会话 32 轮就吃满 1.88 M tokens，主要来自整文件读取与长日志。新会话请用 `grep`/定点读取，长结果写文件，单会话到 20–30 万 tokens 就落盘结论、开新会话。

## 8. 新会话开场建议

```
先读 NEXT_SESSION_HANDOFF_zh.md 和 proof_work/publication_validation/VALIDATION_STATUS_zh.md，
继续推进 Thomson n=9 证明候选的 Lean 最终定理（从 CoverageSoundness 的覆盖引理接到具体算术证书）
与第二内核复核。保持「未形式化、未外审，不宣称已解决」的表述。先给出计划，不要整读大文件。
```

## 9. 备注

- 本次交接只从会话中提取了结论与进度，没有改动 `proof_work/` 下的任何证明产物。
- 需要更细的历史（每轮工具调用、子代理结果、被删除文件的内容）时，可解码 `/home/dsh/.dsh/sessions/--home-dsh-Thomson~0020Problem--/session-ca65a138-619f-461a-bdc3-0369e0d8ab95/session.v4.jsonl.zstd`（zstd 多帧容器，逐帧解码后共 12,502 条记录、41.6 MB）。
