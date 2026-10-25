# n=10 候选发现接入规范（2026-10-25）

这份记录把真实十粒子问题的下一步固定成一个可审计的接入阶段。当前项目已经有一个 D4d 对称族候选、精确的十点几何与能量恒等式，以及一维驻点的区间数据；但还没有可接受的 n=10 全局下界证书或完整 Lean 适配器，因此清单 `n10_discovery.json` 仍必须返回 `UNKNOWN`。这不是失败的定理，也不是 n=10 结果。

## 现状边界

仓库中名称带 `analytic10` 或 `d10` 的大部分旧文件是 n=9 的十阶三点核/多项式实验：它们仍使用 n=9 的 84 个无序三元组、729 个有序三元组和 n=9 候选能量。它们可以作为方法学参考，不能填充本规范的十粒子全局字段，也不能作为 n=10 全局证明。真正的 n=10 发现材料是 `n10_*` 文件及 `ThomsonCertificate/N10D4dGeometry.lean`、`N10CandidateInterval.lean`。

## 接受一个 n=10 候选所需的最小数据

候选搜索可以使用浮点优化；进入证明阶段前必须导出以下可复核数据：

1. `candidate.json`：十个单位球面点的精确代数表示，或带有可在 Lean 中使用的有理端点/误差证书的区间表示；
2. `model.json`：十粒子 Thomson 能量、归一化约定和从原能量到低维残差的等式；
3. `symmetry.json`：候选的置换/旋转对称性、参数数目和去重规则；
4. `contact.json`：接触关系、接触方程、秩与兼容性证书；
5. `certificate.json`：局部非负性、PSD 块、覆盖树和每个叶子的终止原因；
6. `generated/Instance.lean`：只引用上述精确数据并由 Lean 内核检查的适配器。

缺少任一层时，状态最多为 `CANDIDATE_ONLY` 或 `UNKNOWN`。数值能量、未经误差界包围的坐标、外部仓库的定理名称和文件名相似性都不能提升状态。

## 阶段门

```text
DISCOVERY_PENDING
  -> CANDIDATE_ACCEPTED
  -> MODEL_REDUCED
  -> CERTIFICATE_COMPILED
  -> GLOBAL_REPLAY
```

每一门都要留下输入哈希、生成器版本、命令和输出。只有最后一门完成后，才允许把 n=10 清单改为 `verified_adapter` 并报告 `PASS`。当前状态是 `DISCOVERY_PENDING`。本轮短时、固定种子的 32 次 L-BFGS-B 搜索产生了一个数值提案，能量约为 `32.71694946014815`，并观察到一个近似对跖点对；结果保存在 `n10_numerical_candidate_proposal_2026-10-24.json`。该提案仍是浮点数据，尚未通过精确化、接触方程、全局下界或 Lean 重放，因此不会改变 UNKNOWN 状态。 进一步把点集拟合为“一对对跖极点 + 两个相差 45° 的方形环”的一参数族，得到 `h = 0.422687424043986066...`。`ThomsonCertificate/N10D4dGeometry.lean` 现在已由 Lean 验证 (0<h<1) 时十点构型两两不同、位于单位球面，并把 45 个点对的距离倒数汇总为精确 D4d 能量公式；这仍只是对称族候选。 对该一参数驻点条件的精确符号消元得到一次 224 次因子；它是必要条件的候选代数载体，因消元引入的多余根和未完成根隔离，仍不能作为定理。 随后用精确有理 Bernstein 证书隔离出区间 `[63701661910807/10^14, 63701661910808/10^14]` 内唯一结果式根；原始含根号分支在同一区间端点通过纯有理区间算术得到相反严格符号，且同一算术把 D4d 族能量包围在约 `[32.71694946014744, 32.71694946014774]` 内。`ThomsonCertificate/N10CandidateInterval.lean` 已由 Lean 内核验证该有理 `t` 区间映射到有理 `h` 区间，并证明驻点表达式在该区间连续，以及端点变号时由 IVT 得到区间内零点。端点符号目前仍由外部纯有理区间证书提供，尚未在 Lean 中重放；整个十点构型空间的全局下界也尚未建立。具体分支表和根处残差仍是高精度数值检查。

独立证书 `n10_stationarity_endpoint_certificate_2026-10-25.json` 另外记录两个端点的完整有理区间运算链和严格符号，供 Lean 重放时逐项对照。`ThomsonCertificate/N10StationarityEndpoint.lean` 已先完成无 `sorry` 的区间原语重放（倒数、平方根、\(\sqrt2\) 有理包围和端点成员）；最终驻点表达式符号尚未接入该文件。

本轮还加入 `proof_work/n10_rational_lp_bound_2026-10-25.py/json`：它用纯 `Fraction` 和 25 次 Bernstein 细分给出无条件基线
\[
 E_{10}\ge 326807/10000=32.6807.
\]
该下界距 D4d 候选约 `0.03624946015`，没有关闭最优性缺口；它是外部精确算术证书，不是 Lean 定理。方法迁移、规模和不可直接替换的 n=9 固定数据见 `N10_GLOBAL_BOUND_PROGRESS_2026-10-25_zh.md` 与 `N10_GLOBAL_BOUND_FRAMEWORK_ANALYSIS_2026-10-25_zh.md`。

进一步的 `n10_three_point_sdp_discovery_2026-10-25.py/json` 在 degree 8 的有限采样和差分进化 SDP 中得到约 `32.71694946` 的候选目标，但六轮运行的最新验证仍有约 `-5.95e-5` 的负残差，故只能用于寻找三点核/局部覆盖数据，不能改写 `UNKNOWN` 状态。
degree-10 的独立诊断记录在 `n10_three_point_sdp_discovery_degree10_2026-10-25.json`，最新最坏残差约 `-5.31e-4`，没有关闭缺口。
Clarabel/SCS 对比记录在 `N10_SDP_SOLVER_COMPARISON_2026-10-25_zh.md`，进一步确认浮点 SDP 只能作发现工具，不能用来改变 `UNKNOWN` 门禁。
约化候选 Gram 零空间的后续诊断见 `N10_REDUCED_THREE_POINT_SDP_2026-10-25_zh.md`；它提高了数值稳定性，但没有全局覆盖。
候选 120 个三角形的符号分类见 `N10_CANDIDATE_TRIPLE_TYPES_2026-10-25_zh.md`；该分类可用于下一步局部/边界证书生成，但本身不是全局证明。

## 可执行入口

`run_certificate_pipeline.py` 支持 `mode = discovery`。它检查证据路径安全性后返回 `UNKNOWN`，从而把“尚未找到候选”和“候选已经被 Lean 证明”严格分开。完成候选接入后，应保留本清单作为历史记录，另建 `n10_structured.json`，再编译新的适配器；不应修改旧的 UNKNOWN 报告来伪造时间线。

## 下一项实质研究

当前按以下顺序推进：

1. 将 `n10_stationarity_endpoint_certificate_2026-10-25.json` 的有理运算链逐项重放到 Lean，形成端点严格符号定理；
2. 把 D4d 几何、能量公式、驻点根和端点符号封装为独立的候选适配器，并记录所有输入哈希；
3. 将当前一元下界先接入 `LowerBoundBridge` 作为非最优基线，再将 n=9 的三点 PSD/局部证书框架参数化到十点的 120 个三元组和相应 Gram 域，寻找可审计的全局下界证书；
4. 只有全域覆盖、局部非负性、能量恒等式和 Lean 内核重放全部通过后，才把状态从 `DISCOVERY_PENDING` 提升为正式 n=10 定理。

在第 3 步完成以前，任何 D4d 能量或一维驻点结果都只能作为候选发现，不能写成“n=10 已证明”。

三点泛型恒等式的 n=10 接口和复用边界见 `N10_GLOBAL_COVER_REUSE_ANALYSIS_2026-10-25_zh.md`；这一步只封装了条件式接口，未提供全局 `F/H` 证书。

恒 Gram 边界类型的 Lean 代数引理已放入 `ThomsonCertificate/N10TripleBoundary.lean`，但尚未连接到全域非负覆盖。
左端点第一驻点项的 Lean 重放已在 `N10StationarityLeftTerm1.lean` 完成；完整端点符号仍需继续接入。
第二驻点项已在 `N10StationarityLeftTerm2.lean` 完成，第三项和最终符号仍未完成。
第三项的 numerator 区间层已在 `N10StationarityLeftTerm3.lean` 完成，逆三次幂和最终符号继续推进。
左端第三项的完整倒数立方链和最终严格负号现已由 `N10StationarityLeftTerm3Final.lean` 编译通过；右端第三项仍未完成。
右端点第一、第二项也已完成无 `sorry` 重放，剩余是两端第三项和最终变号定理。

右端第三项现已用修正后的 sqrtTwoI 区间完成平方根、倒数立方、成员关系和最终严格正号；这仍只是 D4d 一维驻点端点证书。
