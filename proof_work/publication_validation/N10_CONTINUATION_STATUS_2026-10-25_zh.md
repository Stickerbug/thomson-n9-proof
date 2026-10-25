# n=10 持续推进状态（2026-10-25）

本记录用于长任务续接，明确哪些部分已经可复核、哪些部分仍然阻塞 n=10 完整证明。它不改变 `certificate_manifests/n10_discovery.json` 的 `DISCOVERY_PENDING` 状态。

## 已完成的可复核层

* `N10D4dGeometry.lean` 在 Lean 4.34.1 中验证 D4d 十点坐标的单位球面条件、`0<h<1` 时的两两不同，以及 45 个无序点对的精确能量恒等式。
* `N10CandidateInterval.lean` 验证有理 `t` 区间到 `h=(1-t^2)/(1+t^2)` 区间的映射、驻点表达式在区间上的连续性，并提供端点变号到区间内零点的 IVT 桥接定理。
* `n10_stationarity_elimination_2026-10-24.json` 记录必要驻点条件的结果式消元；`n10_root_isolation_2026-10-24.json` 记录 224 次因子在目标区间内的根隔离和导数符号检查。
* `n10_stationarity_endpoint_certificate_2026-10-25.py/json` 使用纯 `Fraction` 区间算术重算左右端点，得到严格符号 `-1` 与 `+1`。这份证书是外部算术记录，尚未等同于 Lean 重放。
* `ThomsonCertificate/N10StationarityEndpoint.lean` 已通过 Lean 4.34.1 编译，提供无 `sorry` 的有理倒数/平方根区间原语、\(\sqrt2\) 有理包围和左右端点成员；最终驻点表达式的逐项符号仍未接入。
* `n10_rational_lp_bound_2026-10-25.py/json` 以纯有理 Bernstein 细分给出无条件外部基线 \(E_{10}\ge 326807/10000=32.6807\)。它距候选约 `0.03624946015`，尚不足以证明候选最优；对应方法分析见 `N10_GLOBAL_BOUND_FRAMEWORK_ANALYSIS_2026-10-25_zh.md`。
* `n10_three_point_sdp_discovery_2026-10-25.py/json` 用 n=10 的三点归一化（`8F+d`、目标 `15c-(5/3)F111`）进行了 degree-8 采样和差分进化搜索；数值目标约 `32.71694946`，但六轮运行的最新独立验证仍发现负残差（差分进化约 `-5.95e-5`），且 PSD 数值最小特征值受浮点误差影响。这是证书搜索线索，不是下界证明。
* 同一搜索器的 degree-10 诊断记录在 `n10_three_point_sdp_discovery_degree10_2026-10-25.json`；有限采样下目标仍贴近候选，但最坏残差约 `-5.31e-4`，未形成可接受的改进证书。
* `N10_SDP_SOLVER_COMPARISON_2026-10-25_zh.md` 对比 Clarabel/SCS，显示浮点 PSD 与有限采样误差会显著改变残差；因此这些数值残差既不能作为反例，也不能作为证明。
* `N10_REDUCED_THREE_POINT_SDP_2026-10-25_zh.md` 记录候选 Gram 零空间约化实验：PSD 数值稳定性改善且目标锁定候选，但全域残差仍未闭合。
* `N10_CANDIDATE_TRIPLE_TYPES_2026-10-25_zh.md` 记录 120 个候选三角形的 12 类符号分类和 3 类恒 Gram 边界类型，为局部/边界证书提供精确几何输入。

## 仍未完成的证明层

1. 把端点有理区间运算链逐项导入 Lean，得到可审计的端点严格符号定理；
2. 将 D4d 候选、驻点和能量数据封装为完整的 n=10 candidate/model/contact adapter；
3. 在全部十点球面构型上建立达到约 `32.71694946` 的全局下界，而不是只在 D4d 一参数族中找驻点；当前 `32.6807` 仅是非最优基线；
4. 对新的十点证书执行依赖有序编译、轴公理审计和 fresh 内核重放。

因此目前可以严谨地说“发现并形式化了一个 n=10 D4d 候选层”，不能说“n=10 Thomson 最小值已经证明”。`UNKNOWN` 是有意保留的门禁结果，不是验证失败。

## 推荐的执行顺序

```text
endpoint Lean replay
  -> candidate/model/contact adapter
  -> n=10 PSD + local nonnegativity certificate
  -> full Gram-domain coverage
  -> ordered audit + fresh kernel replay
  -> only then status = PASS
```

旧 n=9 fresh replay 不应因本记录重复执行；它的结果已经由发布版本和交接状态保存。任何新报告都应同时保留本文件、端点 JSON、Lean 源文件及其哈希，以便审稿人区分候选发现与全局定理。


* `N10_GLOBAL_COVER_REUSE_ANALYSIS_2026-10-25_zh.md` 和 `N10ThreePointAdapter.lean` 已确认 n=10 的三点恒等式可直接复用泛型定理；尚缺实例化的 `F/H` 数据和全域覆盖。

* `N10TripleBoundary.lean` 已在 Lean 中证明三个恒 Gram 边界类型及一个内部类型的精确行列式公式。
* `N10StationarityLeftTerm1.lean` 已无 `sorry` 证明左端点第一驻点项的区间成员关系和严格负性；term2、term3 及最终端点符号仍待完成。
* `N10StationarityLeftTerm2.lean` 也已无 `sorry` 编译通过，并证明左端点第二驻点项严格为负；term3 和最终端点符号仍待完成。
* `N10StationarityLeftTerm3.lean` 已完成第三项的代数 numerator 区间层（pbase、a/b base、a_num、b_num）；逆三次幂和最终符号仍待完成。
* `N10StationarityLeftTerm3Final.lean` 进一步完成左端第三项的平方根、倒数立方、乘法链和最终严格负号；右端第三项尚未闭合。
* 右端点 term1、term2 的 Lean 区间成员和严格符号也已完成；两端的 term3 与最终符号仍待完成。

右端第三项现已用修正后的 sqrtTwoI 区间完成平方根、倒数立方、成员关系和最终严格正号；这仍只是 D4d 一维驻点端点证书。
