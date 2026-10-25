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

