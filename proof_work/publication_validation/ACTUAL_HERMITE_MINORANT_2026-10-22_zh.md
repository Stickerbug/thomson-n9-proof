# 实际 Hermite 系数与全域代数下界

统一验证完成：2026-10-22T03:22:23+08:00（UTC+08:00）。

## 正式检查点

**807/807 个不同条件 gathered 目标、1446 项公理审计、183 模块，统一 PASS。**
本轮新增 9 模块、83 条审计。814 条逐目标声明仍只覆盖 807 个不同目标；历史基线为 272 个不同目标。
一次 LocalVerification --fresh 重放耗时 939.9 秒，覆盖 182 模块及正式根入口的 181 模块。
允许公理只有 propext、Classical.choice、Quot.sound；没有 sorryAx 或证明逃逸。
既有可达数学源码保持，formal/.lake 缓存继续保留复用。

## 本轮已证明

1. ActualHermiteScalar 在 1024 位整数区间内包住实际 14 个节点、196 个有符号逆差表项和 14 个 Coulomb 函数值。
2. ActualHermiteArray 将显式 Hermite 基函数公式转换为已验证的系数列表，证明列表所表示的多项式等于实际 H。
3. ActualHermiteBounds 无额外假设地证明实际 H 的全部 28 个系数属于归档 H_coefficients_ascending 区间。
4. ActualQuotientStructure 构造实际 W、Q，证明 G(H)=WQ、W 首一且次数 28、Q 次数至多 27。
5. IntervalMonicSolve 证明首一卷积的递降恢复算法正确；ActualQuotientArray 用它包住实际 Q 的系数。
6. RationalListPolynomial 解释精确有理系数列表及 Bernstein 基函数。ActualQuotientBernstein 由内核检查 28×28 变换的单项式恒等式，以及 28 个实际 Bernstein 系数的严格正下界。
7. ActualHermiteMinorant 证明 Q 在整个 [-1,1] 非负，从而实际 H 在整个 [-1,1) 满足 H(t) ≤ 1/√(2−2t)。这比归档证书的 [-1,14/25] 范围更强。

最小 Bernstein 系数下界的精确算术预检约为 0.06890337909；Lean 证明使用精确整数/有理数。
精确整除来自插值值与导数条件以及互素平方线性因子，不将“区间包含零”作为等式证明。
不需要形式化 28 阶导数的 Hermite 余项公式。

## 复现

先运行 export_hermite_coefficients.py --check --self-test 重现三份数据源码并检查四类畸形输入。
统一验证使用 verify_local_lean.py --reuse-local-build；工具链固定为 Lean 4.34.1，保留 formal/.lake。
复核包检查源/产物/日志哈希、完整 fresh 覆盖，并拒绝四类无效报告。

## 后续

实际 F/c 的精确接触系统、核基和 PSD 构造，实际 R_H 与归档 807 个源区间的绑定，其他完整 Hessian/局部非负、45 接触方程、rank33/W、68,063 叶 Lean 覆盖树及全局能量组装仍需完成。
ThomsonNineClaim 和全局唯一性仍未证明。Lean 自带内核重放不是外部独立验证。
长任务继续在 work/translation20261022 中推进实际 N 与接触系统，不将后续隔离成果计入本检查点。
