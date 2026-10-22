# 平移语义、实际驻点半径与实际 Hermite 多项式

统一验证完成：2026-10-22T02:46:04+08:00（UTC+08:00）。

## 当前正式检查点

**807/807 个不同条件 gathered 目标、1363 项公理审计、174 模块，统一 PASS。**
覆盖保持完整；本轮新增 20 模块、146 条审计，814 条逐目标声明仍只覆盖 807 个不同目标。
一次 LocalVerification --fresh 内核重放耗时 901.1 s，闭包 173 模块，覆盖正式根入口 172 模块；Axioms 单独编译并限制为 import/#print axioms。
公理只有 propext、Classical.choice、Quot.sound；没有 sorryAx、native_decide 或证明逃逸。
上个检查点的全部可达数学源码保持；正式 .lake 缓存继续复用。

## 已闭合的数学接口

1. `CollectedTranslation` 对非重复目标支持且涵盖各源下指数的任意有限多项式，证明 uncollected expandedEval 等于 gathered 系数的多项式求值。
2. `SparseSupport` 的位掩码成员解释与逐坐标前驱引理，把向下封闭检查化为有限局部证据。`AAASupport` 检查实际 807 项互异、每项坐标小于 28、全部前驱仍在支持中。
3. `AAACollected.eval_shift_gathered` 给出原固定源多项式在 a+x 的值与全部 gathered 系数多项式在 x 的值相等。`CoordinateTranslation` 证明真实一、二阶坐标导数与固定平移交换。
4. `AAACollected.source_h00_mem` 因而约束原固定源多项式在 a+x 的真实二阶 u 导数。它不再只对一个未识别的平移系数族断言成员关系。
5. 严格有理平方比较包围五个平方根、正分母除法检查五个导数项，从而证明归档半径区间两端 familyEnergyDeriv 严格异号。IVT 给出实际驻点，既有唯一性定理把它识别为唯一驻点。
6. 再用新的有理端点证明同一实际半径属于宽度恰为 2^(-800) 的区间；`tight_width` 在 Lean 中检查这个宽度。选取端点的 mpmath 近似不进入证明可信基础。
7. `AAACenter` 把实际 AAA 中心绑定为 1-3r²/2，并将 source_h00_mem 的中心前提消去。标签 A 在此对应这一式，不能误用 r²/2-1。
8. `HermiteInterpolation` 用 Lagrange 基函数显式构造双重节点插值，证明值、导数、次数界和节点处基函数导数的倒数差之和公式。
9. `ActualHermite` 证明 14 个实际节点互异且小于 1，构造实际 H，验证 H(node)=f(node)、H'(node)=f(node)^3、次数≤27，并得到精确 G=∏(X-node)^2 Q 的商存在。
10. `HermiteMinorant` 证明 Q 在一点非负即推出 H(t)≤1/sqrt(2-2t)。Q 的实际非负性仍待绑定。`IntervalListPolynomial` 为下一步 H 系数提供整数区间系数列表加乘及其多项式语义证明。

H 的节点恒等式是精确实数等式；没有把“区间包含零”提升成等式。它们也不是尚待证明的 45 个 SDP 接触方程。

## 性能与复现

807 编码的互异检查改用相邻严格排序与传递性，约 42 s / 10.3 GiB 的试点降到约 6.7 s / 2.64 GiB。
最终 20 模块最近成功编译合计 34.2 s；全部探索/刷新构建累计 129.5 s。
新增产物合计 8122240 字节。细目在 semantic_radius_hermite_result.json。

```bash
export LEAN_BIN_DIR=/workspace/cloud-setup/lean-4.34.1-linux/bin
python3 -B proof_work/publication_validation/export_semantic_inputs.py --check --self-test
python3 -B proof_work/publication_validation/verify_local_lean.py --reuse-local-build
```

生成器逐字节复现支持表、四个端点证书和实际节点数据；输入、模板、所有可达源码/产物哈希进入统一检查。
四个打包负测与完整归档逐项哈希检查继续执行。规范包信息见 HANDOFF_STATE.json。

## 长任务继续方向与边界

用户已授权持续推进至完整问题证明，常规实现和优化自行处理；本文件记录检查点，不表示长任务结束。
当前在隔离工作目录继续实际 H 的 28 个系数包围证明。800 位半径与 1024 位内部算术的精确 Python 预检已经全部符合归档 H 区间，但不能将这项数值预检计为 Lean 证明。
之后仍需实际 F/c 构造与系数绑定、真正 R_H 残差恒等式及源系数成员关系、Q 非负性、其他完整 Hessian/局部非负、45 接触方程、rank33/W 与 PSD 实例、68,063 叶覆盖树的 Lean 实例化和全局能量组装。
最终 ThomsonNineClaim 与全局唯一性仍未证明。Lean 自带内核重放不是外部独立验证。本轮没有重跑整个 Python 覆盖树。
