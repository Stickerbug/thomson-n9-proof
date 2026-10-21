# 局部证书：Lean 数据、递推和解析接口

本项仍是 Thomson n=9 的未评审证明候选。以下结果不构成最终 `ThomsonNineClaim`，也不证明所有极小构型的全局唯一性。

## 数据来源及已经闭合的算术步骤

`export_local_lean.py` 读取既有独立局部结果和 SHA-256 绑定的 12 份逐类记录，确定性生成 `formal/ThomsonNine/LocalLDLData.lean`。包括 9 个内部三维、3 个边界二维证书，33 个严格正有理主元下界，36 个中心区间包含定理，以及 3 个边界导数 `R_u` 的正下端点定理。`--self-test` 检查 12 种损坏输入。数据来源、适用盒及未证明的绑定记录在 `local_lean_export_manifest.json`。

`export_local_ldl_replay.py` 从保存的预处理 Hessian 区间开始，按独立检查器相同的 640 位向外舍入次序重放 LDL。共 147 个区间运算，得到的 L 和主元端点与保存结果逐项完全相同。生成 `formal/ThomsonNine/LocalLDLReplay.lean` 与 `local_ldl_replay_manifest.json`；Lean 证明每一步的角点界或平方界，不信任 Python 的舍入实现。每类的 `psd_*` 定理以真实预处理 Hessian 条目的区间归属为前提，结论是任意实方向上的二次型非负；真实递推主元的区间归属由运算可靠性证明推出。

`export_local_hessian_bridge.py` 将原始 `target_Hessian` 区间经精确有理 W 映射到保存的预处理区间，覆盖全部 12 类、63 个独立条目。`LocalHessianBridge.lean` 已编译；`psd_original_*` 现在直接以原始矩阵条目归属为前提，调用具体 LDL 重放和逆合同推出原矩阵二次型非负。原始 Hessian 条目确实包围真实残差二阶导数仍须另证。

`export_local_sparse_hessian.py` 是首个具体求值实例：AAA 类的 H00，保留 807 项（550 项二阶求导后非零）、28 个幂区间和 34 个求和块，生成 `LocalSparseHessianAAA.lean`。15 项负面测试通过。全部 10 个模块已编译：`Base`、`Chunk00`/`Chunk01`（各 96/96 零项）和 `Chunk02`–`Chunk07`（550 个非零项）+ 组装 `LocalSparseHessianAAA`。非零项不再用逐项 `norm_num` 直接展开 807 个系数区间（单 term 曾超过 193 s CPU），而是用 `IntervalLocalOps.mem_mul_of_bounds` 的 8 个精确文字角点不等式；单个代表项的精确模板约 17 s CPU 通过。2026-10-20 14:45 统一复核 PASS（620 条公理审计、90 模块）。目标定理仍以固定实系数属于保存的平移系数区间、点属于相对盒为前提，内部完成幂与端点包围，不假设端点比较或实际 Hessian 归属；原始残差到这些平移系数的绑定仍未证明。状态见 `AAA_PARTIAL_STATUS_2026-10-19_zh.md`。

`SparseTranslation.lean` 已编译，证明任意固定实系数稀疏多项式在中心 `a` 的平移满足 `eval(a+x)` 等于未合并的有限二项式展开，并给出 `expandedCoefficient` 的区间成员界。它固定同一系数族与同一中心，不依赖点、不含接触假设；但把同指数项合并成保存的平移系数区间、以及把真实残差识别为该系数族，仍未形式化。

## 代数和解析结构

- `LocalLDLSemantics.lean` 给出三维、二维 LDL 与逆合同语义。约定 `P = W H Wᵀ = L D Lᵀ`；原 H 的方向应先做 `W⁻ᵀ`，再做 `Lᵀ`。把 L 或 W 的方向倒过来将得到另一个二次型。
- `LocalLDLFactorization.lean` 从实际除法递推推出逐项分解恒等式。它仍接受主元区间归属为前提；上面的具体 `psd_*` 定理补上了预处理 Hessian 输入区间到主元归属这一步。
- `IntervalLocalOps.lean` 证明任意符号区间的乘法、过零平方、正分母除法及区间放宽可靠性。端点是精确有理数；没有浮点运算或 `native_decide`。
- `IntervalLinear.lean` 证明任意符号有理线性映射的区间可靠性。`IntervalSparsePolynomial.lean`、`IntervalPowerReplay.lean` 和 `IntervalSparseDerivative.lean` 已编译，分别给出带符号幂与稀疏求值、方幂缓存的可靠性、以及实际一二阶坐标导数等于形式求导式（含同轴连续求导）。系数是求值前固定的一族实数，不能随点选择。
- `LocalNonneg.lean` 通过 [0,1] 上的连续性、一二阶导数见证、二阶导数非负，以及中心精确值与一阶导数为零推出线段非负，含两个端点。另有二维边界图接口与沿 u 单调延拓。延拓区间必须同时包含图值与源点，不能仅假定原 sourcebox 足够。
- `GramBoundary.lean` 从 Gram 行列式恒等式推出可行点位于两个根式图之间，证明下图上 Gram 为零，并接入下图到可行点的单调延拓。它不计算实际残差的边界导数。
- `LocalCerts.lean` 只包含早先的中心区间与辅助定理。`LeafCert.lean` 的 `LocalCert` 是 Bernstein 张量接口；这些 Hessian 证书没有冒充该类型的实例。

## 验证与复现

从项目根目录运行快速数据复现：

```bash
python3 -B proof_work/publication_validation/export_local_lean.py --check --self-test
python3 -B proof_work/publication_validation/export_local_ldl_replay.py --check
python3 -B proof_work/publication_validation/export_local_hessian_bridge.py --check --self-test
python3 -B proof_work/publication_validation/export_local_sparse_hessian.py --check --self-test
```

编译、公理审计与独立内核重放使用一个串行进程：

```bash
python3 -B proof_work/publication_validation/verify_local_lean.py
```

若逐个模块刚刚编译完，可用 `--reuse-local-build`；脚本会拒绝早于自身源文件或直接本项目依赖的产物，仍重新编译聚合模块和正式根入口。也可用 `--adopt-build` 显式接收一个外部编译产物，但仍要求产物 mtime 不早于源文件。脚本输出 `local_lean_verification.json` 及 `local_lean_verification_logs/`。只有报告为 `LOCAL_LEAN_COMPILER_AXIOMS_AND_KERNEL_PASS`，才表示本轮数据、根入口、公理审计和 `leanchecker ThomsonNine.LocalVerification` 都通过。2026-10-20 14:45 的 `--adopt-build` 复核已取得该 PASS：620 条公理审计、91 模块闭包、第二内核 exit 0。`TwoSourceBindings.lean` 另含 32 个双源目标的区间证书，`ChainBindings.lean` 含 54 个三/四源链式目标的区间证书；合计 87/807。`GatheredBinding.lean` 对 `.t126` 绑定完整 807 项展开后的 gathered coefficient；`GatheredTwoSource.lean` 把其余 32 个 two-source 目标全部升级为完整 807 项 gathered 绑定；`GatheredChain.lean` 再把 54 个 chain 目标升级为完整 gathered 绑定；`SingleSourceBindings.lean` 覆盖 19 个单源目标，`FiveSourceBindings.lean` 覆盖 21 个五源单轴 chain 目标，`ChainRestBindings.lean` 覆盖 21 个六源单轴 chain 目标，累计 217/807 个目标有完整 gathered 证书；`MultiCornerBindings.lean` 另以字面角点区间证书覆盖 15 个五源多轴 delta≤1 目标，使覆盖达到 255/807；`MultiCornerPBindings.lean` 另加入 13 个八源三轴目标，其余 11 个八源目标的逐源和宽于 q，尚未纳入。公理审计要求每条打印均出现，只允许 `propext, Classical.choice, Quot.sound`。构建失败返回非零；内核接受模块名而非绝对 olean 路径。

这些命令读取保存的独立局部结果，并未重新进行约 47 分钟的全树运算，AAA H00 导出器重新检查保存的 807 项平移系数的二阶导数包围，但尚未证明这些区间来自真实残差的平移，也未重新计算所有类的完整 Hessian。独立内核重放的是局部模块的证明依赖闭包；这不等于最终九点定理的第二内核验证。

## 仍未闭合的真实对象绑定

1. 实际残差多项式及边界图的 Hessian/导数在各完整盒上的可靠区间包围。精确 W 到已保存预处理区间的包围已由具体有理线性证明完成。
2. 真驻点处的全部 45 个接触等式，rank33/W 兼容性，以及中心精确函数值和梯度为零。
3. 实际边界图的链式求导、沿线段的定义域与连续性、扩展 hull 包围，以及 R_u 的真实区间归属。正端点定理自身不证明真实导数归属。
4. 把真实局部非负性绑定到覆盖树的局部终端，实例化 68,063 个叶子，并连接 PSD、Hermite、配对归约和最终能量下界。

通用定理不会因假设尚未实例化而补出这些步骤；独立 JSON 的 PASS 也没有被当成 Lean 公理使用。
