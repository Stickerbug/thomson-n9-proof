# n=10 全局下界框架分析（2026-10-25）

## 已复用的 n=9 结构

n=9 的全局证明不是一个可以把 `9` 替换成 `10` 的单一泛型定理，而是以下几层固定数据的组合：

1. `MainCoverage.RootData` 把任意配置约化到三变量有序 Gram 点 `p : Fin 3 → ℝ`，并给出 `RootCube`、单调排序和 Gram 行列式约束。
2. `MainCoverage.GlobalAssembly` 给出 12 个局部源盒 `localCores`，把每个局部多项式证书接到全局残差。
3. `MainCoverage.ChunkModel` 中每个 `CertifiedChunk` 同时携带路径、局部树和检查布尔值。
4. `MainCoverage.CutPackage` 的 `rootCut` 是固定展开的覆盖树，`root_cut_checked` 用内核 `decide +kernel` 检查。当前树有 807 个有序叶目标。
5. `MainCoverage.CheckedCover` 先证明有序根域残差非负，再用三元组置换和 `frozen_claim_of_ordered_residual` 回到任意十点/九点配置。

因此可复用的是 `Tree`/`Spec`/`Certificate` 的语义接口、Bernstein/PSD 的局部检查器和 `LowerBoundBridge` 的逻辑桥；12 个局部盒、807 叶树、残差系数、轴切分和源数据都属于 n=9 实例，不能直接证明 n=10。

## n=10 的实际几何规模

当前 D4d 一参数候选由两个对跖极点和两个相差 45° 的四点环组成。候选点对的内积至少分为以下 7 类：

```text
-1,
+h, -h,
h^2,
2 h^2 - 1,
-h^2 + (1-h^2)/sqrt(2),
-h^2 - (1-h^2)/sqrt(2).
```

在候选根 `h≈0.4226874240` 时，非平凡数值约为

```text
 h       0.4226874240
 h^2     0.1786646584
 2h^2-1 -0.6426706831
 cross+  0.4021071312
 cross- -0.7594364481
```

这说明 n=10 的局部证书至少要处理新的接触/近接触类别和根式参数。现有 n=9 的 3 变量残差可以作为技术模板，但其系数和覆盖树没有可证明的迁移关系。

## 为什么通用接口目前不能自动解决 n=10

`GenericCertificate.lean` 只定义有限树和 `Checked` 谓词；`GenericLowerBound.lean` 的 `LowerBoundBridge` 要求实例适配器自行提供：

- 原始配置类型与可行性；
- 约化映射 `reduce`；
- 对所有配置的域/覆盖证明；
- 由残差目标推出能量下界的 `conclude`。

这些正是 n=10 尚未完成的数学内容。把一个 n=9 证书包装成 `Certificate 10` 会改变索引而不会产生任何新的覆盖或下界事实。

## 当前可验证的下界和缺口

本轮的 `n10_rational_lp_bound_2026-10-25.py` 用纯 `Fraction` 和 Bernstein 细分验证了一个 12 次 Legendre 多项式，得到

\[
 E_{10}\ge 326807/10000=32.6807.
\]

D4d 候选能量约为 `32.71694946014759`，差距约 `0.03624946015`。该证书还没有 Lean 重放，但它给出了一个无条件、可复算的基线，并说明单纯一元 Legendre 下界不足以关闭缺口。

## 推荐的真实下一阶段

先把上述一元证书接入 Lean 的 `LowerBoundBridge`，得到一个正式但非最优的 `n=10` 下界定理。随后再增加保持 D4d 接触结构的三点/四点 Gram 约束，或生成新的局部 Bernstein/PSD 覆盖。只有当新残差达到候选能量并完成覆盖，才能建立 `GlobalMinimumContract 10`；在此之前清单应继续保持 `UNKNOWN`。
