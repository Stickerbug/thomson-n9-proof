# n=10 全局覆盖复用分析（2026-10-25）

检查现有 Lean 三点框架后，得到一个明确的参数化边界：`ThomsonNine.ThreePointBound.three_point_identity` 和 `three_point_bound_sos` 本身已经对任意 `n`（只要求 `3 ≤ n`）参数化，因而可直接取 `n=10`。对 n=10，三点核归一化为

```text
Rk  = 8 • S3(u,v,t) + S3(u,u,1) + S3(v,v,1) + S3(t,t,1)
      + (1/9) • S3(1,1,1).
```

相应的恒等式是：若 `s` 对前两个及后两个变量对称，则

```text
dsum ((H(u)+H(v)+H(t))/3 - e / choose(10,2) - Rs s 10 u v t)
  + 8 * Σ_{i,j,l} s(<xi,xj>,<xi,xl>,<xj,xl>)
 = 16 * (Σ_{i<j} H(<xi,xj>) - e).
```

这说明 n=10 的真正缺口不在抽象三点恒等式，而在实例数据：

1. 十点 D4d 候选的精确 Hermite `H` 和常数 `e`；
2. 每个 degree 块的显式 SOS/PSD 矩阵 `F k`，以及 `Rk` 的 Gram 域逐点上界；
3. 全部 `GramOK` 域的 Bernstein/局部覆盖，包含 25 个候选三角类型及其边界类型；
4. 十点配置的 pair cutoff、根域约化和从三点残差回到能量的实例适配器。

现有 n=9 `MainCoverage` 的 `RootCube`、12 个局部盒、807 叶 `CutTree`、残差系数和固定树都绑定 n=9 的 `ActualF/ActualR`，不能仅替换索引迁移到 n=10。n=10 的 `N10CandidateAdapter` 目前只封装 D4d 候选和显式 `lower_bound` 输入，尚未提供这些实例数据。

因此当前最小可行下一步是先新增一个不含具体系数的 `ThomsonTen.ThreePointAdapter`，实例化 `n=10` 的 `three_point_bound_sos` 接口，再逐步填入约化 PSD 块和 Gram 覆盖。该接口层不会改变 n=10 的 `UNKNOWN` 状态；只有所有 `hpt` 与覆盖叶证明完成后才能建立全局下界。
