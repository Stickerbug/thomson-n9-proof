# Thomson 证书框架通用化路线（2026-10-23）

## 当前结论

n=9 项目已经包含几层可以复用的形式化语义：

- `ThomsonNine.Coverage`：任意类型的有限二叉覆盖树、分裂关系和叶证书的归纳正确性；
- `ThomsonNine.Interval`：有理端点区间及其加、减、乘、幂的包含定理；
- `ThomsonNine.Interval.RatInterval.LocalCert`：三变量 Bernstein 张量叶证书的非负性；
- `ThomsonNine.PSDSemantics`：任意有限矩阵维数的 PSD 二次型和有限块求和；
- `ThomsonNine.Semantics`：域内 Bernstein 非负性、域外排除和能量平衡的逻辑接口。

这些层证明了“证书有效性”，不证明任意 `n` 都存在可找到的证书。

## 仍然绑定 n=9 的部分

下面的内容目前不能直接宣称为任意 `n` 的算法：

1. 物理域固定为三个 Gram 变量 `(u,v,t)`；
2. 根盒固定为 `[-1,14/25]^3`；
3. 能量平衡使用九点的 84 个无序三元组和 729 个有序三元组；
4. 候选构型、六个接触内积和 45 个接触方程是九点专用数据；
5. 局部 Hermite/Hessian 证书和 807 个系数目标是具体证书数据；
6. 主残差 `R`、PSD 块和边界乘子来自该候选核的固定解析分解。

因此，当前代码可以支持“通用证书检查器”的主张，不能支持“已经解决任意 `n`”的主张。

## 建议的分阶段实现

### 阶段 A：通用证书内核

建立独立命名空间 `ThomsonCertificate`，将下列接口参数化：

- 点类型、盒类型、可行域和目标命题；
- 叶证书和二分/多分裂关系；
- 有理区间运算和 Bernstein 张量维数；
- PSD 块的有限索引族；
- 从证书树到域内全局下界的统一定理。

验收标准：不引用 `ThomsonNine.Statement`、n=9 候选数据或固定系数；使用一个小型玩具多项式实例通过 Lean 编译。

### 阶段 B：n=9 适配器

把现有 n=9 模块改为该接口的一个实例，保持最终定理和所有哈希不变。验收标准是旧的 2390 模块、1507 审计、807/807 覆盖和 fresh replay 仍然通过。

### 阶段 C：跨 n 复用

在取得上游许可并完成来源比对后，分别为 n=7、n=8 写适配器。论文应报告真正复用的定理、代码行数或模块数，以及每个实例专用的证书数据。不能把不同项目的结果合并成一个未经核对的证明。

### 阶段 D：证书生成器

实现外部精确算术生成器，输出与 `ThomsonCertificate` 接口匹配的证书。生成器可以是启发式或数值辅助的；Lean 只检查证书，不把搜索过程当作证明前提。应同时提供失败输出和篡改证书的负向测试。

### 阶段 E：n=10 试验

先做候选构型、对称性和低维残差的可行性审计，再决定是否投入完整证明。只有在完成完整全局覆盖和审计后，才能写成“第一个 Lean-verified n=10 proof”。

## 可发表的准确表述

在阶段 A 完成前，可以写：

> a reusable formal certificate interface instantiated by the nine-point proof

在阶段 B/C 完成后，可以考虑：

> a reusable kernel-checked certificate architecture spanning multiple Thomson instances

只有在任意 `n` 的参数化定理和清楚的证书存在条件都正式化后，才可以讨论：

> a generic formally verified certificate framework for finite Thomson lower-bound proofs

这些表述都不等同于“对任意 `n` 自动求解 Thomson 问题”。

## 首创性边界

Karthigeyan 的 n=9 项目已经先公开，因此本项目不应主张第一个九点形式化证明。可检验的新颖性方向是：

- 通用证书语义和跨实例复用；
- 更完整的精确算术覆盖记录和重放流程；
- 独立的证书生成器与失败传播测试；
- 在确认无先例后，完成 n=10 的完整形式化证明。

每一项都必须在投稿前做公开代码、论文和 DOI 检索，并在论文中给出准确范围。
