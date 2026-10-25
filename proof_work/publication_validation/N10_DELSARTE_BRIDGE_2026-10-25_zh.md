# n=10 Delsarte 下界 Lean 桥接（2026-10-25）

`formal/ThomsonCertificate/DelsarteBridge.lean` 已在 Lean 4.34.1 下编译通过，且不含 `sorry` 或新增公理。它定义了 `DelsarteBridge N d`，显式携带：

* 多项式常数系数、非负高阶系数和基函数；
* 点态多项式下界 `minorant`；
* 每个高阶基函数的双重和非负性 `harmonic_nonneg`；
* 能量的有序非对角和表达式；
* 把系数下界与非对角多项式和连接起来的有限求和恒等式。

`DelsarteBridge.sound` 从这些假设推出 `lowerBound ≤ energy x`。这一步是可复用的逻辑桥，不声称任何具体十点证书已经满足这些字段。

当前 `n10_rational_lp_bound_2026-10-25.py/json` 仍是外部 `Fraction` 算术证书，尚未实例化该结构。要完成实例化，还必须在 Lean 中重建 13 个精确系数、25 次 Bernstein 非负性证明、Legendre 基函数的球面加法定理，以及十点 Thomson 能量的有限求和约定。故 n=10 清单继续保持 `UNKNOWN`，下界 `32.6807` 也不提升为正式定理。
