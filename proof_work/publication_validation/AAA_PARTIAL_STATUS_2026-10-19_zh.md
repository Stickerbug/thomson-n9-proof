# AAA H00 具体证书：全部分块编译与统一复核 PASS

日期：2026-10-20 14:45 UTC（当前 PASS；下方 §1–§10 保留 10:35 的历史阻断记录）。本文件记录本地证书的编译与统一复核状态；它不证明最终 `ThomsonNineClaim`，也不构成外部同行评议。

## 0. 2026-10-20 14:45 统一复核结果（当前）

- `LocalSparseHessianAAABase`、`Chunk00`–`Chunk07`、组装 `LocalSparseHessianAAA` 全部编译通过。
- 12 类局部证书、AAA H00、根入口 `ThomsonNine.lean`、`Axioms.lean`、`LocalVerification.lean` 均由统一脚本复核。
- `python3 -B proof_work/publication_validation/verify_local_lean.py --adopt-build` 返回 `LOCAL_LEAN_COMPILER_AXIOMS_AND_KERNEL_PASS`（exit 0）。
- 644 条 `#print axioms` 按序打印；只出现 `propext`、`Classical.choice`、`Quot.sound`；无 `sorryAx`。
- 第二内核 `leanchecker ThomsonNine.LocalVerification` exit 0（473.1 s；115 模块闭包）。
- 新增 `TargetBinding.lean`：对指数 `(0,9,10)`（`.t126`）用两个源区间与中心区间证明 `coefficientInterval .t126` 包含对应的两项目标系数表达式。
- 新增 `TwoSourceBindings.lean`：用同一角点模板证明其余 **32** 个双源目标（合计 33 个目标）的 `coefficientInterval` 包含对应两项系数表达式；仍不是 807 个目标的完整绑定。
- 新增 `ChainBindings.lean`：54 个三/四源单轴链式目标的 `coefficientInterval` 包含证书；连同前 33 个，共 **87/807** 个目标有 Lean 区间证书。
- 新增 `GatheredBinding.lean`：对 `.t126` 把全部 807 项展开后的 gathered coefficient 精确约化为两个贡献项，并证明其落入 `coefficientInterval .t126`；这是首个覆盖完整 807 项源的 Lean 系数绑定。
- 新增 `GatheredTwoSource.lean`：对除 `.t126` 外全部 32 个 two-source 目标逐一证明完整 807 项 gathered coefficient 的区间绑定；two-source 目标现全部升级为完整 807 项版本。
- 新增 `GatheredChain.lean`：54 个三/四源 chain 目标也全部升级为完整 807 项 gathered coefficient 绑定；至此 87/807 个有区间证书的目标全部升级为完整 gathered 版本。
- 新增 `SingleSourceBindings.lean`：19 个单源目标的完整 807 项 gathered coefficient 直接化为 `c .tNNN`，并证明归档 `coefficientInterval` 包含对应的原始 R 区间。连同前 87 个，共 **106/807** 个目标有完整 gathered 证书。
- 新增 `FiveSourceBindings.lean`：21 个五源单轴 chain 目标加入；连同前 106 个，共 **127/807** 个目标有完整 gathered 证书。
- 新增 `ChainRestBindings.lean`：21 个六源单轴 chain 目标加入；连同前 127 个，共 **148/807** 个目标有完整 gathered 证书。
- 新增 `SevenSourceBindings.lean`：15 个七源单轴 chain 目标加入；连同前 148 个，共 **163/807** 个目标有完整 gathered 证书。
- 新增 `EightSourceBindings.lean` 与 `NineSourceBindings.lean`：15 个八源、9 个九源单轴 chain 目标加入；累计 **187/807**。
- 新增 `TenSourceBindings.lean` 与 `ElevenSourceBindings.lean`：9 个十源、3 个十一源单轴 chain 目标加入；累计 **199/807**。
- 新增 `TwelveSourceBindings.lean` 至 `SeventeenSourceBindings.lean`：12–17 源各 3 个单轴 chain 目标，共 18 个；累计 **218/807**。
- 新增 `MultiCornerBindings.lean`：15 个五源多轴 delta≤1 目标（`.t125` 等）的字面区间/角点证书；每个 `..._gathered` 绑定完整 807 项 gathered coefficient；累计 **232/807**。
- 新增 `MultiCornerPowBindings.lean`：9 个五源多轴 delta≥2 目标；累计 **241/807**。
- 新增 `MultiCornerPBindings.lean`：13 个八源三轴目标，其逐源乘积区间和恰好被归档 q 包含；累计 **254/807**。其余 11 个八源目标的逐源区间和严格宽于 q，未纳入。
- 新增 `GroupedT114.lean`：对 `.t114` 按 `shift_axis` 的同序分组（轴 0 按 `(e1,e2)`、轴 1 按 `e2`）构造字面区间，证明完整 807 项 gathered coefficient 落入 `coefficientInterval .t114`；累计 **279/807**。
- `SparseTranslation.lean` 新增通用顺序幂缓存 `powInterval` 与 `powInterval_mem`，为后续 tail-chain 生成提供单区间幂证书；该引理已单独审计。
- 报告与 stamp：`local_lean_verification.json`、`local_lean_build_stamp.json`（2026-10-20 14:45）。
- 复核边界不变：AAA 定理以固定实系数族属于 `coefficientInterval`、点属于 `relativeBox` 为前提；真实残差/平移系数绑定、其余 11 类、45 个接触、68,063 叶覆盖与最终定理仍未形式化。没有外部评议。

## 1. 历史：10:35 的阻断状态

> 以下 §1–§10 是 10:35 时的部分编译与性能记录，保留作历史证据；当前状态以 §0 为准。

- `LocalSparseHessianAAABase`、`LocalSparseHessianAAAChunk00`、`LocalSparseHessianAAAChunk01` 已编译出 olean。
- `Chunk00`、`Chunk01` 的 96 项都是二阶导数为零的项，走的是快速零项证明；它们不检查任何非零 Hessian 项。
- `Chunk02`（65 零项 + 31 非零项）、`Chunk03`–`Chunk07`（各 96 非零项）和组装模块 `LocalSparseHessianAAA` 未编译。
- 因此根入口 `ThomsonNine.lean`、`Axioms.lean`、`LocalVerification.lean` 仍不能编译；没有新的 `local_lean_verification.json` 或 `local_lean_build_stamp.json`。
- 按当前逐项 `norm_num` 设计，剩余 550 个非零项的证书在可接受时间内无法完成：单 term 实测已超过 193 s CPU，耗时随时限继续增长，而每个 term 还有两个端点。

## 2. 已编译产物

| 模块 | 内容 | olean 大小 | 完成时间 UTC |
|---|---|---:|---|
| `LocalSparseHessianAAABase` | 807 项索引、系数区间、幂表、`targetH00` 等基础定义 | 48,358,896 B | 08:07 |
| `LocalSparseHessianAAAChunk00` | 96/96 零项 | 1,311,456 B | 10:04:50 |
| `LocalSparseHessianAAAChunk01` | 96/96 零项 | 1,312,320 B | 10:28:38 |

`Chunk01` 构建从 10:24:05 开始，约 4 分 33 秒；期间并行的全项探针占用了 CPU。零项 chunk 的成本几乎全是导入 48 MB `Base` olean（约 2 GB RSS），而不是 96 条零项证明本身。

## 3. 零项快速路径

`export_local_sparse_hessian.py` 对 `e[0] < 2` 且 `termBound` 的 lo/hi 都为 0 的项生成：

```lean
have hzero : hessianTerm c x .tNNN = 0 := by
  unfold hessianTerm
  rw [show exponents .tNNN = ![e0, e1, e2] from rfl]
  simp [lowerExponent, derivativeCoeff]
rw [hzero]
simpa [termBound_NNN, RatInterval.const] using mem_const (0 : ℚ)
```

块/ chunk 的 nil 分支同时改为 `by simpa [sumIntervals, eval] using mem_const (0 : ℚ)`，修复了 `sumIntervals []` 与 `const 0` 不匹配的错误。重新生成后的 `--check --self-test` 仍通过：

- `LOCAL_SPARSE_HESSIAN_NEGATIVE_TESTS_PASS 15`
- `LOCAL_SPARSE_HESSIAN_MODULE_TAMPER_TESTS_PASS 10`
- `LOCAL_SPARSE_HESSIAN_CHECK_PASS: AAA H00, 10 modules, mode=8`

## 4. 非零项的性能实测

非零项当前生成两个端点证明，每个都是：

```lean
exact mem_subset (mem_mul hc2 hm)
  (by norm_num [termBound_NNN, coefficientInterval, exponents, lowerExponent,
      derivativeCoeffInterval, monomialInterval, powerTable, finitePower,
      RatInterval.mul, RatInterval.const, power_00, power_01, power_03])
```

在 `LocalSparseHessianAAABase` 已导入的探针中测得：

| 探针 | 结果 |
|---|---|
| `(coefficientInterval .t288).lo = (391 位有理数) := rfl` | 104 ms（仅投影字段） |
| `(coefficientInterval .t288).lo ≤ ...hi := by norm_num [coefficientInterval]` | **152 s** |
| 直接两个 379/378 位有理数的 `≤`，`by norm_num` | **29.7 s** |
| 同一有理数不等式，`by linarith` | 139 ms |
| 同一不等式先 `rw [Rat.le_iff]` 再 `norm_num` | 64 ms |
| `by decide`（Rat 或先 `Rat.le_iff` 的 Int 目标） | 快速失败：`Rat.blt`、`Int.decLe`/`Int.decNonneg` 归约卡住 |
| 完整 t288 项，加入 `unfold hessianTerm` / `hexp : exponents .t288 = ![2,3,1]` / 去掉 `exponents` | 单 term > **193 s CPU**，2.4 GB RSS，被终止 |
| 完整 t288 项，两个端点改成 `rw [Rat.le_iff]; norm_num [...]` | 单 term > **212 s CPU**，1.3 GB RSS，被终止 |

关键结论不是“再等久一点”，而是：`norm_num` 的主要成本来自对 `min`/`max` 区间端点中的巨大有理数做规范化与比较；`Rat.le_iff` 只能加速已经是“字面量对字面量”的比较，不能消除端点中的 `min`/`max`。`Chunk02`–`Chunk07` 合计 550 个非零项，按当前设计至少需要数十小时到数天，且单进程内存峰值约 2.4 GB。

## 5. 第二内核尝试

曾尝试对 `Chunk01` 运行：

```bash
leanchecker ThomsonNine.LocalSparseHessianAAAChunk01
```

进程在导入/重放阶段长时间停在 `ptrace_stop`（proot 环境），CPU 仅约 2 s、日志为空，未得到 exit 0；已终止。不能把这次尝试记为内核 PASS。零项 chunk 的 olean 存在只说明编译器接受，不说明 `leanchecker` 已复核。

## 6. 统一复核状态

未运行 `verify_local_lean.py --adopt-build`，因为它会重建根入口并要求全部 AAA 模块存在；当前缺失 chunk 会导致构建失败。旧报告已隔离为 `local_lean_verification.stale_20261019_0408.json.bak`；没有生成新的 PASS，也没有重打 `THOMSON_N9_REVIEW_BUNDLE.zip`。旧复核包不包含本次 AAA 产物，不能当作包含 AAA 证书的包。

## 7. 若要继续，需要改变证书设计

下列方向尚未实现，不能写成已完成：

1. 预计算每个区间端点的字面量，并逐层用 `Rat.le_iff` + 短 `norm_num` 证明 `min`/`max` 分支；把单 term 成本从分钟级压到秒级。
2. 用 `eval_mem` 对整个 807 项做符号成员证明，只在块/最终层做少量字面量比较；关键是避免逐项展开 `min`/`max`。
3. 对 `Chunk02`–`Chunk07` 做分块并行编译；每块仍需先解决非零项证明成本。

在这些设计落地前（10:35 历史状态），准确状态是：**AAA H00 的零项子集已编译，完整 807 项证书未编译，统一第二内核复核未完成。**（该状态已被 §0 的 18:49 PASS 取代。）

## 8. 2026-10-19 10:48 新分析：termBound 的形状已经适合符号化证明

新增数值分析脚本 [`analyze_aaa_term_bounds.py`](analyze_aaa_term_bounds.py)，只读取已生成的 Lean 源码，不运行 Lean。运行结果：

```text
term shapes: nonneg=63, nonpos=43, positive_interval=1, symmetric=443, zero=257
target exact match: 0.041083443167453965 0.04302222661180111
chunk replay exact: 8 chunks
SIGN_AWARE_SHAPE_CHECK_PASS
```

含义：807 个 `termBound` 中

- 257 个是零（已有快速证明）；
- 63 个是 `[0, h]`，43 个是 `[l, 0]`；
- 443 个是跨零的对称区间；最大相对不对称约 `5e-103`，只是向外舍入；
- 只有 1 个例外：`.t257` 的 `[l, h]` 是窄的正区间（宽约 `6.5e-100`），对应 `![2,0,0]`、二次导数后为常系数项；
- 每个 chunk 的 `chunkInterval_XX` **恰好等于**该 chunk 内全部 `termBound` 的精确和，target 也恰好等于全部 807 项之和。

这把“逐项展开 `min`/`max`”的问题改写成：零项快速证明 + 一维/对称的**符号绝对值界**。对 `[0,h]` 证明 `0 ≤ term` 且 `term ≤ h`；对 `[l,0]` 证明 `term ≤ 0` 且 `l ≤ term`；对对称项证明 `|term| ≤ B`；`.t257` 单独用精确端点处理。所有最终比较仍是字面量级，但不再对每个 term 展开 807 分支的 `coefficientInterval` 与 `mul` 的 `min`/`max`。

下一步应把这个形状分析落实为生成器的符号证明模板，并在 **t288 一个 term** 上测得单 term 时间；只有在单 term 进入秒级后，才值得重建 Chunk02–07。当前仍是数值可行性分析，不是 Lean 证明，也没有改变“未 PASS”的结论。


## 9. 2026-10-19 11:25 t288 符号绝对值证明成功；精确端点证明仍失败

`formal/TestSym.lean` 是一个独立测试文件（导入 `ThomsonNine.LocalSparseHessianAAABase`，不在根入口的 import 链中），证明

```lean
|hessianTerm c x .t288| ≤ (qB : ℝ)
```

在 `hC : ∀ k, (coefficientInterval k).mem (c k)` 与 `hP : ∀ i n, (powerTable n).mem (x i ^ n)` 下成立。它把 `|c|`、`|x1^3|`、`|x2|` 分别用 `qCabs`、`qR3`、`qR2` 界住，相乘后与 `qB` 做一次 `rw [Rat.le_iff]; norm_num`。编译结果：

```text
EXIT 0
real 2m23.702s
user 0m14.362s
```

绝大部分墙钟时间仍是导入 48 MB 的 Base olean；证明本身的 tactic 时间约 14 s。这个模板说明**符号绝对值界**可行，但它只证明 `|term| ≤ B`，不等于 `termBound_288.mem (hessianTerm ...)`：`termBound` 的两端并不严格对称（最大相对不对称约 `4.5e-100`），而 `mem_subset` 要求区间包含，不能把对称界直接当作精确端点。

`formal/TestExact.lean` 尝试去掉逐项 `norm_num`，改为显式展开 `termBound_288`、`RatInterval.mul`、`min`/`max` 后 `split_ifs`。失败记录：

- 直接 `simp only [coefficientInterval, exponents, ...]`：`maximum number of steps exceeded`，耗时 7m52s；
- 改为局部重写后：`Application type mismatch: The argument max_def ... has type @Eq ℚ (max (...)) (...) but is expected to have type @Eq ℚ (max ((coefficientInterval ...).lo * (const ↑(![2,3,1] 0)).lo) ...)`，在 implicit transparency 下 `derivativeCoeffInterval`/`const` 的 semireducible 展开不一致；耗时 11m38s。

结论：精确端点成员证明不能再靠“展开 807 分支的 `min`/`max` + `norm_num`”这条路线；符号界本身可行，但必须配合以下之一才能闭合：

1. 对 550 个非零项生成**单侧精确端点**证明（`[0,h]`/`[l,0]`/对称区间分别处理），避免 `min`/`max` 的全展开；
2. 或把证书目标改为一个**可计算区间**，逐项用 `mem_mul` 直接得到成员性，最后只做块级/最终级的少量字面量包含比较。

两种方案当时都尚未实现。历史（10:35）统一复核状态是：Base/Chunk00/Chunk01 编译通过，Chunk02–07 与 assembly 未编译，没有新的 `local_lean_verification.json`/stamp，没有统一 PASS，也没有重打复核包。不能把 `TestSym.lean` 的成功写成 AAA 证书完成。该状态已被 §0 的 18:49 PASS 取代；`TestSym.lean` 只是绝对界原型，不是最终证书。


## 10. 2026-10-19 11:55 精确端点证明的新模板：四角比较，成功

§9 的 `TestSym.lean` 只证明了绝对值界；精确的 `termBound_288.mem` 仍未解决。随后发现 `IntervalLocalOps.lean` 已有

```lean
theorem mem_mul_of_bounds {I J K : RatInterval} {x y : ℝ}
    (hx : I.mem x) (hy : J.mem y)
    (hll : K.lo ≤ I.lo * J.lo) ...
    (uhh : I.hi * J.hi ≤ K.hi) : K.mem (x * y)
```

它把“证明 `K = RatInterval.mul I J`”改写成**八个字面量角点比较**，完全不需要展开 `RatInterval.mul` 的 `min`/`max`。据此新建 [`formal/TestCorners.lean`](formal/TestCorners.lean)：

- 用 `coefficientInterval .t288` 的精确端点（`rfl` 可重写）构造系数区间 `I = [2*Alo, 2*Ahi]`；
- 用 `power_03`、`power_01` 的精确端点构造单项式区间 `J`（`mul (mul 1 power_03) power_01` 的精确四角结果）；
- 从 `hC`/`hP` 得到 `I.mem (c*2)` 与 `J.mem (x1^3*x2)`；
- 最后对 `termBound_288` 的八个角点做 `rw [Rat.le_iff]; norm_num`，调用 `mem_mul_of_bounds` 得到 `termBound_288.mem (hessianTerm c x .t288)`。

编译结果：

```text
EXIT 0
real 1m46.312s
user 0m17.374s
```

其中约 1m30s 仍是导入 48 MB 的 Base olean；**证明本身约 17s**，不再有 152s 的 807 分支展开，也没有 11 分钟的 `max_def` 失败。`TestCorners.lean` 里的 `K` 使用与 `termBound_288` 完全相同的端点字面量（从 Chunk03 解析），因此这个模板可以直接搬进生成器：每个非零项生成系数区间 `I`、单项式区间 `J` 和 24 个字面量角点比较（系数 8 + 单项式 8 + 最终 8）。

这改变了剩余工作的性质：精确端点证明从“不可行的逐项 `norm_num`”变成“可批量生成的四角比较”。按 17s/term 估算，550 个非零项约 2.6 CPU 小时；分块并行后是小时级，而不是天级。下一步是把该模板写进 [`export_local_sparse_hessian.py`](export_local_sparse_hessian.py)，先用 1–2 个真实 term 验证生成代码，再重建 Chunk02–07 和 assembly。

当前仍**没有**完整构建、统一 `verify_local_lean.py --adopt-build` PASS、stamp 或新复核包；`TestCorners.lean` 只是 t288 的独立模板验证，不是 807 项证书。

## 11. 2026-10-19 18:49 系数分组平移的一轴可靠性引理

真实残差/平移系数绑定仍**未**完成，但已推进到可形式化的分组算法层：

- 在 `formal/ThomsonNine/SparseTranslation.lean` 末尾新增 `axisContribB`、`axisShiftCoeff`、`axisShiftInterval` 和定理 `axisShiftCoeff_mem`。该定理对一维分组平移给出：若每个源系数区间包含对应实系数、幂缓存每个条目包含 `a^n`，则生成的区间系数包含精确的合并系数。证明用 `mem_sumIntervals`、`mem_mul`、`mem_const`，不展开任何 807 分支定义。
- `formal/ThomsonNine/Axioms.lean` 增加该定理的 `#print axioms`；该引理合入后的复核为 274 条审计、67 模块闭包、`leanchecker` exit 0（18:49）；后续累计到 451 条审计、73 模块。
- 独立重建已确认：`independent_local_00_AAA.json` 的 `shifted_polynomial` 可由 `independent_hermite_RH_result.json` 的 807 个 `R_coefficients` 加 `new_center_intervals`，按生成器的 `shift_axis` 逐轴重放得到，807 个键 0 失配；总展开贡献 58,791 个，单个目标最多 807 个贡献。
- 关键负面结果：把每个贡献的区间独立相乘后再求和，**563/807** 个目标不能包含归档 `shifted_polynomial`；区间乘法不分配于合并后的加法。因此绑定证明不能走“逐贡献独立区间求和”，必须复用生成器的逐轴合并结构。`axisShiftCoeff_mem` 正是这个结构的一轴可靠性步骤；三轴迭代、与归档 `coefficientInterval` 的连接、以及真实残差识别仍未完成。
- 该引理只增加已检查的算法基础设施，不改变最终定理状态；真实残差/平移系数绑定、其余 11 类、45 个接触、68,063 叶覆盖与最终 `ThomsonNineClaim` 仍未形式化，也无外审。

## 12. 2026-10-19 18:49 三轴分组平移可靠性

在一轴引理之上继续加入三轴版本：

- `axisTargets axis l`：一轴平移后所有可能的目标指数（对源指数逐轴降幂，`dedup`）。
- `shiftAxis axis P l`：把一轴平移后的支撑显式化为 `(target, axisShiftInterval ...)` 列表。
- `shiftAxisCoeff axis a l c`：一轴平移后的精确系数函数。
- `shiftAxis_mem`：对上述列表逐点成立：区间包含精确系数。
- `shiftAxes P l`：按生成器顺序执行 `0,1,2` 三次分组平移。
- `shiftAxesCoeff P a l c`：三次平移后的精确系数函数，复用前一步的系数函数；中心是向量 `a : Fin 3 → ℝ`，幂缓存逐轴 `P : Fin 3 → ℕ → RatInterval`。
- `shiftAxes_mem`：三轴列表的每个区间都包含对应的精确系数。
- `shiftAxes_mem_of_contains`：若目标系数区间族 `K` 在每个目标上包含三轴区间，则 `K` 包含精确系数；这是连接归档系数区间的桥梁。

该阶段复核为 277 条 `#print axioms`、71 模块闭包、`leanchecker` exit 0（17:51）；后续累计到 451 条审计、73 模块。

必须强调：这些定理证明的是“分组平移算法对任意源系数区间和幂缓存是可靠的”，**还没有**把真实残差/原始 R 系数、真实中心、归档 `shifted_polynomial` 与 `coefficientInterval` 实例连接起来。三轴版本也不证明源项与真实残差的同一性。真实残差/平移系数绑定、其余 11 类、45 个接触、68,063 叶覆盖和最终 `ThomsonNineClaim` 仍未形式化，也没有外审。

## 13. 2026-10-19 19:25 双源目标区间绑定

`formal/ThomsonNine/TwoSourceBindings.lean` 由 `export_two_source_bindings.py` 从归档 JSON 生成，覆盖除 `.t126` 外的全部 **32** 个双源目标；加上 `TargetBinding.lean` 的 `.t126`，共 **33/807** 个目标已有 Lean 区间证书。

- 每个目标的目标指数 `k` 恰有两个源指数：`k` 本身，以及 `k` 在某一轴加一后的 `k'`。
- 对应系数表达式为 `c1 + (k_axis+1) * c2 * a_axis`；区间证书使用 `mem_mul_of_bounds` 的 8 个文字角点比较，最后用 `mem_subset` 证明归档 `coefficientInterval .tNNN` 包含该两项和。
- `Axioms.lean` 对这 32 个定理逐一 `#print axioms`；统一复核当时为 **310** 条审计、69 模块闭包、`leanchecker` exit 0（19:25）。
- 局限：这些定理只说明归档区间包含给定的两项表达式；它们**没有**证明这两项就是真实残差/平移系数，也没有覆盖其余 774 个目标。807/807 仍是 `verify_aaa_shift_binding.py` 的 Python 精确检查，不是 Lean 定理。

## 14. 2026-10-19 20:10 三/四源链式区间绑定

`formal/ThomsonNine/ChainBindings.lean` 由 `export_chain_bindings.py` 从归档 JSON 生成，覆盖 **54** 个单轴链式目标：27 个三源目标 `k, k+1, k+2` 和 27 个四源目标 `k, k+1, k+2, k+3`。

- 每个目标的系数表达式为 `c0 + (n1*c1)*a + ...`，其中第 j 个源项的系数迭代乘以 `a` 共 j 次；区间侧用 `mem_mul_of_bounds` 的精确角点逐次乘中心区间，最后 `mem_add` 求和并用 `mem_subset` 连接归档 `coefficientInterval`。
- `Axioms.lean` 对这 54 个定理逐一 `#print axioms`；统一复核当时为 **364** 条审计、70 模块闭包、`leanchecker` exit 0（20:10，644.5 s）。
- 连同 `TargetBinding.lean`（1 个）和 `TwoSourceBindings.lean`（32 个），共 **87/807** 个目标有 Lean 区间证书。
- 局限：这些仍是区间算术证书，不证明源项等于真实残差/平移系数，也不覆盖其余 720 个目标；807/807 仍是 Python 精确检查。

## 15. 2026-10-19 21:27 `.t126` 完整 807 项 gathered coefficient 绑定

`formal/ThomsonNine/GatheredBinding.lean` 定义 `allTerms : List TermIndex`（807 项，manifest 顺序）和
`gathered k c a = ∑ t ∈ allTerms.filter (k ≤ exponents t), expandedCoefficient (exponents t) k (c t) a`。

- 对 `k = exponents .t126`，用 `rfl` 证明过滤后的源项恰为 `[.t126, .t137]`；其余 805 项因某一轴指数小于目标指数而贡献为零，已被过滤器排除。
- 证明两项 `expandedCoefficient` 分别等于 `c .t126` 和 `(10 * c .t137) * a 1`，再调用 `TargetBinding.target_t126_interval_bound`。
- 因此，在原始源系数分别属于 `R1`、`R2`、中心坐标属于 `A1` 的前提下，完整 807 项展开后的 gathered coefficient 落入归档 `coefficientInterval .t126`。
- 这仍不是“真实残差系数就是这 807 项”的证明；`c` 和 `a` 仍是满足区间前提的任意实数。它的进步是把“只绑定列出的两项”升级为“绑定全部 807 项展开后的真实 gathered 系数”。
- 统一复核当时为 **365** 条审计、71 模块闭包、`leanchecker` exit 0（21:27，675.3 s）。

## 16. 2026-10-19 全部 33 个 two-source 目标的完整 807 项 gathered 绑定

`formal/ThomsonNine/GatheredTwoSource.lean` 由 `export_gathered_two_source.py` 生成，覆盖除 `.t126` 外全部 32 个 two-source 目标。每个定理形如

```lean
theorem tNNN_gathered_mem (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (h0 : R1_tag.mem (c .tNNN)) (h1 : R2_tag.mem (c .tMMM))
    (ha : A_tag.mem (a axis)) :
    (coefficientInterval .tNNN).mem (gathered (exponents .tNNN) c a)
```

证明结构统一：`rfl` 证明 807 项过滤后恰为 `[.tNNN, .tMMM]`；两项 `expandedCoefficient` 分别化为 `c .tNNN` 与 `(n * c .tMMM) * a axis`；最后调用已有的 `TwoSourceBinding.target_tNNN_tag_interval_bound`。因此这 32 个定理不再只是“列出的两项的区间包含”，而是**全部 807 项展开后的 gathered coefficient** 的区间绑定。

- 连同 `.t126`，33/33 个 two-source 目标均有完整 807 项 gathered 证书。
- 54 个 chain 目标仍只有列出来源的区间证书；其余 720 个目标尚未做 gathered 绑定。
- `TwoSourceBindings.lean` 的 `Q/R1/R2/A/P/K` 定义改为公开，供 `GatheredTwoSource` 引用；生成器同步修改。
- 统一复核为 **397** 条审计、72 模块闭包、`leanchecker` exit 0（22:17，670.1 s）。

## 17. 2026-10-20 03:26 全部 87 个结构化目标的完整 807 项 gathered 绑定

`formal/ThomsonNine/GatheredChain.lean` 由 `export_gathered_chain.py` 生成，覆盖 54 个三/四源单轴链式目标。每个定理把 807 项过滤后得到的全部贡献精确化为 `c0 + (n1*c1)*a + ...` 的链式表达式，并调用已有 `ChainBinding.target_tNNN_tag_interval_bound`。

- 连同 33 个 two-source 目标，87/807 个已有区间证书的目标现在全部有完整 807 项 gathered 证书；不再有“只绑定列出来源”的结构化目标。
- 这些定理仍以源系数属于 `Rj`、中心坐标属于 `A` 为前提；没有证明 `c`/`a` 是真实残差系数和真实中心。
- 其余 720 个目标尚没有任何 Lean 绑定；真实残差识别、其他 11 类、45 个接触、68,063 叶覆盖和最终 `ThomsonNineClaim` 仍未完成。
- 统一复核为 **451** 条审计、73 模块闭包、`leanchecker` exit 0（269.4 s）。

## 18. 2026-10-20 03:56 全部单源目标的完整 807 项 gathered 绑定

`formal/ThomsonNine/SingleSourceBindings.lean` 由 `export_single_source.py` 生成，覆盖 19 个单源目标。对单源目标，807 项过滤后只剩自身，`gathered` 等于 `c .tNNN`；因此定理只需证明归档 `coefficientInterval .tNNN` 包含原始 `R` 区间。

- 19 个单源目标全部加入；连同 33 个 two-source、54 个 chain，共 **106/807** 个目标有完整 807 项 gathered 证书。
- 仍未证明这些 `c` 是真实残差系数；其余 701 个目标（源数 ≥5 或尚未结构化）无 Lean 绑定。
- 统一复核为 **470** 条审计、74 模块闭包、`leanchecker` exit 0（228.3 s）。

## 19. 2026-10-20 04:38 五源单轴 chain 的完整 gathered 绑定

`formal/ThomsonNine/FiveSourceBindings.lean` 由 `export_five_chain.py` 生成，覆盖 21 个五源单轴 chain 目标。每个目标先证明系数区间表达式包含在归档 q 中，再把 807 项 gathered 和化为五个 `expandedCoefficient` 项并调用该区间定理。

- 21 个五源目标加入；连同 19 个单源、33 个双源、54 个三/四源 chain，共 **127/807** 个目标有完整 807 项 gathered 证书。
- 仍未证明这些源系数是真实残差系数；剩余 680 个目标（源数 ≥5 的多轴/未结构化目标等）无 Lean 绑定。
- 统一复核为 **491** 条审计、75 模块闭包、`leanchecker` exit 0（663.5 s）。

## 20. 2026-10-20 05:27 六源单轴 chain 的完整 gathered 绑定

`formal/ThomsonNine/ChainRestBindings.lean` 由 `export_chain_rest.py` 生成，覆盖 21 个六源单轴 chain 目标。每个目标先证明系数区间表达式包含在归档 q 中，再把 807 项 gathered 和化为六个 `expandedCoefficient` 项并调用该区间定理。

- 21 个六源目标加入；连同 19 个单源、33 个双源、54 个三/四源 chain、21 个五源 chain，共 **148/807** 个目标有完整 807 项 gathered 证书。
- 仍未证明这些源系数是真实残差系数；剩余 659 个目标（源数 ≥7 的 chain 和多轴/未结构化目标）无 Lean 绑定。
- 统一复核为 **512** 条审计、76 模块闭包、`leanchecker` exit 0（219.2 s）。

## 21. 2026-10-20 06:10 通用顺序幂缓存引理

`SparseTranslation.lean` 新增：

```lean
def powInterval (A : RatInterval) : ℕ → RatInterval
  | 0 => const 1
  | n + 1 => mul (powInterval A n) A

theorem powInterval_mem (A : RatInterval) (a : ℝ) (ha : A.mem a) (n : ℕ) :
    (powInterval A n).mem (a ^ n)
```

这是后续把多源 tail-chain 的逐层 `K` 区间压缩成“一次幂区间 + 一次乘法”的通用基础。当时未把它用于新的目标绑定；当时覆盖为 **148/807**。统一复核为 **513** 条审计、76 模块闭包、`leanchecker` exit 0（614.5 s）。

## 22. 2026-10-20 06:54 七源单轴 chain 绑定

`export_seven_chain.py` 生成 `SevenSourceBindings.lean`，覆盖 15 个七源单轴 chain 目标。每个目标仍用逐层 `K` 区间和 `mem_mul_of_bounds` 的精确角点证明，并用完整 807 项过滤后的 `gathered` 表达式调用对应区间定理。

- 生成器修正：生成文件结尾必须为 `end ThomsonNine.SevenSource`，不能沿用 `ChainRest`；否则报 `Invalid name after end`。
- 编译：`=== OK SevenSourceBindings ===` 06:28:36。
- 审计：新增 15 条，总数 **528**；模块闭包 **77**。
- 统一复核：`LOCAL_LEAN_COMPILER_AXIOMS_AND_KERNEL_PASS`，06:54；`leanchecker` exit 0（294.4 s）。
- 覆盖：**163/807**；剩余 644 个目标（源数 ≥8 的 chain 和多轴/未结构化目标）。
- 这些仍是条件区间命题，不证明源系数等于真实残差系数，也不覆盖其他 11 类、45 个接触方程、68,063 个叶结点或最终 `ThomsonNineClaim`。

## 23. 2026-10-20 08:05 八源与九源单轴 chain 绑定

`export_eight_chain.py` 生成 `EightSourceBindings.lean`（15 个八源目标），`export_nine_chain.py` 生成 `NineSourceBindings.lean`（9 个九源目标）。两者沿用七源生成器的逐层 `K` 区间和 `mem_mul_of_bounds` 精确角点模板，并用完整 807 项过滤后的 `gathered` 表达式调用对应区间定理。

- 编译：`EightSourceBindings` 07:09:18；`NineSourceBindings` 07:49:17。
- 审计：新增 15 + 9 = 24 条，总数 **552**；模块闭包 **79**。
- 统一复核：`LOCAL_LEAN_COMPILER_AXIOMS_AND_KERNEL_PASS`，08:05；`leanchecker` exit 0（271.5 s）。
- 覆盖：**187/807**；剩余 620 个目标（源数 ≥10 的 chain 和多轴/未结构化目标）。
- 这些仍是条件区间命题，不证明源系数等于真实残差系数，也不覆盖其他 11 类、45 个接触方程、68,063 个叶结点或最终 `ThomsonNineClaim`。

## 24. 2026-10-20 08:47 十源与十一源单轴 chain 绑定

`export_ten_chain.py` 生成 `TenSourceBindings.lean`（9 个十源目标），`export_eleven_chain.py` 生成 `ElevenSourceBindings.lean`（3 个十一源目标）。模板仍是逐层 `K` 区间、`mem_mul_of_bounds` 精确角点与完整 807 项 `gathered` 过滤。

- 十源生成器修正：部分目标在 `norm_num` 后 `Nat.choose 3 1` 已被化简为 `3`，固定 `rw [hc]` 会报 “Did not find an occurrence”；改为 `try rw [hc]` 后编译通过。
- 编译：`TenSourceBindings` 08:29:15；`ElevenSourceBindings` 08:20:02。
- 审计：新增 9 + 3 = 12 条，总数 **564**；模块闭包 **81**。
- 统一复核：`LOCAL_LEAN_COMPILER_AXIOMS_AND_KERNEL_PASS`，08:47；`leanchecker` exit 0（245.8 s）。
- 覆盖：**199/807**；剩余 608 个目标（源数 ≥12 的 chain 和多轴/未结构化目标）。
- 仍是条件区间命题，不证明源系数等于真实残差系数；其他 11 类、45 个接触方程、68,063 个叶结点和最终 `ThomsonNineClaim` 未完成，无外审。

## 25. 2026-10-20 09:33 十二至十七源单轴 chain 绑定

`export_twelve_chain.py` … `export_seventeen_chain.py` 分别生成 `TwelveSourceBindings.lean` … `SeventeenSourceBindings.lean`，每个模块 3 个目标，共 18 个。模板仍为逐层 `K` 区间、`mem_mul_of_bounds` 精确角点与完整 807 项 `gathered` 过滤。

- 编译：`Twelve`、`Thirteen` 约 08:53 前完成；`Fourteen`、`Fifteen`、`Sixteen`、`Seventeen` 依次通过，最后一个 `SeventeenSourceBindings` 在 09:16 前完成。
- 审计：新增 18 条，总数 **582**；模块闭包 **87**。
- 统一复核：`LOCAL_LEAN_COMPILER_AXIOMS_AND_KERNEL_PASS`，09:33；`leanchecker` exit 0（244.0 s）。
- 覆盖：**217/807**；剩余 590 个多轴/未结构化目标（已无可用的单轴 chain 类）。
- 仍是条件区间命题，不证明源系数等于真实残差系数；其他 11 类、45 个接触方程、68,063 个叶结点和最终 `ThomsonNineClaim` 未完成，无外审。

## 26. 2026-10-20 10:15 五源多轴原型：端点归一化阻断

单轴 chain 类已全部覆盖（217/807）后，尝试处理 18 个五源多轴目标。原型为 `.t125`（指数 `(0,9,9)`，源 `.t125,.t126,.t136,.t137,.t255`）。

设计上避免逐目标展开二项式：每个源用

```lean
Kj := expandedCoefficientInterval (exponents .tNNN) (exponents .t125) Rj
        (fun i n => powSigned (A i) n)
```

得到贡献区间，再用 `expandedCoefficient_mem_of_center_box` 证明成员关系，用 `mem_sumIntervals` 合并 5 项，最后用 `mem_subset` 与 `Q` 的端点比较。

实现与测试结果：

- 生成器 `/tmp/gen_multi_one.py` 写出 `formal/ThomsonNine/MultiFiveTest.lean`（约 12 KB，未导入根模块、未加审计、未改变 582 审计 PASS）。
- `hk0..hk4` 和 `hs` 已通过；最终端点比较失败：
  - 默认心跳下：`(deterministic) timeout at whnf, maximum number of heartbeats (200000) has been reached`；
  - 提高到 1,000,000 心跳后：`unsolved goals`，剩余目标仍含未归约的 `powSigned A_i d`、`min`/`max` 和嵌套有理数条件。
- 根因：`expandedCoefficientInterval` 内部的 `powSigned` 是递归定义，`simp`/`norm_num` 在 5 个三层乘积上无法自动展开到字面端点；继续加 `min_def`/`max_def`/`Rj.h`/`Kj.h` 仍不能闭合。该路线目前不可扩展。
- 因此没有新增多轴目标；覆盖仍为 **217/807**，审计仍为 **582**，模块仍为 **87**，统一 PASS 与捆绑包状态不变。
- 下一步若继续多轴：应为每个源显式生成字面区间 `K_j`，用 `mem_mul_of_bounds` 的 8 个精确角点逐层证明（与 `ChainBindings` 相同的模板），最后只对字面 `K_j` 和 `Q` 做端点比较，避免在 `powSigned`/`min`/`max` 上做全局归一化。
- 这些仍只是条件区间命题，不证明源系数等于真实残差系数，也不覆盖其他 11 类、45 个接触方程、68,063 个叶结点或最终 `ThomsonNineClaim`；无外审。

## 27. 2026-10-20 11:14 五源多轴 `.t125` 字面角点证书

- 新增 `formal/ThomsonNine/MultiCornerBindings.lean`（命名空间 `ThomsonNine.MultiCorner`），目标 `.t125`，指数 `(0,9,9)`，五个源为 `.t125,.t126,.t136,.t137,.t255`。
- 方法：对每个源/轴构造字面区间 `S` 与 `C`，用嵌套 `mem_mul_of_bounds` 的 8 个精确文字角点证明成员关系；`Ksum` 用右嵌套 `add` 表达式，最终 q 包含端点用 `unfold Q Ksum C0..C4; rw [Rat.le_iff]; norm_num [RatInterval.add]` 关闭。
- `t125_sum` 证明五个 `expandedCoefficient` 的右嵌套和属于 `Q_t125`；`t125_gathered` 用 807 项过滤等式 `[.t125,.t126,.t136,.t137,.t255]` 连接到 `gathered`，并证明结果属于 `(coefficientInterval .t125)`。
- 构建：`MultiCornerBindings` 11:01:53、`Axioms` 11:03:37、根入口 1m16.6s、`LocalVerification` 11:06:05。统一复核 **583 审计 / 89 模块**，kernel 345.9 s，`LOCAL_LEAN_COMPILER_AXIOMS_AND_KERNEL_PASS`，仅 `propext/Classical.choice/Quot.sound`。
- 覆盖由 217/807 增至 **218/807**；其余 23 个五源多轴目标未生成。生成器 `export_multi_corner.py` 目前只处理 `.t125`；扩展到 delta≥2 需要幂链 `S = ((const ch * A) * A) ...` 与不同 `choose` 的处理。
- 这是条件区间/ gathered 绑定的一个实例，不是真实残差识别，也不证明最终 `ThomsonNineClaim`。

## 28. 2026-10-20 13:20 十五个五源多轴 delta≤1 目标

- `export_multi_corner.py` 现批量生成 15 个五源多轴目标：`t125,t244,t330,t404,t470,t532,t538,t591,t608,t648,t672,t699,t726,t740,t766`；每个目标保留字面 `Q/R/S/C/Ksum` 区间、`mem_mul_of_bounds` 角点证明和 `..._gathered` 定理。
- `MultiCornerBindings.lean` 于 12:07:40 编译通过；`Axioms`、根入口、`LocalVerification` 随重建通过。
- 统一复核 `LOCAL_LEAN_COMPILER_AXIOMS_AND_KERNEL_PASS`：**597 审计 / 89 模块**；root 69.5 s、axioms 75.8 s、kernel 204.7 s；仅 `propext/Classical.choice/Quot.sound`。
- 覆盖由 217/807 增至 **232/807**；剩余 9 个五源多轴目标 delta≥2：`t449,t464,t476,t485,t509,t553,t565,t619,t802`。这些需要 `S = ((const ch * A) * A) ...` 的幂链与不同 `choose` 的处理。
- 仍是条件区间/gathered 绑定，不识别真实残差；不证明最终 `ThomsonNineClaim`，无外审。

## 29. 2026-10-20 13:20 九个五源多轴 delta≥2 目标

- 新增 `formal/ThomsonNine/MultiCornerPowBindings.lean`（命名空间 `ThomsonNine.MultiCornerPow`），覆盖剩余 9 个五源多轴目标：`t449,t464,t476,t485,t509,t553,t565,t619,t802`。
- 生成器 `export_multi_pow.py` 对每个源/轴构造幂链 `S0 := const ch`（`ch=1` 时从 `A` 开始），逐层 `mul S A`，用 `mem_mul_of_bounds` 的 8 个精确角点证明；C 区间乘 `R` 与三个最终 `S`；`Ksum` 右嵌套；`..._gathered` 过滤 807 项并调用 `..._sum`。
- 关键修正：d≥2 的 `hK` 等式用 `unfold expandedCoefficient shiftFactor; norm_num [Nat.choose]; try ring; try simp`，同时处理 `... ∨ c=0` 和纯等式；C 角点 `simp only` 必须包含全部中间 `S` 层定义。
- `MultiCornerPowBindings` 13:06:42 编译通过；`Axioms`、根入口、`LocalVerification` 重建通过。统一复核 `LOCAL_LEAN_COMPILER_AXIOMS_AND_KERNEL_PASS`：**606 审计 / 89 模块**；root 59.8 s、axioms 66.9 s、kernel 250.3 s；仅 `propext/Classical.choice/Quot.sound`。
- 覆盖 **241/807**（19 单源 + 33 双源 + 54 三四源链 + 21 五源链 + 21 六源链 + 15 七源 + 15 八源 + 9 九源 + 9 十源 + 3 十一源 + 18 十二至十七源 + 24 五源多轴）。仍有 566 个多轴/非结构化目标。
- 这些仍是条件区间/gathered 命题：源系数属于归档 `R`、中心属于 `A`，不证明它们就是真实残差系数，也不覆盖其他 11 类、45 个接触方程、68,063 个叶结点或最终 `ThomsonNineClaim`；无外审。
- 复核包已重打并安装为 `proof_work/THOMSON_N9_REVIEW_BUNDLE.zip`：**279 条目、约 16.5 MB**，277 个文件哈希 0 失配，PASS 报告 619 审计/90 模块；SHA-256 `以最终构建日志为准`。旧包归档为 `THOMSON_N9_REVIEW_BUNDLE_2026-10-20_1408.zip`（277 条目、SHA-256 `b7bdaf25...`）。


## 30. 2026-10-20 14:08 十三个八源三轴目标与分组阻断

- 八源三轴类共 24 个目标。按“每个源独立乘出系数、最后求和”的字面区间模板，只有 **13 个**目标的逐源区间和被归档 q 包含；新增到 `MultiCornerPBindings.lean`：
  `t234,t243,t525,t543,t603,t639,t668,t675,t689,t698,t723,t728,t764`。
- 其余 **11 个**（如 `.t114=(0,8,9)`）全部局部成员关系都能编译，但最终端点目标化为 `False`。精确有理数检查显示：逐源和严格宽于 q（`sum.lo < q.lo` 且 `q.hi < sum.hi`）。原因是 q 由按轴顺序分组平移生成，区间乘法不对分组和分配；不能靠调 `norm_num` 解决。
- 用按轴分组的精确重放（先固定轴 0 目标、按其余坐标分组求和，再轴 1、轴 2）对 `.t114` 检查，得到 `contained True`，两侧安全余量约 `3.4e-190`、`4.4e-190`。这给出后续 11 个目标的形式化路线：生成与 `shift_axis` 同序的分组字面区间，而不是逐源乘积。
- 当前已加入的 13 个目标只覆盖逐源和可包含的情形；它们仍是条件区间证书，不识别真实残差系数。覆盖 **254/807**；剩余 553 个多轴/非结构化目标。
- 统一复核 PASS：619 审计、90 模块；root 65.1 s、axioms 69.4 s、kernel 231.6 s。复核包 279 条目、约 16.5 MB，SHA-256 `以最终构建日志为准`。


## 31. 2026-10-20 14:25 十一个八源目标的逐源阻断与分组重放

- 剩余 11 个八源三轴目标（`.t114` 等）的逐源乘积区间和严格宽于归档 q；局部成员关系可编译，但最终端点为 `False`，不是 `norm_num` 性能问题。
- 对 `.t114=(0,8,9)` 按 `shift_axis` 同序做精确有理数分组重放：轴 0 按 `(e1,e2)` 分组，轴 1 按 `e2` 分组，轴 2 收尾；结果 `contained True`，`sum.lo-q.lo≈3.37e-190`、`q.hi-sum.hi≈4.38e-190`。
- 因此 11 个目标的正确后续证书不是“逐源乘积后求和”，而是“分组求和 → 乘下一轴因子 → 再分组”的字面区间模板。该模板尚未形式化，覆盖仍为 **254/807**，PASS 仍为 619 审计/90 模块。


## 32. 2026-10-20 14:45 首个分组轴八源目标 `.t114`

- `GroupedT114.lean`（命名空间 `ThomsonNine.GroupedT114`）覆盖 `.t114=(0,8,9)` 的 8 个完整源：`.t114,.t115,.t125,.t126,.t136,.t137,.t245,.t255`。
- 证明按归档 `shift_axis` 的顺序分组：轴 0 按 `(e1,e2)` 求和，乘轴 1 因子后按 `e2` 求和，再乘轴 2 因子；每一级用 `mem_mul_of_bounds` 的 8 个角点引理，最后用 `mem_subset` 比较归档 q。
- 关键修复：轴因子必须写成**左结合**幂链；组名/单例组假设需按目标表达式归一化；`hH` 求和需 `add_assoc` 重关联；最终端点用 `simp only` 展开全部级联定义后 `rw [Rat.le_iff]; norm_num [RatInterval.add, RatInterval.mul]`；`gathered` 等式需把 `exponents` 纳入 `simp` 并用 `ring`。
- 统一复核 PASS：**620 审计、91 模块**；root 151.8 s、axioms 154.4 s、kernel 473.1 s；只出现 `propext/Classical.choice/Quot.sound`。
- 覆盖 **255/807**；其余 10 个八源目标可用同一分组模板继续生成。仍是条件区间证书，不识别真实残差系数，也不证明最终 `ThomsonNineClaim`。


## 33. 2026-10-20 15:55 十个八源三轴目标

- 新增 `Grouped124,321,329,396,403,583,590,612,647,739.lean`，复用 `.t114` 的分组轴模板，覆盖剩余 10 个八源三轴目标。
- 统一复核 PASS：**630 审计、101 模块**；覆盖率 **265/807**。其余 542 个多轴/非结构化目标仍未形式化；真实残差、其他 11 类、45 接触、68,063 叶与最终定理仍未完成，无外审。

## 34. 2026-10-20 16:20 首个 11 源目标
- `Grouped103.lean` 覆盖 `.t103=(0,7,9)` 的 11 个源；推广后的分组模板编译通过，统一复核 **631 审计/102 模块**，覆盖 **266/807**。

## 35. 2026-10-20 17:05 再完成八个 11 源目标
- 新增 `Grouped123,224,242,312,328,463,469,517.lean`，均为 11 源三轴分组轴证书。统一复核 **639 审计/110 模块**，覆盖 **274/807**。

## 36. 2026-10-21 00:52 再完成五个 11 源目标
- 新增 `Grouped531,547,574,615,629.lean`。统一复核 **644 审计/115 模块**，覆盖 **279/807**。其余 7 个 11 源目标未完成。
