# Thomson n=9 项目转接说明（给下一个 AI）

更新时间：2026-10-21  
仓库：https://github.com/Stickerbug/thomson-n9-proof（private，`main`）  
本文件是对话的**完整工作上下文转接**；不是原始聊天记录的逐字导出。

## 0. 直接指令

继续推进 Thomson n=9 的 Lean 形式化。当前成果是**本地、条件性的证明候选**，不是最终定理，也没有外部评审。不要声称 `ThomsonNineClaim` 已证明，不要把条件区间证书说成真实残差绑定。

最高优先级：
1. 保持现有 `LOCAL_LEAN_COMPILER_AXIOMS_AND_KERNEL_PASS` 可复现；
2. 继续把 11 源三轴目标的 grouped 证书从 14/21 推到 21/21；
3. 再处理真实残差/平移系数绑定、其他 11 类、45 个接触、68,063 叶覆盖，最后才是 `ThomsonNineClaim`。

## 1. 权威状态（2026-10-21）

- 验证报告：`proof_work/publication_validation/local_lean_verification.json`
  - status：`LOCAL_LEAN_COMPILER_AXIOMS_AND_KERNEL_PASS`
  - `axiom_audits = 644`
  - 模块闭包：115
  - axioms 仅 `propext`、`Classical.choice`、`Quot.sound`
  - kernel：`leanchecker ThomsonNine.LocalVerification` exit 0
  - scope：`Local certificate implications only; final ThomsonNineClaim is unproved.`
- stamp：`proof_work/publication_validation/local_lean_build_stamp.json`
- 条件系数覆盖：**279/807**
- 规范复核包：`proof_work/THOMSON_N9_REVIEW_BUNDLE.zip`
  - 304 entries，16,641,132 B
  - SHA-256 `7d99da9b3c542ca84b14a793875ab6ad13354d80dd61717f5a3a755247d0cac9`
- Git 最新提交：`ee2e7be`（本转接文件会再产生一个提交）
- 仓库 private；如需公开，由仓库所有者改 Settings → Visibility。

## 2. 已经完成什么

### 2.1 AAA H00 坐标 Hessian 证书

- 807 项原始稀疏项，550 项二阶求导后非零；`LocalSparseHessianAAABase`、`Chunk00`–`Chunk07`、组装 `LocalSparseHessianAAA` 全部编译。
- 非零项使用 `IntervalLocalOps.mem_mul_of_bounds` 的 8 个精确有理角点，避免逐项 `norm_num` 展开 807 个系数区间。
- 零项走快速路径；`t257` 是唯一的正窄区间特例。
- 定理 `actual_h00_mem` 仍是**条件定理**：假设系数族属于 `coefficientInterval`、点属于 `relativeBox`。

### 2.2 统一复核器

`proof_work/publication_validation/verify_local_lean.py` 会：
- 解析 67→115 模块闭包；
- 要求恰好/至少 644 条 `#print axioms`（每个关键审计都在）；
- 扫描禁用词 `sorry/admit/axiom/native_decide/#eval/run_cmd/...`；
- 重新编译 root/Axioms，或 `--adopt-build` 采用 mtime/hash 合格的外部产物；
- 运行 second-kernel `leanchecker`；
- 通过后才写 PASS report/stamp。

构建脚本：`proof_work/publication_validation/formal/build_direct.sh`。

### 2.3 条件系数绑定（279/807）

- 单源：19 个（`SingleSourceBindings.lean`）
- 双源：33 个（`TwoSourceBindings.lean` + `GatheredTwoSource.lean`）
- 3/4 源单轴 chain：54 个（`ChainBindings.lean` + `GatheredChain.lean`）
- 5 源：21 个单轴 chain + 24 个多轴 = 45 个（`FiveSourceBindings`、`MultiCornerBindings`、`MultiCornerPowBindings`）
- 6 源单轴 chain：21 个（`ChainRestBindings`）
- 7–17 源单轴 chain：15+15+9+3+18 个（`Seven...SeventeenSourceBindings`）
- 8 源三轴：13 个逐源 contained + 11 个 grouped；`.t114` 首个 grouped，随后 10 个，共 24 个全部完成。
- 11 源三轴：21 个目标中 **14 个**已完成并复核：`.t103`、`.t123`、`.t224`、`.t242`、`.t312`、`.t328`、`.t463`、`.t469`、`.t517`、`.t531`、`.t547`、`.t574`、`.t615`、`.t629`。
- 剩余 7 个 11 源目标：`.t646`、`.t664`、`.t677`、`.t697`、`.t720`、`.t738`、`.t762`。
  - 源文件已经生成并编译过，但**没有**进入 644 审计闭包；
  - 已隔离在 `proof_work/experimental/grouped11/`；
  - 不要再把它们说成已验证。

## 3. grouped 生成器

`proof_work/publication_validation/export_grouped_generic.py` 是推广到任意 m 源的生成器。

用法：

```bash
cd "/home/dsh/Thomson Problem"
python3 proof_work/publication_validation/export_grouped_generic.py <target_index> <output.lean> <Namespace>
```

它从以下文件读取数据：
- `proof_work/publication_validation/independent_hermite_RH_result.json` 的 `R_coefficients`
- `proof_work/publication_validation/independent_local_00_AAA.json` 的 `shifted_polynomial` 和 `new_center_intervals`

生成的每个文件包含 `tNNN_sum` 和 `tNNN_gathered`，按照 `shift_axis` 的真实分组顺序：
轴 0 按 `(e1,e2)` 分组求和 → 乘轴 1 因子 → 按 `e2` 分组 → 乘轴 2 因子 → 与归档 q 做端点比较。

生成器关键坑（已修，不要回退）：
- 成员证明必须写在 theorem 内，不能放顶层 `private def` 引用 `a`/`c`；
- `T.mem ((expr))` 需要外层括号；
- 单例 group 的 `c*1` 会归一化成 `c`；需要 `simpa` 别名；
- group 求和必须右嵌套，`mem_add` 才是右嵌套；
- 端点必须 `simp only [全部级联定义, RatInterval.const]`，再 `rw [Rat.le_iff]; norm_num [RatInterval.add, RatInterval.mul]`；
- `heq` 的 RHS 必须用 `c .tNNN`，并 `simp [expandedCoefficient, shiftFactor, Nat.choose, exponents]; ring`。

单目标编译约 5–9 分钟（主要成本是 Base olean 导入）。

## 4. 复现命令

```bash
cd "/home/dsh/Thomson Problem/proof_work/publication_validation/formal"
./build_direct.sh LocalVerification
cd "/home/dsh/Thomson Problem"
python3 -B proof_work/publication_validation/verify_local_lean.py --adopt-build
```

期望最后一行：`LOCAL_LEAN_COMPILER_AXIOMS_AND_KERNEL_PASS`。

注意：
- 当前 644/115/279 是**已复核口径**；
- 7 个 experimental 文件不在 root/Axioms 导入中，不要误加后直接宣称 PASS；
- 任何新增 theorem 都要加 `#print axioms`、重建 root/Axioms/LocalVerification，再跑 verifier。

## 5. 未完成/后续路线

1. 完成剩余 7 个 11 源目标：生成、编译、加入 `ThomsonNine.lean`/`Axioms.lean`、+7 audits，预期 **651 审计 / 122 模块 / 286-of-807**，再 PASS。
2. 继续更大的三轴类：12、13、14、17、20、21、…、807 源；生成器已支持任意 m，但每个目标的展开成本和 group 数会上升。
3. 真实残差/平移系数绑定：目前所有 279 个都是“给定源系数属于 R、中心属于 A”的条件区间证书；尚未证明它们等于真实 residual/shifted polynomial 的系数。
4. 其他 11 个类、45 个接触方程、rank-33/W 兼容、68,063 叶覆盖实例化。
5. 最终 `ThomsonNineClaim` 和全局唯一性。

## 6. 对话历史（按阶段）

1. 接手被上下文限制中断的 `session-345db606`；确认旧 `local_lean_verification.json` 过期并隔离。
2. 重写 verifier v3（严格 import、注释剥离、67 模块闭包、TOCTOU、273 审计、禁用词）。
3. 发现 550 个非零项逐项 `norm_num` 不可行（单 term >193 s）；改为 `mem_mul_of_bounds` 8 角点。
4. 编译 Base/Chunk00–07/assembly；首次统一 PASS（273→274→277→278→…）。
5. 建立 33 个双源、54 个 3/4 源 chain、19 个单源等条件证书；逐步升到 106、148、163、217、254。
6. 建立 5/6/7–17 源单轴 chain；8 源三轴先做 13 个逐源 contained。
7. 发现逐源求和不等于 q 的分组结构；`.t114` 首个 grouped 成功。
8. 10 个 8 源三轴 grouped 完成，265/807。
9. 推广到 11 源，`.t103` 完成，266/807；再 8 个、再 5 个，达到 279/807、644 审计/115 模块。
10. GitHub：创建 private 仓库、推送 2,092 文件；大 JSON 放 Release；7 个未复核实验模块隔离。
11. 当前请求：生成此转接说明并上传。

## 7. 重要注意事项

- 这个环境里 `write` 工具曾产生 broken l2s symlink；写文件优先 bash heredoc/Python。`git add` 会因 broken symlink 报 `Operation not permitted`，要显式列出 regular files。
- `leanchecker` 在 proot 下可能挂起；不要在普通 shell 里随意跑单模块 `leanchecker`，统一走 verifier。
- 不要把 `.lake/`、toolchain、`python_deps/` 提交进 Git；见 `LARGE_DATA.md` 和 Release。
- 仓库是 private；大数据在 https://github.com/Stickerbug/thomson-n9-proof/releases/tag/data-2026-10-21。
- 所有覆盖数字都是**条件区间证书**口径，不是最终定理。

## 8. 关键文件

- `proof_work/publication_validation/local_lean_verification.json`
- `proof_work/publication_validation/local_lean_build_stamp.json`
- `proof_work/publication_validation/AAA_PARTIAL_STATUS_2026-10-19_zh.md`（当前 §36 记录 279/807）
- `proof_work/publication_validation/CONTINUATION_2026-10-19_zh.md`
- `proof_work/publication_validation/README_local_lean.md`
- `proof_work/publication_validation/VALIDATION_STATUS_zh.md`
- `proof_work/THOMSON_N9_CURRENT_zh.md`
- `NEXT_SESSION_HANDOFF_zh.md`
- `LARGE_DATA.md`
