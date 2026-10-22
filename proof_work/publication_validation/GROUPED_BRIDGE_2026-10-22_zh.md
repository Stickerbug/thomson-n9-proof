# 通用 grouped/gathered 桥梁与 807 源试点

完成时间：2026-10-22T01:01:24+08:00（UTC+08:00）。

## 正式结果

统一状态 `LOCAL_LEAN_COMPILER_AXIOMS_AND_KERNEL_PASS`：**293/807 个不同条件目标、674 项公理审计、138 模块**。
新增目标只有 t000；原先 292 个全部保留。当前 300 条 gathered 声明，重复目标仍为历史七项，不按声明数重复计算覆盖。
一次 `leanchecker --fresh ThomsonNine.LocalVerification` exit 0，耗时 615.2 s，实际闭包 137 模块，完整覆盖 136 模块的正式根入口。
Axioms 单独编译且严格限于 import / #print axioms。仅 propext、Classical.choice、Quot.sound，无 sorryAx。

## 新增数学内容

`GroupedTranslation.lean` 定义对任意有限源列表的目标筛选与两层按键分组：先按剩余 (v,t) 坐标汇总 u 轴贡献，再按 t 汇总 v 轴贡献，最后乘 t 轴因子求和。
通用 regroup 定理证明按键归并保持加权总和；由两次应用得到 `groupedCoeff_eq_gatheredOn`，严格等于完整二项式展开的 gathered 系数。
它不限制源数、不要求源索引互异，也不要求系数或中心为正。
`groupedInterval_mem` 利用已有乘法、有限和和幂表成员引理，证明同一算法的有理区间包含真实 gathered 系数。
`groupedInterval_mem_of_bounds` 仅在显式端点比较成立后转入目标区间。

现有 SparseTranslation 的单轴/三轴区间传播定理继续复用；新实现采用逐目标筛选和按键归并，直接对应 gathered，减少对全局中间索引表重索引的证明负担。
这里没有新增原 `shiftAxesCoeff` 与 gathered 的全局定义等式；本轮的桥梁针对 `Grouped.groupedCoeff`，名称和表达式见 Lean 源码。

`AAAGroupedData.lean` 从归档 R_coefficients 和中心区间导出 807 个源区间，校验它们与已形式化目标的指数顺序一致。
每个区间的良定义由普通 `decide +kernel` 检查；显式全项列表覆盖全部 TermIndex 构造子的定理也已证明。
`computed_mem_gathered` 将通用算法统一实例化到任意一个 AAA 目标，前提为固定源系数族的源区间成员关系以及固定中心的区间成员关系。
该定理的结论是新算法的 computed 区间；转到归档 coefficientInterval 仍需端点证据。

`AAAGroupedPilot.lean` 用普通 `decide +kernel` 完整检查 t286 与 t000 的两个端点。
t000 的全部 807 个原始源项均有贡献，随后由通用定理得到 `t000_gathered`，无需手写 807 项展开归并证明。
t286 只作数值回归，没有添加第二条 gathered 声明；正式覆盖仅新增 t000。
三个新模块共增加十条审计，详情在 aaa_grouped_bridge_result.json。

## 性能与后续批量证书

通用定理模块约 367.3 KiB，归档数据与桥梁模块约 3.14 MiB，试点模块约 16.9 KiB。
隔离样本：t286 编译约 2.5 s，t000 约 36.1 s；t000 运行时曾观察到约 8.9 GiB RSS，此值不是峰值测量。
这说明直接重复归约所有目标的巨大精确分数会耗费内存；没有将 807 目标全部塞进一个未经资源评估的 decide 调用。
既有 45 个 grouped 精简模块、其他历史证明与 formal/.lake 均保留；本轮仅编译三个新数学模块和三个汇总入口。

针对新算法的精确 Fraction 预检在 9.30 s 内通过全部 807 项归档包含关系。
进一步把幂表及两层中间分组结果向外舍入到 768 位，在 3.69 s 内仍通过 807/807 项，最终分母最多 1537 位；1024 位也全部通过。
数值脚本为 check_cached_grouped_numeric.py，记录为 aaa_cached_grouped_feasibility.json。
这些 Python 结果只是下一步构造缓存证书的可行性证据，不是 Lean 端点证书，不增加正式覆盖。
下一步应证明可缓存中间包围的分阶段证书正确性，并输出共享幂表与两层分组见证，减少重复展开和分母增长。
之后继续真实残差/平移系数绑定，不恢复按低源数机械堆叠独立模块。

## 统一验证与复现

export_aaa_grouped_data.py --check --self-test 校验源码、清单和三个畸变数据负例（缺项、指数错位、反向区间），已进入统一 verifier。
全部历史数据导出、45 项 compact 复现、验证回归测试、674 项公理审计、禁用项扫描和完整闭包重放均通过。
期望配置为 local_lean_expected.json；报告与构建戳绑定其哈希以及所有可达源码/产物。
四个打包负测继续验证：RUNNING、缺失重放模块、未带 --fresh 的命令和错误产物哈希都被拒绝，旧规范包保持完整。

```bash
cd /workspace/thomson-n9-proof
export LEAN_BIN_DIR=/workspace/cloud-setup/lean-4.34.1-linux/bin
python3 -B proof_work/publication_validation/export_aaa_grouped_data.py --check --self-test
python3 -B proof_work/publication_validation/verify_local_lean.py --reuse-local-build
python3 -B proof_work/publication_validation/check_cached_grouped_numeric.py --bits 768 1024
```

规范复核包仍为 proof_work/THOMSON_N9_REVIEW_BUNDLE.zip；最终条目数、大小与 SHA-256 在 HANDOFF_STATE.json。

## 证明边界

本轮证明了通用分组算法和 t000 的条件归档系数界；整批 807 个归档端点的 Lean 证书尚未完成。
源系数尚未识别为真实残差系数，区间包含零不代表接触值精确为零。
H00 的 550 活跃项前提弱化、其他类完整 Hessian、45 接触等式、rank33/W、68,063 叶 Lean 实例化、最终 ThomsonNineClaim 与全局唯一性仍未完成。
Lean 自带内核重放不是外部独立验证；本轮未重跑完整 Python 覆盖树算术，也没有外部评审。
