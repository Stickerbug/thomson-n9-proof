# 真实残差的十二类局部非负性

本轮在隔离工作区 `work/translation20261022` 完成十二个原始绝对源盒上的真实残差非负性。统一定理为 `ThomsonNine.ActualLocal.all_twelve_residual_nonnegative`，源码位于 `work/translation20261022/LocalAll/Nonnegative.lean`。它仅要求点属于指定源盒，以及实际 Gram 行列式非负。九个内部盒事实上无需 Gram 前提。

已通过的数学连接包括：真实半径与全部 45 项接触方程、十二个真实中心的零残差、内部梯度零、边界切向接触、完整残差的 807 项平移系数、真实一阶和二阶导数的全盒区间，以及从这些区间到局部非负性的微积分证明。边界盒使用扩大的第一坐标区间，先证明下侧 Gram 曲面上非负，再通过严格正的第一偏导延拓。

平移采用逐坐标 Horner 算法，每个中心三轮。十二个中心的 36 个平移模块全部通过 Lean，每中心算术贡献数由直接平移约 58,791 项降至 12,030 项。内部 DFF 盒使用简单有理合同矩阵 `[[1,0,0],[1,1,0],[2/5,-3/5,1]]`。其余内部盒和三个边界的二维 Hessian 区间可直接通过 Schur 正性证书。

验证证据：`work/translation20261022/all_locals_build.log` 最终记录 `ALL12_ACTUAL_SOURCE_BOX_NONNEGATIVITY_AND14_AXIOM_AUDITS_PASS`；`LocalAll/Axioms.log` 的十四项关键声明只依赖 `propext`、`Classical.choice`、`Quot.sound`。新增局部证明压缩为 144 个正式模块，已进入根入口，当前 577 模块编译及 1499 项公理审计通过。正式结果见 `actual_local_nonnegativity_result.json`，集成日志见 `work/localintegration20261022/integration.log`。此前 433 模块的完整 fresh 重放被环境恢复中断，当前 577 模块的完整重放尚未完成；不得把编译与公理审计通过写成完整重放通过。规范复核包仍保留此前已完整验证的 183 模块检查点。

两点正性依据、严格内积排除界 14/25、实际候选能量的固定上界以及使用 Coulomb 残差的全局装配接口已在隔离工作区编译通过，尚未进入本次 577 模块检查点。全局仍需完整主覆盖树的真实残差算术与局部叶连接，以及消除最终装配中的覆盖前提。冻结的 `ThomsonNineClaim` 尚未证明；Lean 自带内核重放也不等于外部独立验证。历史覆盖基线仍为 272 个不同条件目标，现有条件系数目标覆盖为 807/807，不能当作全局证明完成度。
