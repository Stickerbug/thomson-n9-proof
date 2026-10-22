# 主覆盖证明：进行中（2026-10-22T01:01:58.905747+00:00）

正式根入口当前为 577 模块、1499 项公理审计，编译与审计通过；完整 fresh 重放尚未完成。此前 433 模块的 fresh 重放被环境恢复中断。规范复核包仍保留已完整验证的 183 模块、1446 项审计检查点，不得覆盖为新的 PASS。历史条件目标基线为 272 个不同目标；807/807 条件系数目标已完成，不能当作最终全局定理。

真实十二类源盒非负性、全部 45 项接触方程已正式集成。隔离工作区另外完成了两点正性依据、内积严格小于 14/25、候选能量小于固定 U、Coulomb 残差的全局装配接口。装配中的全覆盖前提仍待消除。

主覆盖必须针对 Coulomb 残差 Rf，而不是 Hermite 多项式残差 RH。真实 F 的系数中点误差、六置换对称化、真实 c 的上界和 K/D 分解已接通：MainCoverage.Envelope、MiddleModel、KernelEnvelope 均编译通过。MainCoverage.TreeSound.check_sound 给出全部五类覆盖叶及递归分裂的通用正确性；CutCover 证明分块前缀覆盖；AxisSound.axisCertificateOK_sound 证明一维 Taylor/对角多项式/截断尾项/Bernstein 取整证书的正确性。它们仍需与全部具体数据实例连接。

覆盖树共 136125 节点、68063 个叶，已导出为 498 个检查块，另外 497 个上层分裂节点；终端所需一维区间键为 4810 个。三轴矩阵转换使用整数收缩而非逐项全展开；五个根张量的 Python 精确预检匹配归档数值。四组仿射 Bernstein 矩阵和 4816 个一维对角缓存节点已全部通过 Lean。根张量、区间下界、主树的具体检查仍在运行，进度分别见 root_tensor_build_order_progress.json、axis_build_order_progress.json、main_tree_build_order_progress.json。

所有正在运行的长任务均通过 work/daemon_launch.py 分离到 PID 1 下，保留 formal/.lake。构建包装器使用内存锁串行化大型数值证明，小型对角证书可并行；新增 RSS/cgroup 保护会记录资源终止，不写成 PASS。此前一次新叶引理过度展开触发 OOM，已改为通用四项引理并编译通过，缓存保留。当前冻结 ThomsonNineClaim 尚未证明；Lean 自带内核重放不是外部独立验证。
