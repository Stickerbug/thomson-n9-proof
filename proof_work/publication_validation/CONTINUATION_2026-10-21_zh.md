# 2026-10-21 接续记录：七个 grouped11 目标正式集成

验证完成时间：2026-10-21T22:54:28+08:00（UTC+08:00）。

## 接手时实际状态

按请求先读取 `HANDOFF_STATE.json`；指定的本文件在接手快照中不存在，已核对旧交接文件、历史报告、日志和所有进程。
新环境没有运行中的 Lean 构建或内核重放；因此未中断既有任务。
CPU cgroup 配额为 `400000/100000`，即 4 核；affinity 为 0–4；内存上限为 17,179,869,184 字节（16 GiB），无已配置交换空间。

本环境没有带入项目 `.olean`，历史依赖缓存解压也未完成，旧报告不能作为当前环境的新验证。
保留了整个 `formal/.lake`，复用其源码与压缩缓存，恢复固定依赖后重新编译。
Lean 为 4.34.1 x86_64；Mathlib 固定在 `d13f23b723b8a846827a245b89c10fc7d3f11612`，其余依赖也按 manifest 校验。
`LocalLDLSemantics.lean`、`IntervalLinear.lean` 两份源码在仓库快照中缺失，已从既有规范复核包恢复，SHA-256 与历史 PASS 报告逐项一致。
另恢复规范复核包要求的三份缺失历史文件 `analytic10_2026_sum.c`、`exact128_2026.c`、`verify_sharp2026_final_linkage.py`，其哈希与旧包内清单一致。
上轮被描述为运行中的 ThomsonNine 根入口重放没有随本快照保留；本轮重新完成该步骤。

## 正式集成

- 七份 `Grouped646/664/677/697/720/738/762.lean` 从 experimental 迁入 `formal/ThomsonNine/`。
- `ThomsonNine.lean` 与 `Axioms.lean` 全部导入七份模块；新增七条 `tNNN_gathered` 公理审计。
- `LocalVerification.lean` 现在导入正式根入口，覆盖全部已集成证明；只增加导入，不断言全局定理。
- `export_grouped_generic.py` 使用相对自身的路径。七份已集成文件与由归档输入重新生成的文件逐字节相同。
- 构建脚本及 verifier 支持 `LEAN_BIN_DIR`/PATH，去掉旧 `/home/dsh` 和 aarch64 固定路径；统一构建按依赖先编译 root，再编译 LocalVerification 和 Axioms。
- verifier 记录去重目标清单和重复声明；同时要求两次 `--fresh` 重放通过。
- 打包器要求 651/122/279、成功的两次 fresh 重放及日志/源码/产物哈希匹配，拒绝过期 PASS；实测 RUNNING 报告被拒绝，原规范包哈希不变。

## 正式结果与统计口径

权威报告：`local_lean_verification.json`；构建戳：`local_lean_build_stamp.json`。

| 项目 | 本轮结果 |
|---|---|
| 状态 | `LOCAL_LEAN_COMPILER_AXIOMS_AND_KERNEL_PASS` |
| 公理审计 | 651 条，按顺序精确匹配，无重复审计名称 |
| 允许公理 | `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx` |
| 模块闭包 | 122（含根入口、LocalVerification 和 Axioms） |
| 条件覆盖 | 279/807 个不同目标；286 条 gathered 审计声明 |
| 11 源三轴 grouped | 21/21 已集成并复核 |
| 内置内核重放 | `leanchecker --fresh ThomsonNine.LocalVerification` exit 0，846.1 s |
| 正式根入口重放 | `leanchecker --fresh ThomsonNine` exit 0，851.4 s |

历史 279 条 gathered 声明实际上对应 272 个不同目标，重复的是
`t449、t485、t509、t553、t565、t619、t802`，各自同时出现在 FiveSource 和 MultiCornerPow 中。
因此新增七个后是 **279/807**，不是 286/807。历史阶段日志保留以便溯源，旧覆盖数字以本节去重口径为准。
本轮构建模式：`adopt`；显式采用外部构建时仍记录为采用，不称为 verifier 从零构建。
数据导出器重现检查/负测、正式根入口编译、651 条公理审计、源码禁用项扫描及两次 fresh 重放均通过。
整个覆盖树的 Python 独立精确算术重算未在本轮重新运行；包中保留其历史证据。

## 复现与避免重复工作

```bash
cd /workspace/thomson-n9-proof
export LEAN_BIN_DIR=/workspace/cloud-setup/lean-4.34.1-linux/bin
# 保留并复用 proof_work/publication_validation/formal/.lake
python3 -B proof_work/publication_validation/verify_local_lean.py --reuse-local-build
```

在其他机器上将 `LEAN_BIN_DIR` 设为自己的固定 Lean 4.34.1 工具链；源码齐备、依赖缓存恢复后可不加复用选项进行统一编译。
每次继续前应核对进程与本轮日志，避免重复构建；不能用不存在的旧 olean 或旧 PASS 充当当前证据。
复核包为 `proof_work/THOMSON_N9_REVIEW_BUNDLE.zip`；包清单记录每个有效载荷的哈希。
最终包的条目数、大小与 SHA-256 写入根目录 `HANDOFF_STATE.json`，避免将包自身哈希写入包内导致循环。

## 仍未完成

这些证书以固定源系数属于 R 区间、中心属于 A 区间为前提，尚未识别为真实残差的平移系数。
其余未覆盖目标、其他类完整 Hessian、45 个接触等式、rank-33/W 兼容、68,063 叶 Lean 实例化及最终全局下界均仍有工作。
`ThomsonNineClaim` 和全局唯一性未证明。`leanchecker` 复用 Lean 自己的内核，不是外部独立实现；本轮没有外部评审。
