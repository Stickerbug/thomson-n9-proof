# 45 个 grouped 模块精简与统一验证优化

完成时间：2026-10-22T00:24:25+08:00（UTC+08:00）。

## 正式结果

45 个 grouped 模块已全部替换为精简证明并正式复核。统一状态为 `LOCAL_LEAN_COMPILER_AXIOMS_AND_KERNEL_PASS`。
覆盖率保持 **292/807 个不同条件目标**，仍为 **664 项公理审计、135 模块**（299 条 gathered 声明）。
没有添加目标或假设；审计名称哈希、精确目标集合、全部公开定理签名及区间定义与前轮一致。
仅标准三公理 `propext`、`Classical.choice`、`Quot.sound`；无 `sorryAx` 或证明逃逸。

| 项目 | 前轮 | 本轮 |
|---|---:|---:|
| 45 个 grouped .olean 合计 | 7,255,420,392 字节 | 50,256,824 字节 |
| 相同 LocalVerification 入口 --fresh | 993.5 s | 551.8 s |
| 发布流程的完整重放总时间 | 1989.8 s（两次） | 551.8 s（一次） |

产物合计缩小约 **144.4 倍**。时间为相同环境下各一轮实测，并非重复采样基准；
完整重放总时间还包含取消重复重放的收益，不能全部归因于证明项精简。
机器实际配额为 4 核 CPU、16 GiB 内存；固定 Lean 4.34.1 与相同 Mathlib/cache。
详情与逐模块编译/哈希记录见 `compact_grouped_result.json`。

## 证明保持与生成复现

精简前的 44 个标准模块与原 generic 生成器逐字节相同（仅 option 行存在历史差别）；
精简仅复用既有 `mem_mul`，并用定义归约处理具体指数后规范化组合数及转换，再交 `ring`。
总共复用了 918 组乘法正确性引理，不再重复生成每组八个角点界。
旧版 `GroupedT114` 保留其原始定义、公开接口和三个预计算标量乘积的数值证明；
这三个区间不是定义成精确 `mul`，不能直接应用相同替换。其余可复用乘法与 gathered 归并已精简。
原模板存于 `compact_inputs/GroupedT114.lean`，不属于根入口导入闭包。

每个文件独立编译。44 项首次通过；t114 的三个标量界保留原证明后只重编该文件，未重复编译其他成功项。
编译最多两个进程、每个 `-j2`。标准模块的区间表达式与所有公开签名均作文本核对，最终由 Lean 验证证明。
`compact_grouped_manifest.json` 绑定旧/新源码、旧产物哈希和大小、复用次数；精确模块清单在 `local_lean_expected.json`。
`export_grouped_compact.py --check` 从原始数据/旧模板重新生成全部 45 项并逐字节比对，已纳入统一验证。

## 一次完整重放的覆盖保障

当前 LocalVerification 实际闭包含 134 模块，正式根入口闭包含 133 模块，后者完全包含在前者中。
全部 135 个本地模块等于 LocalVerification 闭包加上 Axioms。
Axioms 单独编译，并严格限制为 import 与 #print axioms；因此它没有未重放的独立数学证明。
verifier 采用 `single_fresh_local_closure_v1`：只运行一次
`leanchecker --fresh ThomsonNine.LocalVerification`，实际 exit 0；正式根入口由其传递导入完整覆盖，未另行运行 root --fresh。
报告和构建戳均绑定实际覆盖模块清单。任何根入口模块遗漏、仅被 Axioms 导入的数学模块都会被拒绝。
root、LocalVerification、Axioms 仍按依赖顺序重新编译，历史数学模块和 Mathlib 依赖缓存继续复用。

五项回归测试（含缺失/重复 compact 清单子例）及全部导出检查通过。
打包器重新计算真实导入图，并实测拒绝 RUNNING 报告、漏掉模块的内核覆盖、未带 --fresh 的重放命令和错误产物哈希。
四个负测均未改动旧规范包，之后恢复真实 PASS 报告；证据见结果 JSON。

```bash
cd /workspace/thomson-n9-proof
export LEAN_BIN_DIR=/workspace/cloud-setup/lean-4.34.1-linux/bin
python3 -B proof_work/publication_validation/export_grouped_compact.py --check
python3 -B proof_work/publication_validation/verify_local_lean.py --reuse-local-build
```

保留并复用 `formal/.lake`。本轮通过后只清理本轮 work 中创建的旧产物硬链接备份（7,255,420,392 字节），
当前有效缓存、固定依赖、原源码与前轮复核包均保留。规范复核包仍为 `proof_work/THOMSON_N9_REVIEW_BUNDLE.zip`，最终 SHA-256 在 HANDOFF_STATE.json。

## 下一步

精简已从隔离样本推广到全部正式 grouped 模块。接下来优先证明分轴平移/分组算法的通用 soundness，
用批量证书提供条件系数界，并推进真实残差/平移系数绑定；不要恢复机械地按源数增加小批目标。
本轮另运行现有 Fraction 分轴算法：3.81 s 内，三阶段均为 807 项，最后 807/807 归档包围检查通过。
这是批量路线的精确数值可行性检查，不是 Lean 证明，不计入正式覆盖率，也未绑定真实残差；源码和输入哈希及输出保存在结果 JSON。
当前 807 项接口不是数学上必须的 807 个独立定理。H00 仅 550 项可能贡献的分析尚未实现为弱化接口的 Lean 定理；其他 Hessian 分量须分别处理。

最终 ThomsonNineClaim、全局唯一性、真实残差绑定、其他类完整 Hessian、45 个接触、rank33/W、68,063 叶 Lean 实例化仍未完成。
Lean 自带内核重放不是外部独立验证，无外部评审；本轮未重跑完整 Python 覆盖树算术。
