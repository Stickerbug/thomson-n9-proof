# 后续 13 个目标：低源数缺口及十三源多轴证书

验证完成时间：2026-10-22T00:04:17+08:00（UTC+08:00）。

## 结果

- 统一状态：`LOCAL_LEAN_COMPILER_AXIOMS_AND_KERNEL_PASS`。
- 664 条公理审计，135 模块；仅 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。
- 292/807 个不同条件 gathered 目标（299 条声明），相较前轮 279/807 新增 13 项。
- `leanchecker --fresh ThomsonNine.LocalVerification` exit 0，用时 993.5 s。
- `leanchecker --fresh ThomsonNine` exit 0，用时 996.3 s。
- 当前报告、构建戳为 `local_lean_verification.json`、`local_lean_build_stamp.json`；精确期望集合为 `local_lean_expected.json`。

## 新增目标

| 源数 | 变化坐标数 | 目标 |
|---|---|---|
| 5 | 2 | t597 |
| 9 | 2 | t381、t409、t653 |
| 13 | 2 | t286、t334、t703 |
| 13 | 3 | t388、t402、t456、t475、t589、t596 |

七个 11 源三轴目标及先前成果保持通过；本轮的十三项均先单独编译，再加入 root/Axioms。
定理结论均为完整 807 项源定义的 `gathered` 系数属于目标归档区间，条件仍是各贡献源系数及中心区间的成员关系。
每项的贡献源集合由 `allTerms.filter` 经 Lean `rfl` 核对，代数归并由 `simp`/`ring` 完成，区间运算与端点比较交 Lean 检查。

## 计算与复用

接续时无运行中的 Lean 任务；实际配额仍为 4 核 CPU、16 GiB 内存。
先核对前轮 122 模块的源码和 `.olean` 哈希，再复用整个 `formal/.lake`，没有重编历史证明模块。
新增模块最多两个编译进程，每个 `-j2`；不同进程写不同产物。随后顺序编译正式根入口与 LocalVerification，并以显式 adopt 模式做统一验证。

三个十三源双轴目标的两个轴平移次数均达到 6，最初触及 100 万 heartbeat 上限。
生成器对最高轴平移次数至少 5 的情形使用有限的 1000 万额度，并关闭冗余 unusedSimpArgs 提示。
只重新生成和编译失败的 t286、t334、t703；其他成功文件保持不变。没有增加数学假设或证明逃逸。
十三项的精确 Fraction 分组包围预检查通过；按当前生成器重新生成的文件与集成文件逐字节一致。
工作记录保留在 `work/next13/`；大编译日志和缓存不进复核包。

## 统一验证与打包门槛

`local_lean_expected.json` 同时记录审计数、模块数、精确去重目标清单及正式根入口应包含的模块。
verifier 检查这些集合、禁止项、全部公理输出、两次 fresh 重放和验证期间源码/产物不变；期望文件哈希进入报告及构建戳。
打包器使用同一期望和已通过报告的真实模块闭包；所有源码、产物、日志哈希仍须匹配。
已实测旧的 651 项审计 PASS 被拒绝，原规范复核包保持不变。

复现：

```bash
cd /workspace/thomson-n9-proof
export LEAN_BIN_DIR=/workspace/cloud-setup/lean-4.34.1-linux/bin
python3 -B proof_work/publication_validation/verify_local_lean.py --reuse-local-build
```

新增目标时须先更新 `local_lean_expected.json`，保留已有去重目标及根入口模块，新增 root/Axioms 导入并编译，再统一复核。
规范包仍为 `proof_work/THOMSON_N9_REVIEW_BUNDLE.zip`；最终条目数、大小和 SHA-256 记录于根目录 `HANDOFF_STATE.json`。

## 下一步与证明边界

现在全部贡献源数不超过 13 的目标均已覆盖。仍有 515 项未覆盖，下一类为 14 源三轴的 30 项：
`t092, t113, t122, t214, t233, t241, t303, t320, t327, t395, t448, t481, t508, t524, t537, t550, t564, t582, t607, t617, t638, t645, t660, t671, t688, t696, t717, t725, t737, t760`。
根据本轮用户提出的效率问题，下一步优先推广精简生成与批量算法证书，不继续机械添加这 30 项。
具体实测、工具与边界见 `OPTIMIZATION_2026-10-21_zh.md`；也需推进实际残差及平移系数识别。

实际残差绑定、其他类完整 Hessian、45 个接触等式、rank-33/W 兼容、68,063 叶 Lean 实例化和最终全局下界仍未完成。
`ThomsonNineClaim` 与全局唯一性均未证明。Lean 自带内核重放不是外部独立实现，也没有外部评审。
本轮没有重新运行整个覆盖树的独立 Python 精确算术重算，包中保留其历史记录。
