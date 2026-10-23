# 跨 n 实例复用与许可边界审计（2026-10-23）

## 已核对的公开项目

| 项目 | 公开位置 | 公开时间 | 许可证信息 | 当前处理 |
|---|---|---:|---|---|
| n=7 | `huwngtran/thomson-n7-lean` | 2026-09-28 | 仓库没有 `LICENSE` 文件，README 也没有明确代码许可 | 不复制代码；只引用公开定理和验证流程 |
| n=8 | `jstoobysmith/Thomson-N-8-Warrant` | 2026-09-24 | README 声明 Apache 2.0；API 元数据没有识别到许可证文件 | 若未来复用代码，先保留声明并取得明确许可确认 |
| n=9 先例 | `aravindkarthigeyan/thomson-n9-lean` | 2026-10-06 | MIT License | 作为相关工作引用，不把其代码并入本仓库 |

时间和仓库元数据来自 GitHub API；定理范围和验证方式来自各项目当前公开 README。该记录没有把 README 中的 AI 生成声明或数学结论当作本项目的验证结果。

## 本仓库当前策略

1. `ThomsonCertificate.GenericBernstein`、`GenericCoverage` 和 `GenericFramework` 是本仓库新写的通用内核原型。
2. n=9 的现有证书和模型仍然是本仓库的专用数据；没有把 n=7/n=8 的源码复制到通用模块中。
3. 未来适配 n=7/n=8 时，只接入公开的定理接口、声明映射和新写适配层；任何逐文件复制必须先完成许可证和来源确认。
4. 在声称“跨实例复用”前，需要完成文件级来源比对，并记录实际复用的定理、代码和证书数据范围。

## 投稿中的准确表述

在来源比对完成前，只能说：

> the repository contains a newly written generic certificate kernel prototype and a planned adapter architecture

不能说所有 n=7/n=8 证明已经由本仓库统一形式化，也不能把上游项目的唯一性定理写成本项目结果。若未来完成适配，应分别列出上游项目、许可证、保留的版权声明和本仓库新增的代码。
