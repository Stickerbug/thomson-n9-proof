# 通用证书内核阶段验收（2026-10-24）

本记录对应阶段 A 的轻量验收，不替代 n=9 根入口的完整 fresh 重放。

## 验收范围

在保留 `formal/.lake` 缓存的工作目录中，重新编译以下七个独立模块：

- `ThomsonCertificate.GenericBernstein`：任意有限维 Bernstein 张量的非负性；
- `ThomsonCertificate.GenericCoverage`：任意盒、点和域谓词的有限覆盖树归纳；
- `ThomsonCertificate.GenericPSD`：PSD 二次型、矩形合同约化和有限 PSD 求和；
- `ThomsonCertificate.GenericFramework`：覆盖树、Bernstein 叶证书和 PSD 求和接口的组合玩具实例；
- `ThomsonCertificate.GenericCertificate`：带自然数实例索引的证书对象和统一 soundness 定理；
- `ThomsonCertificate.GenericLowerBound`：把证书目标连接到原始配置能量下界的桥接定理；
- `ThomsonCertificate.GenericMinimum`：候选、可行性、能量恒等式和全局下界的统一合同。

执行命令（Lean 4.34.1）：

```sh
cd proof_work/publication_validation/formal
PATH=/workspace/cloud-setup/lean-4.34.1-linux/bin:$PATH \
  lake env lean -o .lake/build/lib/lean/<module>.olean <module>.lean
```

七个命令均退出码 0；GenericBernstein、GenericCoverage、GenericPSD、GenericFramework、GenericCertificate、GenericLowerBound 和 GenericMinimum 的实测耗时分别约为 5.53 s、1.05 s、1.63 s、2.20 s、1.50 s、10.5 s、2.0 s。七个源文件中均没有 `ThomsonNine` 导入或名称引用（用 `rg` 检查）。

## 当前源哈希

| 源文件 | SHA-256 |
|---|---|
| `formal/ThomsonCertificate/GenericBernstein.lean` | `db6abcc44c9b3b7f751ceacb61e101837a71eb774e90b539faa17dd0bb466965` |
| `formal/ThomsonCertificate/GenericCoverage.lean` | `209cb644b98e455fcbabdd6d1a340e94d9817fcd966e8937827180991a613199` |
| `formal/ThomsonCertificate/GenericPSD.lean` | `575bc6526a7f794926e04c764a8d5c12a38f619332a4694a4dc20bf1a48fed8e` |
| `formal/ThomsonCertificate/GenericFramework.lean` | `d9d2b8bde3cfeebe8547b77b36bcebd5b708ea2e888bca1a29c4685c96d1cfd1` |
| `formal/ThomsonCertificate/GenericCertificate.lean` | `94b40064bbb90009625e874b69af02d97a3a4891cfa9ae1b31ec80e6e7db7ce9` |
| `formal/ThomsonCertificate/GenericLowerBound.lean` | `8b206b1979790a6c74ac9b955f1bbf74e80e8a7f6cc596b98d28872c9a54f94e` |
| `formal/ThomsonCertificate/GenericMinimum.lean` | `57e673196b5d3a3e7bc9fe571098f70e1d1a5578f216c16b8b7eaa2b20230fbb` |

## 解释和边界

这验证了可复用的证书对象、覆盖树语义、Bernstein 张量、PSD 代数引理、能量下界桥接和最小值合同可以在不引用 n=9 数据的情况下独立编译。它没有证明任意 `n` 都存在证书，也没有把 n=9 的候选构型、807 个系数目标或物理域数据参数化；这些仍属于 n=9 适配器。完整 n=9 验证的既有记录（2390 模块、1507 项审计、807/807 目标以及 13228.165 秒 fresh kernel replay）保持不变，本次没有重复运行。
