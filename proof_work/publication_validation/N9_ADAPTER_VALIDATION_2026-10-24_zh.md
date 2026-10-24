# n=9 通用证书适配器阶段验收（2026-10-24）

`formal/ThomsonCertificate/ThomsonNineAdapter.lean` 将冻结的 n=9 全局残差定理接入 `Certificate 9` 接口。它编译通过，并提供：

```lean
ThomsonNine.n9_certificate_sound
```

执行命令：

```sh
cd proof_work/publication_validation/formal
PATH=/workspace/cloud-setup/lean-4.34.1-linux/bin:$PATH \\
  lake env lean -o .lake/build/lib/lean/ThomsonCertificate/ThomsonNineAdapter.olean \\
  ThomsonCertificate/ThomsonNineAdapter.lean
```

退出码为 0，实测耗时约 3.4 秒。该文件有意导入 n=9 专用的 `MainCoverage.Final`，所以它是实例适配器，不属于通用内核。

当前适配器把已经证明的 `ordered_residual_from_frontier` 作为一个叶证书包装进 `Certificate 9`。它验证了接口和定理类型兼容性，没有重复展开 807 项证书树，也没有改变 `ThomsonNine.thomsonNineClaim_proved`。下一步的结构化适配器需要把 n=9 的 `CutTree`、状态转移和叶终止理由逐层映射到通用 `Tree`，以便报告真正复用的树语义代码量。
