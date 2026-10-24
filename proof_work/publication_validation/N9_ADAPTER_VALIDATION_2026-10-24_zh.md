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

这个语义适配器把已经证明的 `ordered_residual_from_frontier` 作为一个叶证书包装进 `Certificate 9`。它验证了接口和定理类型兼容性，没有重复展开 807 项证书树，也没有改变 `ThomsonNine.thomsonNineClaim_proved`。下面的结构化适配器进一步完成了 `CutTree`、状态转移和叶终止理由到通用 `Tree` 的映射。

## 结构化适配器

随后完成的 `formal/ThomsonCertificate/ThomsonNineStructuredAdapter.lean` 已经把 `CutTree` 递归映射到通用 `Tree N9Box`，并证明：

```lean
ThomsonNine.n9_structured_certificate_sound
```

该文件编译退出码为 0，实测约 2.5 秒。它使用 `n9TreeAt` 保留每个节点的 dyadic 状态和路径，`n9Split` 复用 `box_child` 与 `childCoordinates_mem` 证明子盒覆盖，叶节点逐个调用现有 `check_sound`。因此这是结构化适配器，仍然不改变冻结根定理，也没有重复运行完整 n=9 fresh replay。
