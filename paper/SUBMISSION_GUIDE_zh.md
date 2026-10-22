# Thomson n=9 发布与投稿步骤

这份指南按“先 arXiv，再投期刊”的路线编写。当前论文和复核包已经完成，外部网站的账号创建、上传和发布仍需要作者本人操作。

## 当前稿件信息

- 标题：`A Lean-Verified Computer-Assisted Proof of the Nine-Point Thomson Minimum`
- 作者：Jingxing Huang
- 单位：Qian Xuesen College, Xi'an Jiaotong University
- ORCID：`0009-0002-9805-0331`
- 通讯邮箱：`adult-huang@outlook.com`
- Funding：No external funding
- Conflict of interest：No competing interests
- 论文 PDF：`paper/main.pdf`
- LaTeX 源码：`paper/main.tex`
- 紧凑上传包：`paper/THOMSON_N9_MANUSCRIPT_SOURCE.zip`
- 论文路线：先发 arXiv，再投期刊

## 第一步：本地冻结与留档

1. 确认 `paper/main.pdf` 的作者、单位、ORCID、邮箱、AI 披露、Funding 和 Conflict of interest 都正确。
2. 保存当前复核包 `proof_work/THOMSON_N9_REVIEW_BUNDLE.zip`，并记录 `HANDOFF_STATE.json` 中的 SHA-256。
3. 若要在独立机器重放 Lean，安装 Lean 4.34.1 和指定 Mathlib，设置 `LEAN_BIN_DIR`，保留 `formal/.lake`，再运行：

   ```sh
   python3 -B proof_work/publication_validation/verify_local_lean.py
   ```

   完整 fresh replay 在记录环境中约需 3 小时 40 分钟。只发布当前已经记录的 PASS 时，不需要再次启动这项长任务。
4. 编译论文时运行：

   ```sh
   cd paper
   latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
   ```

## 第二步：提交 arXiv 预印本

1. 打开 <https://arxiv.org>，用作者邮箱注册或登录，完成邮箱验证和可能的学科 endorsement。
2. 选择 **Submit a new submission**，上传 `THOMSON_N9_MANUSCRIPT_SOURCE.zip`。压缩包根目录包含 `main.tex` 和 `main.pdf`，预览系统中选择 `main.tex` 作为主文件。
3. 填写元数据：
   - Title：使用论文标题的原文。
   - Authors：`Jingxing Huang`。
   - Affiliation：`Qian Xuesen College, Xi'an Jiaotong University`。
   - ORCID：`0009-0002-9805-0331`。
   - Abstract：从 `main.tex` 的 abstract 原样复制。
   - Comments：可写 `5 pages; Lean 4.34.1 formalization and reproducibility bundle available at https://github.com/Stickerbug/thomson-n9-proof`。
4. 分类建议：主分类先选 `math.MG`（Metric Geometry）；可根据 arXiv 页面接受情况添加 `math-ph` 和 `cs.LO`。若系统要求 endorsement，按页面指引完成。
5. 许可建议：先使用 arXiv 的非排他分发许可，除非目标期刊或学校有明确的开放许可要求。
6. 在最终预览中逐页检查标题、作者、单位、公式、参考文献和 AI 披露。确认 arXiv 编译结果与本地 5 页 PDF 一致后提交。
7. 保存 arXiv 编号和版本号，例如 `arXiv:xxxx.xxxxxv1`。后续改稿必须上传新版本并保留版本记录。

## 第三步：发布代码和 DOI

1. 在 GitHub 仓库中提交当前源码、论文和复核包，创建带说明的 release。release 说明应包含 Lean 版本、fresh replay 状态、复核包 SHA-256 和文章范围限制。
2. 将 GitHub release 连接到 Zenodo，创建对应的 DOI。Zenodo 元数据填写作者、单位、ORCID、关键词（Thomson problem、sphere energy、Lean、formal verification、computer-assisted proof）和许可证。
3. DOI 产生后，再把 DOI 和正式 release version 写回论文、`paper/README.md` 和 arXiv comments；这一步会改变文件哈希，应重新编译论文并重建复核包。

## 没有 arXiv endorsement 时的替代路线

endorsement 只影响 arXiv 的提交权限，不影响其他预印本平台、代码归档或期刊投稿。短期内建议按下面的顺序发布：

1. **先发 GitHub release + Zenodo DOI。** 这是当前最稳妥的即时方案。GitHub release 保存源码和复核包，Zenodo 对该 release 生成 DOI。记录 DOI、release tag、上传日期和 `THOMSON_N9_REVIEW_BUNDLE.zip` 的 SHA-256。页面标题应写成“software/research data and formal verification archive”，正文中把 `paper/main.pdf` 标为 manuscript/preprint，不要把 DOI 记录写成同行评审期刊论文。
2. **向 Xi'an Jiaotong University 的机构知识库或图书馆提交。** 询问学校是否提供作者自存档、预印本或科研成果归档服务；提交 PDF、LaTeX 源码、GitHub release 和 Zenodo DOI。学校平台的许可和公开时间以图书馆规定为准。
3. **可选：HAL 或 OSF Preprints。** 这些平台通常不要求 arXiv endorsement，适合存放数学预印本；仍需遵守各平台的账号、内容审核和许可规则。若平台允许，使用同一 PDF、同一作者信息和 Zenodo DOI，避免产生多个内容不同的版本。
4. **直接向期刊投稿。** 期刊投稿系统不要求 arXiv endorsement。上传 PDF、LaTeX 源码、复核包链接和 `COVER_LETTER_TEMPLATE.md` 修改版；cover letter 中写明“a public Zenodo/GitHub research archive is available”即可。期刊接受后，再把正式 DOI 和期刊版本补入所有归档记录。

ResearchGate 等社交平台可以作为分享入口，但不应作为唯一的长期归档。viXra 也不适合作为这项工作的主要引用记录，因为数学同行通常更信任 Zenodo、机构知识库、HAL/OSF 或正式期刊。

没有 arXiv endorsement 时，建议在标题和摘要中使用“preprint”或“research archive”，在同行评审完成前不要写“published article”或“peer-reviewed result”。以后获得 endorsement 后，可以把同一版本提交为 arXiv v1，并在 arXiv 元数据中填写 Zenodo DOI。

## 第四步：选择期刊并投稿

可以先把 `Experimental Mathematics` 作为首选方向，因为它接收计算机辅助的具体数学证明；如果更强调形式化验证，可考虑 `Journal of Symbolic Computation`；如果更强调严格数值证书，可查看 `Mathematics of Computation` 的最新投稿范围。提交前必须阅读目标期刊当年的 author guidelines，确认篇幅、数据政策和 AI 披露要求。

1. 在期刊系统创建作者账户，填写 Jingxing Huang、Xi'an Jiaotong University、ORCID 和通讯邮箱。
2. 上传论文 PDF；按系统要求另传 LaTeX 源码、补充材料和 `THOMSON_N9_REVIEW_BUNDLE.zip` 或其下载链接。
3. 上传并修改 `COVER_LETTER_TEMPLATE.md`，填入期刊名称、编辑姓名（若已知）和 arXiv/DOI 信息。
4. 在声明页面填写：无外部资助、无利益冲突、代码和证书公开、AI 使用披露。论文当前明确说明 Lean 自身 fresh replay 不等于外部独立验证，也没有声称所有最小构型的全等唯一性。
5. 提交后保存 manuscript ID、提交日期和系统邮件。审稿意见到达后，用同一个版本号和复核包记录逐项回复。

## 提交前最终检查

- [ ] arXiv 编号和版本号已保存。
- [ ] GitHub release 已创建，Zenodo DOI 已生成或明确暂未生成。
- [ ] 目标期刊和 cover letter 已确定。
- [ ] 作者、单位、ORCID、邮箱和通讯作者标记正确。
- [ ] Funding、Conflict of interest、AI disclosure 与论文一致。
- [ ] 没有把 Lean 内核重放写成外部独立验证，也没有写成所有最小构型唯一。
- [ ] DOI 或 release version 写入论文后，重新编译并更新所有 SHA-256。
