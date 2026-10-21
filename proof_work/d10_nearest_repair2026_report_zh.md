# 最小距离旧混合核修复：有限实验

新目标min ||z||²，x=oldref_projected+1e-4augZ z，固定eta=1e-7，全部190B变量、contact rank33的157自由方向；不是三endpoint权重凸包。oldref由旧mix originalA在共同N投影，并正交投影到augsol+augZ。额外Q_R>=1e-9、P_R>=1e-7，两约束乘1e6增强尺度；Rcuts>=eta*dist²，行scale=1/max(dist²,1e-6)。B>=1e-8I，trace<=2000，interiorH>=1e-6I，boundarylambda>=1e-8，correctedKt>=1e-6I。

继承b2全部mandatory和验证点、旧P/Q/CGF连接点，加旧mix弱Hessian特征方向±半径1e-4/1e-3/.01与边界投影全permutations，共mandatory5478，全部保留。完整域GramPSD∩[-1,.56]^3，无竞争过滤。

## 运行限制和返回状态

首次实际准备83.228秒，保存prepared results后被旧driver遗留build70assert拦下，未执行solver；另两次启动曾compile IndentationError退出，均未求解。原source冻结后，fresh resume_driver直接重建preparedN/Compiled/contactSVD，跳过来源诊断，恢复build20.635秒。resume最多两轮且>105秒不启下一轮；实际只一轮MaxTime，guard生效。resume总105.263秒，含前准备模型时间188.491秒；没有第二个SDP。

CLARABEL配置time_limit55，实际core56.727秒（迭代粒度轻微越界），wall63.568秒；不是硬实时55秒保证。status user_limit/MaxTime，primalres1.44e-11，gap_rel.0198。objective9.7995e8，||x−oldref||3.1304153，affine projection error8.215e-14；不认为这是最近可行点或最近距离下界。

返回点trace164.4126、minB7.92749e-8、contact2.30e-14、interiorH8.14e-5、Q_R4.51468e-7/P_R.0360315均达数值要求，但原A局部验证找到R=−.018433461992153677，于等边点约(−.19881268)^3，Gram=.8657038171。因此不exactify。全部rawscan和64originalA复核、local/DE点保存resume_scan_0.npz和resume_results.json，compiledDE不称独立。

## 旧种子审计：不是新增PSD或jets阻碍

原oldmix minB=1.42234e-6，trace160.24977，interiorHmin.000278048，lambda均>=1.2669e-5，correctedboundaryHmin.00243755；这些充分满足新增固定下界。contact误差1.35e-14，投影前后A最大改动2.84e-14。旧Q originalA R=−2.35100194867e-9，重构R=−2.35100183765e-9，排除了旧mix与共同N投影不一致。5478mandatory只有10点的R−eta*d²低于−1e-12，都在Q附近；最差未归一化margin−2.42477e-9。故该MaxTime大步位移不能用作小修复不可行证据，也不能归因于原mix不PSD或错jets。

保存完整N/B/A/x/c和源文件SHA。results SHA256=9dc24d736c949bc6db0c8f9238d9d44e47ffe610f64c0e8cd431e1e7e7b91ea3，finalA canonicalJSON SHA256=3341e251d107422bd231f8add3bb1db6dc49cb3a9166da9fcb179aa7cdd3b703。audit.json含恢复driver原文/哈希、旧种子约束审计、精确Fraction Gram成员性；R/A仍浮点，不能作严格证书。

本有限实验已结束。没有启动额外轮次或exactification。严格Thomson n9全局证明仍开放，严格LB未变；父应据上述数值未收敛和近可行seed审计决定下一步。
