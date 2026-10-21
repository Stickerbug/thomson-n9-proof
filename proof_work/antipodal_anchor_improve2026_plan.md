# 宽轴域一次四阶实验

独立有限研究，仅一次CLARABEL solve，time_limit=85秒，max_iter=130。
核仍为SO(2)轴向Qk，degree4，z奇偶分块。域|z|,|w|<=.63，t<=.57，Gram>=0。
训练使用已全区间认证h11：rhs=h(t)+(h(z)+h(-z)+h(w)+h(-w))/6。
训练包括随机三角、65x65的两个Gram边界面、z≈±w附近加密。
独立检查包含50000随机三角和一个限时DE，全部仅为数值诊断。
与父d12研究无重复，不改父证书/报告/manifest。

输出result.json中的sampled_bound并非严格下界；
not_rigorous_adjusted_diagnostic=sampled_bound+21*min(0,scanned residual)，
仍不是严格下界，因为搜索最小值不是全域保证。
若有理导出成功，A量化9位并加1e-6 I，再Fraction LDL精确验证；
target25.82只是待认证提案，父可按实际残差调整c。
