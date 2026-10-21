# 25.82提案严格认证未通过

已运行实际新验证器antipodal_anchor_improve2026_exact_verify.py，job bash-922收齐，exit1。
精确重建Q0..Q4、F、D、R，全部Fraction LDL与h11全域minorant检查通过。
全域[-.63,.63]^2×[-1,.57]的48bit向外Bernstein触发
AssertionError: Depth guard reached; no certificate。
因此当前没有25.82严格下界，不能据此升级stationary pair exclusion到-.9938或-.995。
没有重跑SDP，也没有第二次严格验证。

失败真实记录与源SHA256在antipodal_anchor_improve2026_failed_verification.json。
该记录同时精确核对父提供的delta31/5000、theta14/125、dm441/500，
cost463632053/7813968750及正margin；但这些仅为25.82假设下的条件比较。
现有已认证25.80宽域下界及此前pair阈值保持原状。

深度保护可能由未发现的负残差或极接近零的残差触发；本轮没有提取未处理盒，
所以不能判断原因，更不能声称证书形式不可行。下一次诊断应先保存失败盒，
对该盒内点精确评价R，再决定是否降target；不能盲目提高节点预算。
