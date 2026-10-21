# 固定有理合同预条件扩大局部域

实际验证成功，11.97秒，12类均通过，7类严格扩大，未执行任何远区遍历。local_precondition2026_verify.py提供run(source_path,output_path,ctx=None)与--source/--output。所有旧local、prerequisites及coef保持原样。

数学：在真实接触中心的Hessian区间取精确有理中点矩阵，只用于选择固定有理矩阵。对此有理矩阵做Fraction LDL并取W=L^-1；W为单位下三角，det1，程序精确检查WL=I。实际通过判定始终是完整盒上真实Hessian的区间包络，经I384(W) H I384(W)^T后严格LDL正定。W不要求中点矩阵就是真实Hessian；有理W的可逆性与全盒合同后的正定性才是证明。I384(W)严格包含真实有理W，不把四舍五入W视为目标。

内部使用3×3 Hessian，边界使用真实lowerGram图函数的2×2 Hessian；边界expanded_u全盒R_u>0要求完全保留。真节点value/gradient精确为零仍依旧45contact/rank/W兼容定理，不靠pointinterval含0。

结果（标签按数值排序，数字是半宽）：
 AAA .001→.001；CBA .0001→.0003；CCA .001→.001；AFF .001→.001；
 GAF .0001→.0003；BFF .0001→.0003；GGB .0001→.0001；
 CFF .00001→.0001（10倍）；CGF .00001→.00003（3倍）；DDD .00001→.00001；
 DFF .0001→.001（10倍）；GDF .0001→.0003。

local_precondition2026_boxes.json保存每类完整原box、expanded_u（仅边界辅助证明）、固定有理W、变换前H与变换后H的严格区间、通过的LDL主元、旧半宽比较、失败更大半宽及sourcehash。LDL字段沿用原命名，但此处明确指合同后的H；变换前后矩阵另有独立命名。

全域local terminal仅能使用rows.box（及其子域）与Gram域交集，不可将expanded_u作扩大的终止box。完整区间合同正定给原H正定，故原局部Taylor/边界图证明逐字适用。当前结果不是全域证明。

程序为复用相同数学公式，在单进程调用期间临时替换导入模块的ldl回调，并用finally恢复；不改磁盘旧文件。该API不是线程安全接口，不应在同一Python进程中并行调用多个local验证；分别进程或顺序调用均可。不同worker进程无共享状态。
