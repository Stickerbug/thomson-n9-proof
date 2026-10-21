# 近sharp核的PSD约束接触投影

## 一次限时求解

此实验是父线程新授权，区别于此前欧氏投影。旧39条解析contactjets rank32，用x=sol+Zz参数化，保证数值接触条件。不加任何训练cuts，不加tracecap。仅Bk PSD，目标||x−xbest||²+1e−9 trace，CLARABEL time_limit60，实际仅求解一次。

结果status optimal，求解2.8019秒，全部重建与验证总24.0393秒。contact最大误差6.5781e−15，Bk最小特征值+1.2256e−11，总trace21.88572059，距离原x为.000717042。故数值上存在靠近原模型、满足PSD与接触条件的修复；这不是精确存在证明。

## 残差损失

用run2全部11632cuts评估，最差R=−.00040895741418 at(.56,.56,.56)，Gramdet .410432>0；原始design独立重算差4.0e−15。独立continuous validator最差仅−4.40604e−5，位于Gram边界近(-.99839633,-.02831667,-.02831670)。随机/DE检查没有发现更坏的cube corner，说明今后数值验证应显式加入所有可行cube corners和u/v/t=.56面的优化。此前exact全盒认证不受此诊断漏洞影响。

最近PSD接触修复比原模型全域残差明显更坏，不能从小参数距离推断全域证书仍接近。此次没有迭代训练或再次SDP。

实际脚本psd_project_nonsharp_d10_contactjets_v1.py，完整JSON同名；包含修复x/B/A/c、全部特征值、原cuts最差与continuous诊断。bash339与独立核查bash343均exit0，输出已收集。

当前结论：欧氏投影失败不能说明接触PSD空间不可行。直接PSD投影数值成功，但损坏残差，因此还未接上sharp全局证书。数值失败亦不能据以宣称sharp形式不存在。

## 附：非sharp最佳核有理导出误差核查

父发现batch2新A高目标exact覆盖慢，授权仅评估保存cuts，不新DE。compare_nonsharp_batch2_rational_export_v1.py把保存rational A转float，并用原design和真实f/cstar比较原best x重建核，全部11632cuts，耗时2.4247秒。

x重建A与保存浮点A完全相同。A最大变化1.00044528e−10；cstar变化1.37543754e−10。残差最大差仅2.79973567e−9 at(-.3728,.56,.56)，远小于1e−8。原最差R=−2.200534479e−6，有理A最差R=−2.201859165e−6，同点(-.620965367101,-.620964266914,.368355264920)。没有发现exportbasis错误或有理化造成明显高幂放大。此检查不覆盖保存cuts之外的区域，因此不能排除未检测违例，亦不能推断高目标exact必然通过。

完整诊断JSON compare_nonsharp_batch2_rational_export_v1.json。bash348 exit0已收集。所有本任务job339/343/348均完成，无活跃job。

## 模型归属澄清：角点(.56,.56,.56)

所有模型用真实f和各自cstar，原design直接比较：
- 原batch2 best_iteration1：R=+4.4397872931e−5；
- 其有理export：R=+4.4396048365e−5；
- PSD接触修复模型：R=−.000408957414184；
- 欧氏接触投影模型：R=−.000341838936434。

因此负角点只属于接触修复模型，不属于原batch2best。原best全cuts最差−2.2e−6与本角点正残差不矛盾。有理export使用target25.75995的c及h27时，本角点R=+4.7440305439e−5。负角点不能解释原best有理证书全域Bernstein覆盖耗时。完整比较four_models_cube_corner_comparison_v1.json；bash353 exit0输出已收集。
