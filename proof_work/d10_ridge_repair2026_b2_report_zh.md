# 第二批 d10 ridge repair：联动 eta 的接触jets

本批继承前批finalA及全部mandatory、所有已保存validation点（包括最后DE负谷），改用eta<=1e-4与max eta−1e-11trace；三轮均不mintrace。所有内部HessR>=max(1e-6,2eta)I；边界lambda>=1e-7，corrected切向Hess>=1e-6I且>=2eta(TᵀT)。PSD B>=1e-7I，trace<=2000。

每轮新增内部Hessian特征方向±、半径1e-4/1e-3/.01、全permutation；边界同理沿corrected tangent eigenvectors，再Newton修正最大Gramgradient坐标，最后1e-13向原点内推。初始新eigencuts=909，initialmandatory2435，finalmandatory=4740。每轮active5000，若mandatory超限实现会全保留；本批没有裁掉新点。

每轮compiled扫描60000random+6000boundary+mandatory，最低64用originalA recurrence核验；从Q/最低10/CGFcurve/旧发现点原A局部搜索，24秒alarm限制实际运行，可能未完成所有seed。DE只编译找点、原A复核，不称独立。所有scan点和compiledR、最低64originalR保存scan_0.npz至scan_2.npz，各轮local/DE点和原A误差保存在results。

|轮次|原A已发现minR|interior linked margin|boundary linked margin|contact误差|验证秒|
|---|---:|---:|---:|---:|---:|
|1|-0.000255325639529|0.00073502649|0.003724695|8.89424e-15|24.043|
|2|-0.000226177498395|0.00073723116|0.0041824969|1.08524e-14|24.615|
|3|-4.33421899475e-05|0.0011465704|0.002970763|1.59039e-14|19.256|

全部CLARABEL为Solved/optimal，core solve47.733/41.452/36.745秒，含建模wall54.775/50.290/60.830秒，总283.986秒，满足每轮solver55秒与总300秒。最后A仍有真域内负谷，故不能认证；本批目标和验证集改变，不把跨批minR当单调序列。

iteration0负点：{"point": [-0.20483924193661296, 0.4748598376317295, 0.4748598352952389], "originalA_R": -0.00025532563952945786, "Gram_exact": "25917374456505757003186765946649442161347346119/62500000000000000000000000000000000000000000000", "Gram": 0.4146779913040921, "valid": true}

iteration1负点：{"point": [0.24721998733392125, 0.56, 0.24722001359269233], "originalA_R": -0.00022617749839459744, "Gram_exact": "3163081994032056709226157336502513/5000000000000000000000000000000000", "Gram": 0.6326163988064113, "valid": true}

iteration2负点：{"point": [0.08596819714271833, 0.08596820100419908, 0.08596820115548003], "originalA_R": -4.334218994750394e-05, "Gram_exact": "122387388405105934912451108728515464757903169506523/125000000000000000000000000000000000000000000000000", "Gram": 0.9790991072408475, "valid": true}

Fraction仅精确确认有限小数点Gram/box域成员；R和A仍float。不是n9反例或接触锥不可行证明。所有必要jet联动余量为正只控制接触邻域二阶必要性，不意味着全域R>=eta dist²。

results SHA256=063583eeed364ee6981bf573a8c6eef691601dd0a813734e5dfc3489413a5d26；finalA canonicalJSON SHA256=aac6cd1bc39693fede1f6c89f45fdec2682465056e9525c85ddf2171887fe45f。driver.py、sourcehash.json冻结来源；不改父报告/manifest/旧core。三轮已完成，未启动后继批次，严格全局证明仍开放。
