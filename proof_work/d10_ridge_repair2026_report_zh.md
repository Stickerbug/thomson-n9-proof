# d10 ridge repair：新接触锥方向的有限实验

三轮均返回数值模型，但全域残差仍有负点；不是严格证明、不是n9反例、也不是190维接触锥不可行证书。旧三个端点的凸包被P/Q组合排除后，本批优化全部190个B坐标、33个接触等式消元后的157个自由坐标，没有限制在原三个端点凸包。

## 模型与数据

域为完整Gram PSD∩[-1,.56]^3，没有竞争过滤。共同解析核的数值QR基和augsol/augZ从旧正确core重建；种子由旧混合originalA投影至共同N。190变量，接触rank33。B>=1e-7I、trace<=2000；内部9个HessR>=1e-6I，边界3个lambda>=1e-7且Tᵀ(HessR−lambda Hessg)T>=1e-6I，没有错误施加CGF两零点之间全HessianPSD。

初始structured mandatory1487，含P=(.56,.56,.56)、新Q、Q周围60点、CGF与交换接触点之间81个连接点及四尺度侧扰、full contact permutations在1e-4/1e-3/1e-2/.03/.05半径方向扰动以及旧三负谷。cuts距fullcontactset小于1e-4时剔除以减少浮点取消，中心由contact/pointjets控制；因此本批不是接触邻域覆盖证书。每轮负点永保，在mandatory基础上以随机/边界点补至active4000。

目标max eta−1e-10trace，0<=eta<=1e-3，点约束R>=eta*d²；Dred=D@augZ与bred=rhs−D@augsol预计算，以1/max(d²,1e-6)归一化。三轮eta均达到上限附近，微小越界仅数值容差。前两轮验证仍负，故第三轮继续修cuts而非最小trace。全部输入初始pool、curve、fullcontactset、N、sourceSHA和各轮cuts/x/B/A/c保存。

|轮次|eta|trace|minEigB|contact误差|原A已发现minR|CLARABEL秒|
|---|---:|---:|---:|---:|---:|---:|
|1|0.001000000018|65.133644|1.229249e-07|2.0907e-14|-0.000434094130861|24.913|
|2|0.001000000023|66.839435|1.055653e-07|2.0598e-14|-0.000207664144459|33.947|
|3|0.001000000029|73.046038|1.197228e-07|2.3419e-14|-1.94660096868e-06|28.156|

所有solver状态均optimal_inaccurate/AlmostSolved。build24.181秒，总163.539秒，三轮用完，没有第4轮。最后P_R=.042201936939855744、Q_R=9.918020276722395e-7为正；这正是离开旧凸包后解决旧P/Q阻碍的新证据，但只是数值结果。

## 原A验证与剩余负谷

每轮直接originalA recurrence扫描随机/mandatory点，并从Q与CGF连接curve[::10]出发SLSQP最小化原A残差与原A梯度；另外compiled DE找点后原A复核。原A局部搜索相对独立，不把compiledDE称独立搜索。验证秒数7.008/9.891/13.476；原A/compiled最大差8.48e-15/3.22e-15/4.30e-15。
- iteration0: [-0.3979711869695287, 0.5180659415505737, -0.9908630748053631], R=-0.0004340941308606655, Gram=1.5966603794596897e-17, 来源independent_originalA_local。
- iteration1: [-0.5181098310058934, -0.5181099851092424, 0.11914054668573175], R=-0.0002076641444586358, Gram=0.512893447273321, 来源independent_originalA_local。
- iteration2: [-0.7467121604140899, 0.1569399556149882, 0.3334596671928505], R=-1.9466009686802677e-06, Gram=0.22843985809796571, 来源compiled_DE_originalA_check。

最后负谷严格在Gram和box内部，朝原点1e-6内推后仍R=-1.9465901913012784e-06、Gram=0.22844147937291376。Fraction精确确认有限小数点的域成员性；A和R仍浮点，不是exact负证书。

结论：本批确实离开旧三凸包并修复P/Q，但有限cuts仍漏掉其他负谷。normalized训练eta>0不是全域下界；不能用optimal_inaccurate或随机正样本作为证明，也不能因有限三轮失败断言方法不可行。可将最终种子与剩余负点交父决策是否追加不同结构的约束生成或exact endpoint correction；本批未启动任何后继求解。

结果SHA256=6058c518eb208f5170efb88cf68b5a77c91313e6545009db489cff15d8eac6c9；最终A canonical JSON SHA256=04039fd4d5908da03066484b48319efd0db490fddf3393802ca716e60a691fb6。sourcehash.json冻结代码和依赖原文/哈希；audit.json保存三轮精确Gram、内推点、边界lambda/Hessian和误差。当前新jobs47/49/51已exit0收齐；旧fullGram867依旧状态不明，本批未触及或伪称停止。
