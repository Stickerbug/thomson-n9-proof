# 三点证书的缺陷恒等式与竞争构型限制

对象：单位 S² 上九点，E=Σpairs f(t)，f(t)=(2−2t)^(-1/2)。
使用 three_point_d4_exact_25_745.json 中已全域验证的有理 h,F,c。
设 B=12c−(3/2)F(1,1,1)=5149/200，d(t)=F(1,t,t)，
R(u,v,t)=h(u)+h(v)+h(t)−7F(u,v,t)−d(u)−d(v)−d(t)−c。
所有Gram可行三角上 R≥0，且 f−h≥0；核正性给 Σall ordered triples F≥0。

## 精确恒等式

令 T=Σunordered distinct triples F，D=Σunordered pairs d。
84个无序三元组中每条边出现7次，因此

    Σunordered triples R = 7 Σpairs h −7T−7D−84c。

包括重复指标的完整有序三元组满足

    Σall ordered triples F = 6T+6D+9F(1,1,1)。

消去T,D得到：

    E−B = Σpairs (f−h) + (1/7)Σunordered triples R
          + (1/6)Σall ordered triples F。

右侧三项均非负。最后一项进一步分解为每个核块的PSD配对之和。
注意单个F可以为负；非负的是完整有序和以及每个块的完整PSD配对。

## 对所有可能推翻候选的构型的必要约束

取已认证候选能量上包络
U=25.75998653126983156407570227376049402866，δ=U−5149/200。
若 E≤U，则：

- Σpairs(f−h)≤δ，故每条边 f(t)−h(t)≤δ；
- Σunordered triples R≤7δ，故每个实际三角 R≤7δ；
- 0≤Σall ordered triples F≤6δ；
- 每个核块的完整PSD配对均≤6δ。

其中δ≈0.01498653126983156，7δ≈0.104905718888821，6δ≈0.0899191876189894。
全部精确阈值可直接用上面的十进制有理U和B定义，无需相信浮点近似。

这使证明工作可以由一个三角上的宽松下界转向九点兼容性：
对边与三角Gram变量使用上述必要限制，连同9×9 Gram矩阵PSD、rank≤3、diag=1。
若能严格排除候选局部邻域外所有兼容Gram矩阵，再接已认证的局部唯一性，
即可闭合全局证明。这里尚未执行完整排除，也未断言这些约束足够。
当前文档提供代数推论及下一步搜索约束，不是新的最优性证明。
