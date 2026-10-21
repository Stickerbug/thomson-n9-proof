# 真实驻点上的十阶接触核与半正定性认证

## 已证结论与边界

存在一个精确定义在真实驻点r*上的十阶核F，使其满足全部45个候选接触值、内部梯度及边界切向等式，且所有原始核块Ak半正定。十个非空reduced块Bk甚至严格正定。

这不是全局最优性证书：尚未在本结果中证明竞争域内R非负、接触点Hessian或边界法向乘子条件。使用的是原始Coulomb f的接触方程；若改用在六节点值与导数一致的minorant，接触等式仍相同。

源数值模型明确取sharp_contact_refinement2026_results.json的best_solution，迭代2，数值trace约660、minB eigenvalue约2.344e−6；没有使用后续batch2。

## 精确对象的定义

Nk(r)由features两行的固定RREF构造。在Q(r)中同步验证所有零模式，且所有必要除法主元在已认证root区间内严格非零。
将Nk乘常数有理矩阵Tk，使Ntilde=Nk Tk接近父数值QR基。Tk由数值最小二乘提出，再转成明确有理数；其所有条目保存在证书中。种子对称矩阵的190个条目也转成精确十进制有理数。

浮点步骤只提出这些有理常数及33行列选择，不参与后续任何通过/失败判定。

令C为保存的33列，J为33行，x0为保存的190个有理seed。精确定义真实r*处

    x_rest=x0_rest，
    x_C=x0_C+Δ，
    M_JC(r*) Δ=b_J(r*)−M_J(r*)x0。

这33×33系统的所有区间LU主元均严格避开零，因此确实唯一地定义了Δ。
本对象不是将r*替换为有理近似所得的核；其系数由真实驻点及上述方程精确定义。

## 全45行为什么精确成立

先前严格定理给出十二个左关系W，rankW=12，且对于任意Nk支撑的核列，WM=0。常数矩阵Tk不破坏Gk Ntilde=0，因此新变换后的全部190列同样满足W Mtilde=0。
本次新区间33×33子式非零，证明新算子rank≥33；由W给出的上界，又有rank=33，故ImMtilde=kerW。
真实驻点满足Wb=0，因为唯一非恒零的兼容条件是7E'(r*)=0。因此b属于该像空间，所选33行确定的校正必满足全部45行。

Tk无须另行假定可逆：本次新区间子式已证明所需rank33，而Ntilde=Nk Tk仍在真实共同零空间中。下述A半正定也不依赖Tk可逆。因此本结果没有声称所有Tk的可逆性另经认证。

区间计算覆盖整个root区间以包络校正，但一般r≠r*时45行不相容；“全部45行精确成立”只在真实r*成立。

## 校正量与严格正定检查

采用384位整数dyadic向外区间。每个矩阵元素通过Qk及解析梯度递推重建，Coulomb右端由整数平方根外包络构造。
区间Gaussian消元与回代给出33个Δ的严格包络，脚本整数断言

    max|Δ_i| < 5.358×10^(-12)。

展示近似最大值约5.3571703565×10^(-12)。没有使用原数值特征值作为PSD证明。
对每个校正后的reduced块Bk做区间LDL分解，全部10块的每一个对角主元都有严格正的整数下界。因此真实Bk严格正定。于是

    Ak=Ntilde_k Bk Ntilde_kᵀ ≥0，

k10的零维reduced块对应Ak=0。由构造还有〈Ak,Gk〉=0，因此候选互补等号精确成立。

## 文件和复算

- d10_exact_contact_psd_seed1_v1.py：发现后量化、认证以及exact-only复核入口。
- d10_exact_contact_psd_seed1_v1.json：全部有理Tk、190seed、行列索引、精确解定义、Δ包络、LU和LDL证据。
- d10_exact_contact_psd_seed1_replay.json：独立新进程复跑，exit0，9.20秒。
- d10_exact_contact_psd_seed1_exact_reverified.json：仅读取证书有理数据复核，exit0，8.66秒；不读源数值模型、不运行数值最小二乘或QR。

exact-only命令，从workspace根执行并使用尚不存在的输出名：

    PYTHONPATH=proof_work/python_deps OPENBLAS_NUM_THREADS=1 python3 \
      proof_work/d10_exact_contact_psd_seed1_v1.py \
      --certificate proof_work/d10_exact_contact_psd_seed1_v1.json \
      --output proof_work/d10_exact_contact_psd_seed1_new_exact_replay.json

复核入口重建全部190列与右端，重新消元、回代、验证严格校正量界、重做全部LDL，并精确比较保存的LU主元、Δ包络、解包络及PSD_LDL。它仍共享底层dyadic算术程序，因此独立实现审查仍有价值。

本轮全部计算任务已收集，无活跃任务；没有改动父模型或已有全局证书。
