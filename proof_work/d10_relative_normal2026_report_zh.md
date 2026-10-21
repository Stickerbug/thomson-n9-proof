# 相对PSD修复加入法向约束：数值候选达精确适配门槛

本批无SDP，只一次最小相对范数解析active-set投影即达到有限验证阈值，耗时26.471秒。完整Gram域[-1,.56]^3扫描10000随机+2000boundary+旧mandatory5478，compiled最低64点用originalA复核，并原A局部搜索；发现最低R=−6.439293542825908e-15，满足父规定−5e-12移交门槛。这是数值候选，随机/local验证不是全域非负证明。

改进是直接将Q_R>=1e-9、P_R>=1e-7、3个boundary λ>=1e-7作为5个线性约束加入相对PSD投影；不再追逐nearDDD负谷。G各行按2norm归一，枚举active subsets，原始G@y−need以longdouble核验。相对PSD映射δB=LYLᵀ，||Y_k||₂<=||y||₂。contactC@T的数值rank33，nullerror=1.5826611862928982e-14。

||y||=0.0016333097804944485，||dx||=0.01155847528994311，minEigB=1.4223392405921467e-06，contact error=1.2878587085651816e-14，interiorHmin=0.00030305980054677086。Q_R=1.000004634654772e-09，P_R=1.7860065363306532e-05，原A/compiled maxerror=2.3037127760972e-15。

boundary jets=[{"index": 3, "lambda": 9.609136624212705e-05, "tangent_error": 2.7911771198888083e-15, "corrected_eigs": [0.002423844753860855, 0.1796962630621305]}, {"index": 4, "lambda": 0.004404262447341381, "tangent_error": 4.6587150892915715e-15, "corrected_eigs": [0.0046386117441809035, 0.12209324061934568]}, {"index": 7, "lambda": 9.999999969448028e-08, "tangent_error": 9.74409155414345e-15, "corrected_eigs": [0.02041180812915484, 0.020411808129212294]}]。

原始未归一化线性余量=[1.431679974104388e-25, 1.776006536721125e-05, 9.599136624132426e-05, 0.004404162447341241, -7.612784973335285e-20]；active subset=[0, 4]（顺序Q,P,3lambda）。所有浮点微小负余量仍需exact adapter处理，尤其boundarylambda hard target附近不能把float等号当严格。

完整原basis A/N/B/x/c位于results.json solution与history[0].solution；T/Zrel/N/indices/seed保存，rawscan_0.npz含全部点/compiledR/verifiedpoints/originalAR；audit.json冻结driver依赖原文和哈希。results SHA256=368ec491d7c66398ac1cb7639e24fb24059af586fca73980a9f36bfdc177a2fb；finalA canonicalJSONSHA=9295d9568275ef75706a394e56a7d3be3b56c25a3ad560efd315a7b356bcad64。

父代理已即时收到阈值达成通知，可调用既有9c exact adapter；本agent未自行exactify，未启第2patch或任何SDP。严格LB仍25.7599205，严格全局证明尚未完成。
