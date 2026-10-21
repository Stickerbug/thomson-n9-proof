# T2 两外点场：有限 I384 尝试、覆盖核验及 Bernstein 微测

本轮没有证明 T2 上的 `W(q,r) >= 1/25000`，没有得到新的 Thomson 下界。唯一四维区间运行已按时间预算停止，状态为 `budget_exhausted`，2600 个未决盒完整保留。本文只记录这一轮已取得的数据及其可检查性；没有重复运行 Horner，也没有追加 SDP。

## 固定对象与所需不等式

T2 是固定的有理三角内积

```
u = .3464802927157662
v = .3464805531965182
t = .34648072472904085
```

这里十进制解释为 exact Fraction，不是区间邻域，也不是候选构型的精确代数根。取三个单位锚点 `a_i` 实现该 Gram 矩阵，对任意两个外点 `q,r` 定义

```
phi(q) = sum_{i<j in {1,2,3}} Rold(a_i·a_j, a_i·q, a_j·q)
psi(q,r) = sum_{i=1}^3 Rold(a_i·q, a_i·r, q·r)
W(q,r) = (phi(q)+phi(r))/5 + psi(q,r).
```

待证域是单位 `q,r` 且六个锚点外点内积与 `q·r` 均不超过 `14/25`。旧全局 residual 证书保证这些实际几何三角上的每个 `Rold >= 0`，因而 `phi,psi >= 0`。不要求区间输入盒中的每一个非几何三元组也满足 Gram 条件。

若有六个外点，则恰有

```
sum_{15 external pairs} W = sum_6 phi + sum_45 one-anchor residuals.
```

另 20 个全外点 residual 非负，可以丢去。当前 T2 的精确预算 K 记录在结果文件，约为 `.00045090043558526405`。若能严格证明 `m=1/25000=.00004`，就有 `15m=.0006 > K`，超过预算约 `.00014909956441473595`。本轮尚未完成这个前提。

## 单轮四维运行

每个球面使用两张图

```
Q_s(a,b) = (2a, 2b, s(1-a²-b²))/(1+a²+b²),  s in {+1,-1},
(a,b) in [-1,1]^2.
```

任意单位点都有逆参数 `(a,b)=(q_x,q_y)/(1+|q_z|)`，且 `a²+b²<=1`，因此四个 square-product 根覆盖全部点对。整个方形还重复覆盖部分球面，这会增加计算量，不会遗漏点。记录的体积是参数盒体积，不是球面面积。

全部几何区间使用 I384 outward 整数运算；分母为正，平方跨 0 时使用紧的非负下界。单位恒等式给出 dot 在 `[-1,1]`。在证明七个 cap 条件蕴含结论时，可将每个 dot interval 的上端截至 `ceil_I384(14/25)`；只有下端严格超过该 cap 上端时才排除盒。

旧 807 项精确多项式采用 nested sparse Horner。三项固定锚点边长后的 phi 使用精确代入得到的 2D 多项式，psi 使用 3D 多项式。每个实际 residual 下界取 `max(0, interval_lower)`，依赖旧几何 residual 非负证书。整数 W 下界是

```
floor((phiQ_lower + phiR_lower)/5) + sum_3 psi_lower,
```

尺度为 `2^384`；只有它达到 `ceil(2^384/25000)` 才可能通过。浮点数没有进入排除或接受判据。

唯一成功运行 `bash-763` 的数据：

| 项目 | 值 |
|---|---:|
| 内部时间预算 | 59 秒（预留启动失败开销） |
| 实测准备及区间循环 | 59.002085927990265 秒 |
| 节点上限 | 5000 |
| 已处理节点 | 2660 |
| split | 2628 |
| cap 排除 | 32 |
| W 接受 | 0 |
| 完整树节点数 | 5260 |
| pending | 2600 |
| 最大深度 | 10 |

每个根体积是 16。根 0 排除体积 1、pending 体积 15；其余三根各 pending 体积 16。整个参数覆盖体积 64，未决体积 63。根 0 仅排除其自身体积的 1/16；不能将其写成全域已排除 1/16。

pending 数量 root0/1/2/3 分别为 `960/616/512/512`；深度 9 有 1432 盒，深度 10 有 1168 盒。所有已计算 W 下界均为 0。根盒最大单 residual 区间宽度约 `12226.674315660486`；代表深度 9 盒坐标宽度为 `(.25,.5,.5,.5)`，最大 dot 宽度约 `1.1062013`、单 residual 宽度约 `1002.4447`。这些宽度远大于目标，不构成目标不等式为假的证据。

## 独立只读审核

`external_pair_interval2026_audit.py` 不调用 Horner 求值，也不生长树。它重新核验：

- 全部 5260 个 node 的编号、父子关系、分裂轴、中点及两个 child 盒；
- 四个完整根、每根精确前沿体积，以及 pending 文件与 trace 的一致性；
- 全部 32 个 cap 排除，通过独立重建 I384 锚点、图和 dot 下界逐一重算；
- model/report/source 依赖 hash，以及没有任何 W 接受叶。

审核通过，状态 `partial_coverage_and_cap_rejections_verified`。它没有声称闭合 2600 个 pending，也没有重跑旧的 202923 节点全局 residual 证书。

运行后按父线程建议，当前 `external_pair_interval2026_bounded.py` 增加禁止 Python `-O` 的 guard。原运行源码逐字保存在 `external_pair_interval2026_runtime_source.py`：

```
run source SHA256: 23136e8948ca6fa8126ef30b1944cf0f751e55df30c1c09eff732ce0e7846579
current SHA256:    0abc64ef37c5936a4bd0975a3b24a06e37f8d4e3718e95369950c4eed678198e
```

只有这一 guard 差异；没有为它重跑数值尝试。

## 后续单独授权的 20 盒微测

父线程另授权最多 30 秒、最多 20 个已保存 node 的 Bernstein range microbenchmark；它没有延伸四维证明树。

Rold 的逐变量次数为 `(27,27,27)`，3D tensor 为 `28^3=21952` 系数。微测构造 48-bit 下/上整数 Bernstein 张量，用精确 Fraction transform 初始化，midpoint de Casteljau 每次向外取整。已检查初始整数绝对值 `<2^60`，后续凸平均仍在这些整数极值内，每次求和 `<2^61`，所以本微测的 int64 运算有明确安全余量。

phi 先代入固定边长，建立三个 2D tensor；三个 psi 共享一个 3D tensor。查询按参数 interval product 选择交叠 dyadic cells，min lower/max upper 给出 R 的包含区间；单次 query 最多 4 叶、10 次 split，并缓存路径。所有筛选逻辑仍保留 query 的完整覆盖。没有新建 4D 高次张量。

`bash-777` 成功：总 `6.393085937015712` 秒，其中 root 构造 `4.864865104027558` 秒；20 个盒、180 queries、1168 次命中或新建的 query splits、482 个 cached cells。

| 保存盒 | Horner 最大 R 宽度 | Bernstein 最大 R 宽度 | 新 W 下界 |
|---|---:|---:|---:|
| 四个根 | 12226.6743 | 159.7727 | 0 |
| 2044，深度 9 | 1002.4447 | 2.9801 | 0 |
| 2046，深度 9 | 1398.1805 | 2.9450 | 0 |
| 2659，深度 10 | 704.1203 | 2.9801 | 3.2219108306e-6 |
| 2657，深度 10 | 781.5917 | 5.2678 | 2.6407994227e-6 |

其余数据均在 microbenchmark JSON。宽度明显改进，但 20 盒仍全部未达到 `.00004`。这些局部比较不修改原树或 pending 的状态。

## 下一实现的数学判断

直接 3D Bernstein oracle 能消除 Horner 的高次单项式抵消，但将九个 R 分开查询仍丢失共享 dot 的相关性。当前浅盒宽度还是过大，盲目重跑相同 BFS 不合适。

父线程已独立接手更有价值的二维 unary screening，本线程不重复实现。因为 `psi>=0` 且 `phi(r)>=0`，任何严格覆盖盒若满足 `phi(q)>=5m=.0002`，它与任意可行 r 的 W 都达到 m。应先在两张半球图上完整证明或排除高 phi 区域，保留低 phi 盒的 union，再只处理 low×low。直接对整个 phi 的齐次化 polynomial 做 2D Bernstein 可保留三项之间的抵消；逐 R oracle 做不到这一点。还可严格排除 `a²+b²>1` 的 chart 盒，因为两半球 disk 已覆盖球面。

3D oracle 适合作为该低井乘积中的补充：lazy 路径 cache，而非预先铺满每轴深度 6–8 的整树。一次 3D tensor split 每个 bound 约需要 `28²*(1+...+27)=296352` 次整数加法；lower+upper 加倍。单个 3D cell 的两张 int64 tensor 需要 `2*28^3*8=351232` bytes，因此大量离线 cell 很快占满内存。固定边长 phi 的 2D tensor 仅 `2*28²*8=12544` bytes，应优先使用。后续 cache 宜按实际 arg-box 的公共前缀复用，并设置内存上限。

如果 low×low 仍被独立 residual 的下界损失卡住，可以先求各 R 的 3D derivative Bernstein bounds，再用 chart 的 rational Jacobian/Hessian，对 W 先合并梯度再做 centered Taylor 下界。这样近极小点的盒损失可由一阶绝对值之和降至二阶；它是后续设计建议，尚未实施或证明性能。

## 现存文件与重放

本说明及下列文件都位于 `/home/dsh/Thomson Problem/proof_work`，没有编辑父报告、manifest 或旧模型：

- `external_pair_interval2026_bounded.py`：当前带禁止 -O guard 的单轮脚本。
- `external_pair_interval2026_runtime_source.py`：本次实际运行源码快照。
- `external_pair_interval2026_result.json`：预算状态、数值、依赖 hash、根覆盖。
- `external_pair_interval2026_trace.json`：5260 节点的完整动作与分裂数据。
- `external_pair_interval2026_pending.json`：2600 个未决盒。
- `external_pair_interval2026_audit.py` / `external_pair_interval2026_audit.json`：独立只读树与排除核验。
- `external_pair_interval2026_bernstein_microbenchmark.py` / `.json` / `.log`：20 盒比较。
- `external_pair_interval2026_bounded_repaired.log`：唯一成功四维运行日志。

只读重放：

```bash
PYTHONPATH=proof_work:proof_work/python_deps OPENBLAS_NUM_THREADS=1 \
python3 proof_work/external_pair_interval2026_audit.py
```

无需重跑 Horner。若将来需要独立重现数值尝试，可导入脚本后将 `PREFIX` 改成新的名称；默认拒绝覆盖已有 result/trace/pending。

所有相关后台 job 都已收齐：`bash-742` exit2（backend 文件创建失败，未打开源码）；`bash-753` exit1（解析格式失败，未进入区间节点）；`bash-763` exit0（唯一成功四维运行）；`bash-777` exit0（新授权短微测）。前两次失败已如实保留日志，数值运行采用 59 秒限制以预留启动失败开销。归档时没有活跃后台 job。本轮没有新增严格能量下界，也没有完成 T2 邻域或 Thomson 全局 sharp 证明。

## 父线程二维筛选的独立静审与覆盖核验

随后父线程自行完成 `t2_unary_screen2026.py` 与 `t2_unary_screen2026_result.json`，要求本线程只做静审和保存叶的核验，不重复运行其 source。本线程创建的 `external_pair_interval2026_unary_audit.py` 独立核对了 source/result 依赖 hash、Q128 锚点与真单位锚点的 I384 enclosure、扰动上界，以及旧 R 模型与已闭合 report 的 hash 绑定。

静审未发现不等式方向错误：

- 每个锚点坐标向下舍入误差 `<1/Q`，anchor-dot 误差 `<=3/Q`；总次数 `<=27` 与 `(1+3/Q)^26<2` 给出三项 phi 的扰动 `<=18*sum|c|(j+k)/Q<EPS=1e-25`。
- 齐次化多项式是各项 `c_jk N_i^j N_j^k D^(27-j-k)` 之和。`D=1+a²+b²>0`，逐 Bernstein 系数减去 `ceil((TAU+EPS)*upper(D^27))` 保持向下的包含关系。
- cap 多项式使用 `14/25+3/Q`，方向保守；严格排除 `a²+b²>1` 的盒也正确，因为两半球 disk 已覆盖 S²。
- 任何 phi_high 点与任意另一个可行点组成的 W 都满足 `W>=phi_high/5>=1/25000`，条件是旧几何 residual 非负证书有效。

两 chart 的终端矩形映射到各自 128×128 dyadic 网格后，每个格子计数均恰为 1，总 16384 格。正 chart 有 183 high、449 low、1 excluded；负 chart 有 222 high、445 low、4 excluded；没有 budget_pending。两图合计保留 894 个 low 矩形，总参数面积 `447/2048`，相对两张 square charts 的面积 8 为 `447/16384`。low×low 参数面积比例 `199809/268435456`，约较原参数积域缩小 1343.46 倍。这是参数面积，不是球面面积，也不是概率或全局证明完成比例。

`external_pair_interval2026_unary_audit.json` 记录完整结果及仍存的限制：本静审/覆盖审核没有重新构造每个 degree54 Bernstein polynomial，也不验证 low 盒的 W 下界。

父线程又从保存的 br 最小值恢复更强的单点下界。对每个 low 叶，记 `b=brmin/2^64<0`，`Dmin=1+min_box a²+min_box b²`。因为齐次化差 G 满足 `G>=b` 且 `D>=Dmin>0`，有

```
phi_true >= TAU + EPS - anchor_error + G/D^27
         >= TAU + b/D^27
         >= TAU + b/Dmin^27.
```

所以 `max(0,TAU+b/Dmin^27)` 是有效下界。负数 b 的分母方向在此处至关重要；若 b>0，不能套 Dmin，应改用 Dmax 或直接使用 phi>=TAU。当前所有保存 low 叶均 b<0。

本线程从原 result 独立以 Fraction 恢复 894 个下界，再 binary search 精确计数，与父线程一致：136 个下界为 0，最大下界约 `.00019995488311334796`；799236 个有序 low 盒对中，303673 个满足两个 phi 下界之和 `>=1/5000`，从而无需 psi 即有 W>=1/25000，剩余 495563 对未决。

该计数依赖保存的 Bernstein 最小值是正确的 lower-bound datum；不等同于重建全部 degree54 数组的独立证明重放。数据及可重放脚本为 `external_pair_interval2026_unary_phi_pair_audit.json` 和 `external_pair_interval2026_unary_phi_pair_audit.py`。单独重放：

```bash
PYTHONPATH=proof_work:proof_work/python_deps OPENBLAS_NUM_THREADS=1 \
python3 proof_work/external_pair_interval2026_unary_audit.py
PYTHONPATH=proof_work:proof_work/python_deps OPENBLAS_NUM_THREADS=1 \
python3 proof_work/external_pair_interval2026_unary_phi_pair_audit.py
```

独立运行的 degree54 构造属于父线程；本线程没有重新执行该 source、没有新增证明搜索。对将来的独立重放，建议父证书显式增加 `certify_all_degree.py` 与旧 residual 闭合 report 的 hash；本次审核已额外核对这一 model/report 绑定。

