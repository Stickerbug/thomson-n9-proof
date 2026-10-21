# A global analytic N=9 bound with an explicit integrality gap

This note contains a derived global bound, not a proof of the conjectured optimum. The energy is E=Σ_{i<j}(2−2t_ij)^(−1/2), t_ij=x_i·x_j, x_i∈S². All configurations are allowed; no D3h assumption occurs.

## 1. Hermite polynomial and exact constants

Set s=√6, a=(−1+s)/5, b=(−1−s)/5, Δ=a−b=2s/5, f(t)=(2−2t)^(−1/2). Let p be the unique cubic with p(a)=f(a),p'(a)=f'(a),p(b)=f(b),p'(b)=f'(b). Express p=Σ_{k=0}³ p_k P_k in the normalized Legendre basis. Exact formulas suitable for direct verification follow. Write v=s/5, y=t+1/5, F_a=f(a),F_b=f(b), g_a=f'(a),g_b=f'(b), and

C=(g_a−g_b)/(4v),
D=((g_a+g_b)/2−(F_a−F_b)/(2v))/(2v²),
B=(F_a−F_b)/(2v)−Dv²,
A=(F_a+F_b)/2−Cv².

Then p=A+By+Cy²+Dy³. Its monomial coefficients are c0=A+B/5+C/25+D/125, c1=B+2C/5+3D/25, c2=C+3D/5, c3=D. Finally p0=c0+c2/3, p1=c1+3c3/5, p2=2c2/3,p3=2c3/5.

Numerically p_k≈(0.8059134077934681,0.4636468012409988,0.2084481347170135,0.06219138573463149). The accompanying integer-only outward interval script certifies all four coefficients positive. These numerical values are not the proof data.

Define

B0=(81p0−9p(1))/2,
κ=(f(−1)−p(−1))/q(−1)², q(t)=(t−a)(t−b)=t²+2t/5−1/5.

Here q(−1)=2/5 and κ≈0.07172902790718>0. An alternative exact expression for B0 is

B0=(9/2)[(4+s/4)f(a)+(4−s/4)f(b)]≈25.70859423294796.

The alternative expression follows from a two-node quadrature rule with the diagonal node 1; equivalently verify the identity on monomials of degrees zero through three.

## 2. Global remainder inequality

For t∈[−1,1), let R(t)=f(t)−p(t). The Hermite interpolation identity is

R(t)=q(t)² f[a,a,b,b,t],

where square brackets denote divided differences with repeated nodes interpreted by derivatives. The divided difference f[a,a,b,b,t] is nondecreasing in t. To see this, for u>v its difference is (u−v) f[a,a,b,b,u,v]; the latter divided difference is positive because f^(5)>0 throughout the convex hull of the nodes. Therefore

R(t)≥κq(t)²≥0.

This includes t=a,b by continuity. Collisions t=1 have infinite energy and can be discarded. This proof is stronger than merely using the uniform minimum of f^(4)/4!, which gives only 105/12288.

For S_k=Σ_{i,j}P_k(t_ij), the addition theorem gives S_k≥0. Summing the interpolating polynomial yields the exact defect identity

E−B0=(1/2)Σ_{k=1}³p_k S_k+Σ_{i<j}R(t_ij).

Consequently, if z=Σ_i x_i and D0=Σ_{i<j}δ_ij² is defined below,

E−B0≥α||z||²+βD0,

with α=p1/2>0, β=κΔ²/4=6κ/25>0.

## 3. Integer neighbor counts and graph parity

Round every t_ij to a nearest node a or b, breaking midpoint ties consistently for the unordered pair. Put δ_ij=t_ij−rounded(t_ij). Let k_i be the number of a-rounded neighbors of point i (0≤k_i≤8). Since the other root is always at least Δ/2 away, q(t_ij)²≥(Δ²/4)δ_ij², which proves the preceding βD0 term.

Let X have row vectors x_i, and e_i=Σ_{j≠i}δ_ij. Then

e_i=x_i·z−1−8b−k_iΔ.

Set η=(2√6−3)/5. The nearest integer to (−1−8b)/Δ=4+√6/4 is 5; its discrepancy is η. The next nearest is 4, with discrepancy 3/5; every other integer discrepancy is larger than 3/5. The a-rounded pairs form a simple undirected graph. Its nine vertex degrees cannot all equal 5 because their sum would be 45, an odd number. Hence

Σ_i(−1−8b−k_iΔ)²≥G:=8η²+9/25.

This is an inequality for every configuration, irrespective of graph realizability of any particular degree sequence.

By Cauchy–Schwarz, ||e||²≤8Σ_iΣ_{j≠i}δ_ij²=16D0. Also ||Xz||≤||X||_F||z||=3||z||. Since the vector of the nine discrepancies is e−Xz,

√G≤4√D0+3||z||.

Weighted Cauchy–Schwarz gives

(4√D0+3||z||)²≤(βD0+α||z||²)(16/β+9/α).

Therefore the following explicit GLOBAL bound holds:

E≥B0+G/(16/β+9/α).

The accompanying exact interval computation certifies

E > 25.71015.

The closed-form value is approximately 25.7101578424586. This improves the Hermite/tight-design bound by approximately 0.00156360951068, but still lies approximately 0.0498286888112 below the D3h candidate energy 25.7599865312698. No claim of literature novelty is made.

## 4. Tensor interpretation and limitations

Let M=Σ_i x_i x_iᵀ and T=Σ_i x_i⊗x_i⊗x_i. Then

S1=||z||²,
S2=(3/2)||M−3I||_F²,
S3=(5/2)||T0||_F²,
T0=T−(1/5)sym(z⊗I),

where sym(z⊗I)_abc=z_a δ_bc+z_b δ_ac+z_c δ_ab. These are exact equalities; the trace of T is z and ||sym(z⊗I)||²=15||z||². The defect identity controls dipole, quadrupole, and trace-free octupole simultaneously.

At the candidate the dipole vanishes, but the quadrupole and octupole do not. Thus the cubic lower bound cannot be sharp at the candidate. More generally, any tight two-point LP certificate must set p_k=0 whenever the candidate has S_k>0. Finite-degree strict positivity of candidate S_k is being certified independently by the parent session; this note does not assert such positivity at every degree.

The fractional neighbor counts 4±√6/4 explain why the base tight-design quadrature cannot be geometrically attained. Integrality corrects this defect but is far too small to resolve the conjecture. A three-/four-point approach must capture correlated row distributions, triangle compatibility and higher Gram-rank information, or else a domain-specific certificate must use substantially stronger geometry. Establishing positivity or a high numerical bound is not sufficient: an exact global inequality at the candidate energy plus equality rigidity is still missing. No argument here forces a minimizer to have D3h symmetry.

A possible modest improvement is to retain the S2 term and replace ||Xz||≤3||z|| by ||Xz||≤sqrt(3+sqrt(2S2/3))||z||. This improves constants but cannot plausibly close the remaining ~0.05 gap alone.
