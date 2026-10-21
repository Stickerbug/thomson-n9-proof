# Candidate triple-moment blocks: exact low rank and sharp subspaces

Let H=1−r², h=√H, A=1−3r²/2, B=2r²−1, C=r²/2−1. The candidate consists of six prism vertices (r cos(2πj/3),r sin(2πj/3),±h) and three caps (cos((2j+1)π/3),sin((2j+1)π/3),0).

For arbitrary d,k with 0≤k≤d let m=d−k+1, i=0,...,m−1. Define Gk=Σall ordered triples Sk using the six-permutation averaged kernel from the SDP certificate. Fix anchor x and a transverse orthonormal frame e1,e2; set ζy=y·e1+i y·e2 and wi=Σy(x·y)^i ζy^k. The full anchored Yk sum is Re(w w*). Summing over all triples is unchanged by symmetrization.

## Prism anchor

Choose x=(r,0,h), e1=(h,0,−r), e2=(0,1,0). The nine pairs (inner product, transverse complex coordinate) are:

- own point: (1,0), once;
- other upper prism points: (A,−3rh/2 ± i√3r/2), once for each sign;
- same-longitude lower point: (B,2rh), once;
- other lower prism points: (C,rh/2 ± i√3r/2), once for each sign;
- opposite cap: (−r,−h), once;
- adjacent caps: (r/2,h/2 ± i√3/2), once for each sign.

Thus the prism feature pi is real. Let ε=k mod 2 and

    Tk(α,b)=Σ_{j=0}^{floor(k/2)} (−1)^j binom(k,2j) α^(k−2j) H^((k−2j−ε)/2) b^j.

This equals Re((αh+i√b)^k)/h^ε and contains only rational operations on r. Define p_hat_i=pi/h^ε. Then

    p_hat_i = δ(k=0)
      +2 A^i Tk(−3r/2,3r²/4)
      +B^i (2r)^k H^floor(k/2)
      +2 C^i Tk(r/2,3r²/4)
      +(−r)^i (−1)^k H^floor(k/2)
      +2 (r/2)^i Tk(1/2,3/4).

The δ(k=0) term is the own point, with the convention ζ^0=1 even at ζ=0. This formula holds at all positive r<1, independently of the stationary equation.

## Cap anchor

Choose x=(−1,0,0), e1=(0,1,0), e2=(0,0,1). The pairs are:

- own point: (1,0), once;
- other two caps: (−1/2,±√3/2);
- prism longitude zero: (−r,±ih);
- remaining four prism points: (r/2,±√3r/2 ± ih), all four sign combinations.

For odd k the cap feature ci=0 identically: the transverse multiset is invariant under ζ→−ζ at each inner product. For even k define

    Uk=Σ_{j=0}^{k/2} (−1)^j binom(k,2j) (3r²/4)^((k−2j)/2) H^j.

Then

    ci=δ(k=0)+2(−1/2)^i(3/4)^(k/2)
       +2(−r)^i(−1)^(k/2)H^(k/2)+4(r/2)^i Uk.

## All blocks and first three harmonic degrees

The D3h action has six prism anchors and three cap anchors. An ambient orthogonal transformation only rotates or conjugates the complex transverse coordinates; Re(w w*) is frame-invariant. Both representative feature vectors above are real. Consequently, exactly:

    Gk = 6 H^ε p_hat p_hat^T + 3 c c^T.

In particular rank(Gk)≤2 for even k, and ≤1 for odd k. These are bounds; further dependencies can occur for small m or at special r. Everything on the right belongs to Q(r), including odd k after factoring H.

For k=1, c=0 and

    p_hat_i=−3r A^i+2r B^i+r C^i−(−r)^i+(r/2)^i.

For k=2,

    p_i=(3r²/2)(3H−1)A^i+4r²H B^i
       +(r²/2)(H−3)C^i+H(−r)^i+(H−3)(r/2)^i/2,
    c_i=(3/2)(−1/2)^i−2H(−r)^i+(3r²−4H)(r/2)^i.

For k=3, c=0 and

    p_hat_i=(27r³/4)(1−H)A^i+8r³H B^i
       +(r³/4)(H−9)C^i−H(−r)^i+(H−9)(r/2)^i/4.

For k=0 these formulas reduce to the familiar prism and cap pair-moment vectors; G0=6p0p0^T+3c0c0^T.

## Constructing an exact sharp subspace

Since H>0, for PSD Ak the complementary-slackness equality <Ak,Gk>=0 is equivalent to Ak p_hat=0 and Ak c=0. Let Nk have columns spanning the kernel of the two-row matrix [p_hat^T;c^T]; then set Ak=Nk Bk Nk^T with Bk PSD. For odd k only one nonzero row is needed. Entries of Nk can be rational functions of r without square roots.

For odd k choose a pivot index a with p_hat_a≠0. For each j≠a use the column e_j−(p_hat_j/p_hat_a)e_a. For even k choose pivot indices a,b with Δ=p_hat_a c_b−p_hat_b c_a≠0. For each j outside {a,b} set v_j=1, and solve

    [p_hat_a p_hat_b; c_a c_b] [v_a;v_b]=[−p_hat_j;−c_j].

Thus v_a=(−p_hat_j c_b+p_hat_b c_j)/Δ and v_b=(−p_hat_a c_j+p_hat_j c_a)/Δ. Before interval evaluation, choose pivots numerically then certify the selected pivot/minor stays nonzero throughout the isolated r interval. Never infer exact dependence from an interval merely containing zero. If the two rows are exactly dependent, reduce rank algebraically first.

The executable helper `candidate_low_rank.py` implements these formulas over Fraction or compatible algebraic/interval scalar types, and an exact field nullspace routine. Its automatic zero comparisons are suitable for exact fields, not interval pivot decisions. Because interval multiplication loses identities, construct the rational-function formula first and validate pivots separately when using interval arithmetic.

## Validation

For d=8 and each k=0,...,8, at rational r=3/5 and a rational decimal approximation to the candidate r, the helper constructs exact rational feature rows and nullspaces; every nullspace vector is checked by exact dot products. Independently, the full 9³ ordered-triple sum is computed by the original kernel implementation and compared with the low-rank formula. This is a numerical implementation crosscheck; the finite coordinate substitution and symmetry argument above provide the mathematical proof.
