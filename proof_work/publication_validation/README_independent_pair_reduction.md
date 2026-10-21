# Independent rational pair reduction

This new computation does not modify any frozen export artifact. The checker imports only Python standard-library modules and reads the saved rational Legendre coefficients. It does not import a proof_work module, trust the old status/counts, or reuse the legacy three-term recurrence or iterative de Casteljau splitter.

`independent_pair_reduction.py` reconstructs each Legendre polynomial by the closed factorial formula

P_n(t) = 2^(-n) sum_{k=0}^{floor(n/2)} (-1)^k (2n-2k)!/[k!(n-k)!(n-2k)!] t^(n-2k).

All calculations use exact Fraction and integers. Bernstein coefficients are obtained directly by affine power expansion followed by b_i=sum_{k<=i} c_k binom(i,k)/binom(n,k). Midpoint subdivision uses closed binomial sums: left_i=2^(-i)sum_{j<=i}binom(i,j)b_j and right_i=2^(-(n-i))sum_{j<=n-i}binom(n-i,j)b_(i+j). There is no legacy polynomial code dependency.

The exact fixed candidate upper rational is

U = 25.75998653126983156407570227376049402866
  = 1287999326563491578203785113688024701433/50000000000000000000000000000000000000.

Let p(t)=sum_l a_l P_l(t). The checker verifies every a_l>=0 for l>=1, reconstructs B=36a_0-(9/2)sum_{l>=1}a_l and gap=U-B>0, and checks the certificate's U/B/gap against these mathematical values. It requires exact delta=0 and threshold=14/25; nonsharp or changed domain parameters fail.

The saved `independent_pair_reduction_trees.json` contains the complete root polynomials, root Bernstein coefficients, and every split and leaf of both small coverage trees. Paths determine children, each exact rational interval is explicit, each leaf saves its exact Bernstein minimum. A second traversal recomputes all bounds and child boxes from the roots and rejects missing children, duplicate or unreachable nodes, invalid minima, pending nodes, and incomplete coverage. It establishes:

1. 1-(2-2t)p(t)^2 >= 0 on [-1,1].
2. 1-(2-2t)(p(t)+gap)^2 > 0 on [14/25,1].

For t<1, f(t)=(2-2t)^(-1/2)>0. Statement 1 implies |p(t)|<=f(t), hence f(t)-p(t)>=0 without any sign assumption on p. Statement 2 implies |p(t)+gap|<f(t), hence f(t)-p(t)>gap on [14/25,1). The endpoint t=1 is harmless in the polynomial check; a distinct finite-energy pair of unit vectors has t<1.

For nine distinct unit vectors let t_ij=x_i dot x_j, E=sum_{i<j}f(t_ij), and M_l=sum_{i,j}P_l(t_ij). Legendre's addition theorem gives M_l>=0. Since P_l(1)=1, direct separation of diagonal terms gives

sum_{i<j}p(t_ij) = 36a_0 -(9/2)sum_{l>=1}a_l +(1/2)sum_{l>=1}a_l M_l.

Consequently the exact defect identity is

E-B = sum_{i<j}(f(t_ij)-p(t_ij)) +(1/2)sum_{l>=1}a_l M_l,

and therefore E >= B + sum over the 36 pairs of (f-p). All 36 pair defects are nonnegative. If any pair has t_ij>=14/25, its defect is strictly greater than gap, so E>B+gap=U. Thus every distinct configuration with E<=U has all pair dots strictly less than 14/25.

`independent_pair_reduction_result.json` records exact constants, reconstructed monomial p, full-tree counts, code/source bindings, elapsed time and negative-test outcomes. Negative tests break a Legendre LP coefficient, corrupt p to produce an exact negative endpoint in the minorant square condition, supply a wrong positive gap, remove a coverage leaf, insert a pending node, set nonzero delta, and change the threshold. Rejections rely on mathematical inequalities/identities/coverage, not SHA mismatch. The SHA values are provenance only.

This is an independent exact computation layer. Legendre's addition theorem and the existence of an admissible nine-point candidate with energy strictly below the fixed rational U remain explicit mathematical premises. This checker does not prove either premise, the frozen coefficient/local/PSD claims, or a final formal nine-point theorem. No Lean installation is required or performed. Existing output files are preserved by exclusive creation.
