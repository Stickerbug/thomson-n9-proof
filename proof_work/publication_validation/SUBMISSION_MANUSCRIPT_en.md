# A certified computer-assisted proof candidate for the nine-point Thomson problem

**Status: proof candidate prepared for external review.**  The mathematical
argument, the exact interval certificates and a full replay from a rational seed
have been checked inside the originating research session.  The argument has
**not** been externally peer reviewed, has **not** been independently
reimplemented, and the final nine-point energy statement has **not** been
formalized.  Nothing in this note asserts that the nine-point Thomson problem
is solved in the published literature.  No global uniqueness of the minimizing
configuration is claimed.

*Author and affiliation to be supplied by the submitting authors.*

## Abstract

We present a self-contained, machine-checkable proof candidate that the minimal
Coulomb energy of nine distinct points on the unit sphere in $\mathbb{R}^3$ is
attained by a two-cap three-prism (D$_{3h}$) configuration, and equals
$E_* \approx 25.75998653126983156$.  The proof reduces the nine-point problem
to the nonnegativity of an explicit rational residual in three variables on the
physical ordered Gram domain, decomposes the total energy into a sum of local
residuals and a globally nonnegative perfect-square-type term, verifies the
contact (stationarity) equations at the true algebraic root, bounds the local
residuals by exact interval Hermite and Hessian certificates, and closes the
remaining three-variable domain by a fully expanded Bernstein subdivision tree
with 136,125 nodes and 68,063 leaves.  All arithmetic is exact integer/rational
interval arithmetic; an independently written pure-Python checker recomputes
every node from the exported tree and reproduces the closure with `pending = 0`
in 47 minutes 34 seconds.  The Lean 4 formalization currently covers the
candidate geometry, the energy identity, sphere membership, the existence,
uniqueness and strict global minimality of the family stationary point, the
isometry invariance and inner-product form of the energy, and the generic
domain-restricted coverage lemma; the final theorem remains unformalized.  We
describe precisely what is and is not certified, so that referees can attack
the weakest links first.

## 1. Introduction

The Thomson problem asks for the minimum of the Coulomb energy
$E(X)=\sum_{i<j}\|x_i-x_j\|^{-1}$ over configurations $X=(x_1,\dots,x_n)$ of
$n$ distinct points on the unit sphere $S^2\subset\mathbb{R}^3$.  For $n\le 7$
computer-assisted proofs of global minimality are available; for $n=8$ the
ground state is also understood.  For $n=9$ the published record (for example
the MathWorld entry) still lists the global minimizer as unknown.  The present
work is a proof candidate for $n=9$: it does not rely on numerical
optimization to assert nonnegativity, and every inequality used in the global
step is certified by exact rational interval arithmetic.

The candidate configuration has D$_{3h}$ symmetry: two parallel equilateral
triangles of radius $r$ at heights $\pm\sqrt{1-r^2}$, with matching azimuths,
together with three equatorial points between the top and bottom triangles.
Its one-parameter energy $E_D(r)$ is strictly convex on $(0,1)$ and tends to
$+\infty$ at both endpoints, so it has a unique stationary point $r_*$; the
candidate energy is $E_*=E_D(r_*)$.

## 2. Frozen statement

Let $h=\sqrt{1-r^2}$ and, for $k=0,1,2$,
$$
x_k^{\pm}=\bigl(r\cos(2\pi k/3),\,r\sin(2\pi k/3),\,\pm h\bigr),\qquad
c_k=\bigl(\cos((2k+1)\pi/3),\,\sin((2k+1)\pi/3),\,0\bigr).
$$
The nine points $x_0^+,x_1^+,x_2^+,x_0^-,x_1^-,x_2^-,c_0,c_1,c_2$ form the
candidate family.  Its energy is
$$
E_D(r)=\sqrt3+\frac{2\sqrt3}{r}+\frac{3}{2\sqrt{1-r^2}}
+\frac{6}{\sqrt{4-r^2}}+\frac{12}{\sqrt{2-r}}+\frac{6}{\sqrt{2+2r}} .
$$
The true root $r_*$ is isolated by exact interval enclosures and satisfies
$$
r_*\approx 0.71054833409295381132770417927279124376803,\qquad
E_*=E_D(r_*)\approx 25.75998653126983156407570227376049402864 .
$$
The frozen claim is: $E(X)\ge E_*$ for every configuration of nine distinct
points on $S^2$, with equality at the candidate.  The claim deliberately
excludes the classification of all equality cases and any statement of global
uniqueness of the minimizer.

## 3. Reduction to a three-variable inequality

Put $f(t)=(2-2t)^{-1/2}$.  A rational Legendre (positive-definite pair) test
shows that any configuration with $E(X)\le U$, where
$$
U=25.75998653126983156407570227376049402866>E_*,
$$
has all distinct inner products strictly below $14/25$.  Consequently it is
enough to prove the residual nonnegativity on the compact set
$$
D=\{(u,v,t): -1\le u\le v\le t\le 14/25,\; g(u,v,t)\ge0\},
\qquad g=1+2uvt-u^2-v^2-t^2 .
$$
Here $g\ge0$ is exactly the condition that three unit vectors with pairwise
inner products $u,v,t$ exist.  The asymmetric ordering is justified by
permutation symmetry of the residual.

The proof constructs a fully symmetric rational three-point kernel
$F(u,v,t)$ and sets
$$
d(t)=F(1,t,t),\qquad F_{111}=F(1,1,1),\qquad c=E_*/12+F_{111}/8,
$$
$$
R_f(u,v,t)=f(u)+f(v)+f(t)-7F(u,v,t)-d(u)-d(v)-d(t)-c .
$$
The global certificate proves $R_f\ge0$ on $D$ with **zero** slack reserved for
numerical error.

## 4. Global positive semidefinite decomposition and the energy identity

Define the polynomials
$$
Q_0=1,\quad Q_1=t-uv,\quad
Q_{k+1}=2(t-uv)Q_k-(1-u^2)(1-v^2)Q_{k-1}\quad(k\ge1),
$$
and, for $k=0,\dots,10$ and $0\le i,j\le 10-k$, put
$Y_{k,ij}(u,v,t)=u^iv^jQ_k(u,v,t)$.  Choose positive semidefinite matrices
$A_k$ and let $F$ be the six-permutation average of
$\sum_k\langle A_k,Y_k\rangle$.  After projecting the other points onto the
plane perpendicular to a fixed anchor point, $Q_k$ becomes
$\rho_j^k\rho_l^k\cos(k(\theta_j-\theta_l))$, so summing over the two remaining
indices produces a sum of two quadratic forms in real and imaginary moment
vectors.  Hence the fully ordered sum
$$
S_{729}(X)=\sum_{a,b,c=1}^9 F(x_a\cdot x_b,\,x_a\cdot x_c,\,x_b\cdot x_c)
$$
is nonnegative for every nine-point configuration.  In the actual certificate
$A_k=N_kB_kN_k^{\mathsf T}$; every nonempty block $B_k$ has strictly positive
exact interval LDL pivots, so positive semidefiniteness is not inferred from
floating-point eigenvalues.

Let $T$ be the sum of $F$ over the 84 unordered triples of distinct points and
$D=\sum_{a<b}d(x_a\cdot x_b)$.  Enumerating index coincidences gives
$S_{729}=6T+6D+9F_{111}$.  Since every edge lies in seven distinct triples,
$$
\frac17\sum_{84}R_f=E(X)-T-D-12c .
$$
Adding the two identities and inserting the definition of $c$ yields the exact
energy identity
$$
E(X)-E_*=\frac17\sum_{84}R_f+\frac16 S_{729}(X).
$$
The right-hand side is a sum of a nonnegative local residual and a nonnegative
global PSD term, so $E(X)\ge E_*$.  A separate exact rational enumeration over
all 729 ordered triples, keeping independent formal symbols for each pair and
triple, verifies the identity coefficient by coefficient.

## 5. Contact equations at the true root

At the candidate configuration only six distinct dot products occur:
$$
A=1-\tfrac32 r^2,\quad B=2r^2-1,\quad C=\tfrac12 r^2-1,\quad
D=-\tfrac12,\quad F=\tfrac r2,\quad G=-r .
$$
The candidate has twelve congruence classes of distinct-point triples.  The
stationarity conditions consist of twelve vanishing values, three gradient
conditions for each of nine interior triangle classes, and two tangential
derivative conditions for each of three Gram-boundary classes, for a total of
45 exact conditions.  They are not replaced by floating-point near-equalities.

An exact analytic common-nullspace computation produces 190 reduced variables.
The 45 rows satisfy 12 exact left relations; an independent geometric review
checks all 132 anchor moment components using the actual nine-point
coordinates.  The ten permutation relations together with the two summation
relations form a matrix $W$ whose nonzero minor is $-36r$.  The first eleven
right-hand sides vanish identically and the last is $7E_D'(r_*)=0$.  All
interval LU pivots of the $33\times33$ minor avoid zero, so the rank is exactly
33 and the selected 33 rows force all 45.  A rational seed is then corrected on
these 33 rows at the true root; the largest correction is about
$1.44\times10^{-12}$, after which strict LDL positivity is re-proved.

## 6. Hermite minorant and the twelve local classes

The local analysis uses the degree-27 Hermite interpolant $H$ of $f$ at the six
true candidate dot products and at eight additional rational nodes, matching
$f$ and $f'$.  The remainder is $f^{(28)}(\xi)/28!$ times a product of fourteen
squared factors, so $H\le f$ whenever the relevant intervals have
$f^{(28)}>0$.  Replacing the three $f$-terms in $R_f$ by $H$ gives a residual
$R_H\le R_f$ that still vanishes, with zero gradient, at the true contact
configuration.

Nine interior boxes are certified by exact interval Hessians, strictly
positive definite after a fixed rational congruence; vanishing value and
gradient then give nonnegativity on the whole box.  Three Gram-boundary boxes
use the graph
$$
u=b(v,t)=vt-\sqrt{(1-v^2)(1-t^2)} .
$$
On an expanded domain containing $b$ and the original $u$-interval, the
certificate proves $\partial_u R_H>0$ and positive definiteness of the Hessian
restricted to the graph; tangential vanishing then gives nonnegativity on the
graph, and monotonicity in $u$ extends it to the physical domain.  The DDD box
has half-width $10^{-7}$; the other boxes have half-widths between $10^{-5}$
and $10^{-3}$.

## 7. Global coverage of the three-variable domain

A dedicated analytic engine lower-bounds $f-d$ on each one-dimensional
subinterval.  For $x=l+(r-l)z$ it takes a degree-10 Taylor expansion of $f$ at
the left endpoint with strictly rounded-down coefficients, bounds the
degree-20 Bernstein coefficients of $d$ from above, subtracts the positive part
of all coefficients of degree at least 11, and obtains a degree-10 polynomial
lower bound for $f-d$.  The true $F$ differs from its symmetric rational center
polynomial by at most $\varepsilon_F$, and the kernel term together with the
three diagonal terms absorbs $10\varepsilon_F$; $c$ is taken at its upper
endpoint.  A tensor Bernstein box is certified nonnegative when all degree-10
coefficients are nonnegative, or when $R_f-\lambda g\ge0$ for some rational
$\lambda\ge0$ (the multiplier need not equal the true normal derivative).  A
box may also be discarded when $g<0$, when it is disjoint from the ordering
cone, or when it lies in an already certified local box.  Subdivision creates
two subboxes and all rounding directions are fixed.

The accepted run has the following transcript:

| quantity | value |
|---|---:|
| target error $\delta$ | 0 |
| visited nodes | 136,125 |
| split nodes | 68,062 |
| terminal leaves | 68,063 |
| direct positive | 27,392 |
| Gram excluded | 26,797 |
| ordering excluded | 3,278 |
| local-box covered | 78 |
| boundary-multiplier positive | 10,518 |
| maximal depth | 75 |
| pending boxes | **0** |

A second, independent replay starts from the original rational seed, recomputes
the pair exclusion, the 350-bit root enclosure, the Hermite data, the true-root
contact correction, the PSD blocks, all coefficients and all local boxes, and
then reruns the full tree from the complete root domain.  The root-input hash
and the terminal classification transcript agree with the first run.  The
shared arithmetic implementation means this is reproducibility, not an
independent proof checker; the independent checker of Section 8 is a separate
implementation.

## 8. Exact arithmetic, independent checking, and negative tests

All certificates are produced with 384-bit integer outward interval arithmetic
and, in the hot loop, with a range-guarded signed 128-bit native backend.  The
96-bit production runs trigger no range skip and no depth or stack guard.  A
closure is reported only when the pending stack is empty; intermediate results
with a nonempty pending frontier are never treated as a proof.

The exported tree (`sharp_root_tree.jsonl`, 33 MB) records every split and leaf.
An independently written checker, using only the Python standard library
`int` and `Fraction` types and importing none of the original Bernstein,
interval, C or signed-128 code, recomputes all 136,125 nodes in 154 shards.  It
reproduces 68,063 leaves with `pending = 0` in 47 minutes 34 seconds and binds
the result to the SHA-256 digest of the root inputs.  Fifty directed negative
and failure-propagation tests cover false coverage, wrong signs, forged local
boxes, wrong digests and worker failures that must block a PASS.  Additional
component tests independently rebuild the candidate parameter and energy
bounds, the pair reduction, the PSD blocks (10 nonempty blocks, 50 strictly
positive LDL pivots), the analytic kernel on $\mathbb{Q}[r]$, the 33-dimensional
contact solution (190 coordinates), the 756 $F$-coefficients and $c,E_*,F_{111}$
enclosures, the Hermite data (28 $H$ coefficients, 807 $R_H$ coefficients), the
pure-algebra Hermite factor $G=1-(2-2t)H^2=WQ$ with $W=\prod(t-x_i)^2$ and all
28 Bernstein coefficients of $Q$ strictly positive, and the twelve local
arithmetic classes.

## 9. Formal verification status

A Lean 4.34.1 project pinned to Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612` accompanies the paper.  The modules
that compile are:

* `Statement.lean` — the frozen specification only, with no theorem and no
  axiom;
* `Family.lean` — the explicit candidate coordinates, 36 distance-reciprocal
  lemmas, and `energy_candidate : energy (candidate r) = familyEnergy r`
  for $0<r<1$;
* `Derivative.lean` — the explicit derivative `familyEnergyDeriv` and
  `hasDerivAt_familyEnergy`, the derivative of the family energy;
* `Stationary.lean` — the endpoint signs `familyEnergyDeriv(1/2) < 0` and
  `familyEnergyDeriv(9/10) > 0`, continuity of `familyEnergyDeriv` on
  $[1/2,9/10]$, the intermediate-value step, and
  `exists_stationary_point` (existence of a stationary point in $(0,1)$;
  uniqueness is in `SecondDerivative.lean`);
* `SecondDerivative.lean` — the explicit second derivative
  `familyEnergyDeriv2`, `hasDerivAt_familyEnergyDeriv`, positivity of $E_D''$
  on $(0,1)$, continuity on $(0,1)$, and the Rolle-theorem uniqueness
  `stationary_point_unique` / `exists_unique_stationary_point` (the family
  stationary point is unique);
* `Minimum.lean` — strict monotonicity of `familyEnergyDeriv` on $(0,1)$,
  `familyEnergy_strictAntiOn` / `familyEnergy_strictMonoOn`, the strict global
  minimum `familyEnergy_min`, `exists_unique_familyEnergy_min`, and
  `energy_candidate_min` (the candidate energies inherit the strict minimum), and
  `exists_candidate_with_family_min`, which bundles sphere membership, the
  stationary condition and strict family minimality into one existence statement;
  the interval forms `familyEnergy_strictAntiOn_Ioo` and
  `familyEnergy_strictMonoOn_Ioo` state that the energy strictly decreases on
  $(0,r_*)$ and strictly increases on $(r_*,1)$;
* `StrictConvex.lean` — strict convexity of the family energy on $(0,1)$
  (`strictConvexOn_familyEnergy`, via `strictConvexOn_of_deriv2_pos`);
* `EnergyContinuity.lean` — continuity of the nine-point Coulomb energy on
  injective configurations (`continuousAt_energy_of_injective`,
  `continuousOn_energy_injective`);
* `Applications.lean` — invariance of the energy under a linear isometry
  (`energy_comp_isometry`), closure of `SphereConfig` under isometries, the
  crude unconditional bound `energy_ge_eighteen : 18 ≤ energy x`, the
  inner-product form `energy_eq_inner` (via `norm_sub_sq_eq_inner` and
  `norm_sub_eq_sqrt_inner`), the derivative of the energy along the candidate
  curve `hasDerivAt_energy_candidate`, and `sphereConfig_nonempty`;
* `ContactInner.lean` — the six pairwise inner products of the candidate family:
  `A = 1 - 3r²/2`, `B = 2r² - 1`, `C = r²/2 - 1`, `D = -1/2`, `F = r/2`,
  `G = -r`, matching the contact-equation constants;
* `EnergyBounds.lean` — the diameter bound `dist_le_two`, the pair-reduction inequality
  `inv_dist_le_energy` (each reciprocal distance is bounded by the total energy),
  its consequence `dist_ge_inv_energy` (if the energy is at most $U$ then every
  distance is at least $U^{-1}$), and `energy_candidate_strict_min` /
  `exists_candidate_strict_energy_min`, which transfer the strict family minimum
  to the energies of the actual candidate configurations on the sphere;
* `EnergyValue.lean` — a fully rational certified upper bound: the six square-root
  terms at `r = 7/10` are bounded by rationals, giving `familyEnergy (7/10) < 26`
  and, via strict minimality at `r*`, `familyEnergy r* < 26` and
  `energy (candidate r*) < 26`;
* `EnergyForms.lean` — the energy is homogeneous of degree -1 (`energy_smul`: scaling all
  points by `c > 0` multiplies the energy by `c⁻¹`), the scaling derivative
  `hasDerivAt_energy_scale` (`t ↦ energy ((1+t) • x)` has derivative `-energy x` at zero),
  and the inner-product form `energy_eq_sum_rpow` expressing the energy as
  `∑ (2 - 2⟨x_i, x_j⟩)^(-1/2)`, matching the `f(t) = (2-2t)^(-1/2)` pair potential of the
  reduction;
* `PairDeriv.lean` — derivatives along straight paths through a point `x ≠ 0`:
  the affine path `t ↦ x + t v` and its squared distance (`hasDerivAt_affine`,
  `hasDerivAt_norm_sq_affine`), the norm (`hasDerivAt_norm_affine`, via
  `HasDerivAt.norm_sq` and `HasDerivAt.sqrt`) and the inverse distance
  (`hasDerivAt_inv_norm_affine`: derivative `-⟨x,v⟩/‖x‖³`), the pairwise
  derivative gateway for writing the energy gradient as a pair sum and
  connecting it to the 45 contact equations;
* `EnergyGradient.lean` — the gradient `gradAt x i = ∑_{j≠i} ‖x_i-x_j‖⁻³ (x_j-x_i)` and its
  pair-sum form: `hasDerivAt_pair_inv_dist` (derivative of one pair term), `inner_gradAt`
  (`⟨v, gradAt x i⟩` equals the pair sum), translation invariance `energy_translate`, and
  `hasDerivAt_energy_update` (pair-sum derivative of the energy when only point `i` moves),
  the combinatorial identity `sum_Ioi_ite_eq`, `pairSum_eq_inner_gradAt`, and the gradient form
  `hasDerivAt_energy_update_gradAt`
  (`t ↦ energy (update x i (x_i + t v))` has derivative `⟨v, gradAt x i⟩` at zero),
  so that the 45 contact equations are exactly the vanishing of this derivative at the candidate
  configuration and the generating directions;
- `EnergyPath.lean` (`hasDerivAt_pair_inv_dist_path`, `sum_Iio_swap`,
  `sum_univ_ite_eq_sum_erase`, `sum_erase_eq_sum_Iio_add_Ioi`,
  `hasDerivAt_energy_path`): when all nine points move along straight paths,
  `t ↦ energy (fun i => x i + t • v i)` has derivative `∑ i, ⟨v i, gradAt x i⟩` at zero,
  so stationarity is exactly the vanishing of the derivative in every multi-point direction.
- `ThreePointBound.lean` (`dsum`, `Rs`, `dsum_Rs`, `dsum_H`, `gramOK_inner`, `Rk`, `sum4_swap`, `three_point_identity`): the reduced-kernel combinatorics and the exact Bachoc–Valentín three-point identity, adapted with attribution from the same N=7 development; `matDot_moment_nonneg_sos` and `three_point_bound_sos` then give the three-point bound in witnessed SOS form, where the PSD matrices are supplied as explicit sums of rank-one squares `∑ s, vecMulVec (v s) (v s)`; the abstract `PosSemidef` moment lemma is still deferred.  A separate `TreeSemantics.lean` formalizes the leaf-certificate/coverage logic: axis-aligned boxes, bisection splits, tensor-Bernstein certificates with nonnegative coefficients, exclusion leaves for points outside the physical domain, and the theorem that any finite such tree proves `0 ≤ R` on the physical domain (`covered_sound`). The numeric tree and rational coefficients remain inputs checked outside Lean.  The capstone `covered_sound_root` specialises this to the certificate's root box `[-1, 14/25]³`, so a checked tree rooted there yields `0 ≤ R` on the whole physical domain.  `PSDSemantics.lean` records the other certificate interface: `reduced_quadform_nonneg` turns a PSD block `B` into a nonnegative quadratic form for `N B Nᵀ`, and `reduced_sum_quadform_nonneg` assembles finitely many such blocks, matching the `A_k = N_k B_k N_kᵀ` decomposition.  The numeric PSD data again remain outside Lean. `Interval.lean` and `IntervalTensor.lean` start the numeric-certificate route: intervals with rational endpoints (`RatInterval`), soundness lemmas for `add`, `neg`, `sub`, `scale`, `mulNonneg` and `powNonneg`, and the leaf-checking principle `tensor_nonneg_of_coeff_intervals` — coefficients enclosed by rational intervals with nonnegative lower bounds give a nonnegative Bernstein tensor on the unit cube. `IntervalMul.lean` adds the mixed-sign product `mulMixed` (an arbitrary interval times a nonnegative one, with three sign branches) and its soundness theorem, the operation needed to multiply a signed coefficient enclosure by a nonnegative Bernstein-basis enclosure. `IntervalEval.lean` closes the atomic evaluator steps: `bernInterval` encloses the Bernstein basis function `C(n,i) z^i (1-z)^(n-i)` for all `z` in a subinterval of `[0,1]` (`mem_bernInterval`, with nonnegative lower endpoint `bernInterval_lo_nonneg`), and `mem_mulMixed3` encloses a signed coefficient times three nonnegative basis enclosures — exactly one term of a ternary Bernstein tensor — and `sumIntervals`/`mem_sumIntervals` enclose finite sums of such terms. The certificate data themselves remain outside Lean.
- `ThreePoint.lean` (`quad_Y3_nonneg`, `bv_positivity`): the Bachoc–Vallentin three-point positivity on `S²` for arbitrary block size and `k`, adapted with attribution from the N=7 Lean formalization `huwngtran/thomson-n7-lean` (commit `25f2fa5`). This is the reusable core of the `S₇₂₉ ≥ 0` step; the general-PSD pairing lemma (`matDot_moment_nonneg`) is deferred because its Mathlib dependency closure (positive-operator decomposition) is not available in the pinned cache.
- `Minimizer.lean` (`exists_global_minimizer`, `exists_global_minimizer_lt_26`): the energy is continuous on the compact feasible shell (sphere plus the 36 distance lower bounds), so a global minimizer exists in `SphereConfig 9`, and it has energy `< 26`. This supplies the existence half of the frozen statement; the global lower bound itself is supplied by the certified tree.
- `FinalAssembly.lean` (`thomsonNineClaim_iff_global_lower_bound`,
  `thomsonNineClaim_of_pointwise`): the frozen claim is proved *equivalent* to the
  single statement “there is a stationary point whose family energy is a global
  lower bound on `SphereConfig 9`”. Candidate geometry, distinctness, the energy
  identity and stationary-point uniqueness are discharged inside this equivalence,
  so the only remaining unformalized input is the global lower bound itself.
- `GradientZero.lean` (`gradient_zero_iff_directional`, `hasDerivAt_energy_path_zero`):
  the gradient vanishes at every point iff every multi-point directional sum vanishes,
- `EnergyOptimality.lean` (`inner_le_of_energy_le`, `local_min_gradient_zero`,
  `isLocalMin_gradient_zero`, `two_mul_energy`, `energy_perm`, `sphereConfig_perm`): an energy upper bound `U` forces every inner product
  `≤ 1 - (2U²)⁻¹`, and local minimality (along paths or in the ambient space) forces
  `gradAt x = 0`.
  closing the equivalence `stationary_iff_gradient_zero : (∀ v, HasDerivAt … 0 0) ↔ ∀ i, gradAt x i = 0` between stationarity and `gradAt = 0`.
* `GramBound.lean` — the Gram constraint `0 ≤ 1+2uvt-u^2-v^2-t^2` of the domain
  `D` is proved to be a consequence of the unit-norm constraints (Cauchy–Schwarz
  on the projections onto one of the three unit vectors), and pairwise inner
  products of unit vectors lie in `[-1,1]`;
* `DomainChamber.lean` — the three pairwise inner products of any unit triple can
  be sorted into the ordered chamber `-1 ≤ u ≤ v ≤ t ≤ 1` while preserving the Gram
  constraint (`exists_ordered_gram_constraint_of_mem`); the `14/25` upper bound is
  separate pair-reduction input, not claimed here;
* `DistanceValues.lean` — the exact six distance values of the candidate family
  ($\sqrt3\,r$, $2\sqrt{1-r^2}$, $\sqrt{4-r^2}$, $\sqrt3$, $\sqrt{2-r}$,
  $\sqrt{2+2r}$) obtained from the reciprocal lemmas, and the exact
  distance/inner-product relations for the candidate configurations;
* `CandidateMem.lean` — unit norms, injectivity of the nine points, and
  `candidate_mem_sphere`;
* `CoverageSoundness.lean` and `DomainCoverage.lean` — generic finite binary
  tree induction, including the domain-restricted version required by the
  ordered/Gram leaf exclusions (proved without extra axioms);
* `LeafSemantics.lean`, `ReducedPSD.lean`, `TaylorTen.lean`,
  `HermiteFactor.lean`, `TransverseCoordinates.lean` — supporting algebraic
  and analytic lemmas.

`#print axioms` on these theorems reports only `propext`, `Classical.choice`
and `Quot.sound`; there is no `sorryAx`.  The `Family`, `CandidateMem`,
`DomainCoverage`, `CoverageSoundness`, `Derivative`, `Stationary`,
`SecondDerivative`, `Minimum`, `StrictConvex`, `EnergyContinuity`,
`Applications`, `ContactInner`, `EnergyBounds`, `DistanceValues`, `GramBound`,
`EnergyValue`, `EnergyForms`, `PairDeriv`, `EnergyGradient`, `EnergyPath`,
`GradientZero`, `EnergyOptimality`, `EnergySymmetry`, `Minimizer`, `ThreePoint`, `ThreePointBound`,
`FinalAssembly` and `DomainChamber` modules have also been replayed with the second kernel
`leanchecker` (exit 0).

The final theorem `ThomsonNineClaim` is **not** proved.  `FinalAssembly.lean`
proves it is equivalent to the single global lower bound
`∃ r, 0 < r ∧ r < 1 ∧ HasDerivAt familyEnergy 0 r ∧ ∀ x ∈ SphereConfig 9,
familyEnergy r ≤ energy x`; all the other conjuncts are discharged.  What remains
unformalized is the passage from the arithmetic certificates to that bound: the
45 contact equations, the PSD/local certificate semantics, and the instantiation
of the coverage lemma for the 68,063 leaf certificates.  The
family stationary point is formalized as existing, unique, and the unique
strict global minimum of the family energy on $(0,1)$
(`exists_unique_familyEnergy_min`).

## 10. Trust boundary and reproducibility

A referee should treat the following objects as the load-bearing evidence.

1. The exported coverage tree and the independent pure-Python checker.  The
   checker is included in the review bundle together with its tests and the
   full recorded result; the 154-shard run is archived.
2. The exact contact-geometry review, the PSD blocks, the Hermite factor and
   the twelve local certificates, each with its own independent arithmetic
   recheck.
3. The final linkage checker, which verifies the energy identity over all 729
   ordered triples with exact rational arithmetic.
4. The Lean modules listed above, which certify the candidate geometry and the
   coverage logic but **not** the final theorem.

The main logical bridges still requiring external scrutiny are: (i) the
derivation of the 45 contact equations and the rank argument; (ii) the
semantics of each arithmetic certificate as a real inequality; (iii) the
transition from the Hermite minorant to the local boundary graphs; and (iv) the
instantiation of the coverage lemma on the physical domain.  A defect in any of
these bridges would invalidate the proof candidate, although it would not by
itself disprove the optimality of the D$_{3h}$ candidate; that would require an
explicit nine-point configuration whose rigorously certified energy is below
the lower bound for $E_*$.

Reproduction instructions, file hashes and the full record are contained in the
review bundle `THOMSON_N9_REVIEW_BUNDLE.zip` and in
`proof_work/publication_validation/`.  The authors welcome independent
reimplementations, especially of the signed-128 Bernstein engine and of the
contact rank argument.

## References

1. J. J. Thomson, *On the structure of the atom*, Philos. Mag. **7** (1904),
   237–265.
2. H. Cohn and A. Kumar, *Universally optimal distribution of points on
   spheres*, J. Amer. Math. Soc. **20** (2007), 99–148.
3. H. Cohn and J. Woo, *Three-point bounds for energy minimization*, J. Amer.
   Math. Soc. **25** (2012), 939–958.
4. R. E. Schwartz, *The five-electron case of Thomson's problem*,
   Exp. Math. **22** (2013), 157–186.
5. E. W. Weisstein, *Thomson Problem*, MathWorld (accessed 2026), which lists
   the nine-point case as unknown.
6. H.-W. Tran, *A Lean formalization of the N=7 Thomson problem*, GitHub
   repository `huwngtran/thomson-n7-lean`, commit `25f2fa5`.  Our
   `ThreePoint.lean` adapts its Bachoc–Vallentin three-point positivity section
   with attribution; the N=7 development is not imported as a dependency.

*Bibliographic details and additional references are to be completed by the
submitting authors.*
