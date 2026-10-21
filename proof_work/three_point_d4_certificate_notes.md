# Four-degree three-point SDP rational certificate experiment

This note documents a rigorous certification procedure. The accompanying JSON `global.status` determines whether the whole-domain claim has been proved; `budget_exhausted` does not prove a global lower bound.

## Exact model

Sphere S², N=9, E=Σ_{i<j}(2−2xi·xj)^−1/2. Set Q0=1, Q1=t−uv, Q{k+1}=2(t−uv)Qk−(1−u²)(1−v²)Q{k−1}. Set Yk,ij=u^i v^j Qk, 0≤i,j≤4−k, and Sk equal to its six coordinate permutation average. For symmetric positive semidefinite rational Ak, let F=Σtrace(Ak Sk), d(s)=F(1,s,s).

For every finite spherical configuration, Σall ordered triples Sk is positive semidefinite: before symmetrization fix the anchor and use the positive-definite Chebyshev harmonic kernel on its transverse circle. Polynomial extension handles degenerate projections. Symmetrizing does not change the full ordered sum.

Exactly, Σdistinct ordered triples F=Σall F−3Σordered distinct pairs d−9F111. Therefore the polynomial inequality R=h(u)+h(v)+h(t)−7F−d(u)−d(v)−d(t)−c≥0 on the Gram domain implies E≥12c−3F111/2, whenever h(s)≤(2−2s)^−1/2 on [−1,1).

## Rationalization and PSD

The numerical d4 matrices are projected to PSD using the eigendecomposition only to generate a proposal. Their entries are symmetrized, rounded to ten decimal places and interpreted as exact decimal rationals; 10^−7 times the identity is added. Fraction-based LDL decomposition then checks each pivot strictly positive. The numerical eigendecomposition is not trusted by the proof. The output stores every rational matrix entry and every exact positive LDL pivot.

The degree11 Hermite proposal is expanded to monomials, rounded to twelve decimal places and interpreted as exact decimal rationals. Subtract 10^−7 from its constant term. Bernstein subdivision proves h>0 and 1−(2−2s)h²≥0 on [−1,1], which proves h≤Coulomb. The proof does not rely on numerical agreement at the original interpolation nodes.

Choose exact rational c=(target+3F111/2)/12. Thus the claimed energy bound is exactly target if the remaining R≥0 verification terminates.

## Outward tensor Bernstein verification

Construct R and g=1+2uvt−u²−v²−t² as rational polynomials. Transform x=2z−1. For degree vector n, monomial z^a contributes product_i binom(bi,ai)/binom(ni,ai) to tensor Bernstein coefficient b. These transformations use Fraction arithmetic. The resulting residual coefficients are rounded DOWN to integers with denominator 2^70, and the Gram coefficients UP to the same denominator.

Midpoint de Casteljau subdivision uses lower rounded averages for R and upper rounded averages for g. Thus the coefficient enclosures remain outward after arbitrary subdivision depth; all subsequent arithmetic is integer. A box is certified when every lower R coefficient is nonnegative. A box is excluded when every upper g coefficient is negative. Additionally, permutation symmetry allows restriction to u≤v≤t: exclude any box with lower(u)>upper(v) or lower(v)>upper(t). The code checks all six exact permutations of F before invoking this reduction; the h sum and d sum are manifestly symmetric.

The subdivision chooses a coordinate with the fewest prior splits, so each infinite branch has shrinking side lengths. A finite empty pending stack certifies the full Gram domain. Budget exhaustion is recorded explicitly, with counts, depth and pending boxes; it is not converted into a bound.

## Reproduction

Run with PYTHONPATH=proof_work/python_deps:

    python3 proof_work/certify_three_point_d4.py --target 25.733 --budget 300000 --seconds 240

The program stores all exact model data in `three_point_d4_exact_25_733.json`. Check `global.status`, independently of this explanatory note. This experiment is intended to improve a global lower bound; even successful certification of 25.733 would remain below the candidate energy 25.7599865312698 and would not establish optimality.

## Completed certificate: 25.733

The full-domain run completed with `status=certified`, 26,381 visited nodes, 6,453 residual-positive leaves, 6,738 Gram-negative or symmetry-excluded leaves, zero pending boxes, and maximum depth 33. Subdivision took 31.87 seconds. The minorant polynomial required 11 visited univariate Bernstein nodes. A separate reread of the saved JSON rechecked all exact LDL pivots and the identity 12c−3F111/2=25733/1000.

Thus, subject to the stated three-point positivity argument and executable certificate checker, the experiment establishes the unconditional global bound E≥25.733 for every nine-point configuration on the unit sphere. No upper inner-product restriction or numerical assumption on a minimizing configuration is used.

## Improved completed certificate: 25.735

The same four-degree rational matrices and minorant also certify the unconditional bound E≥25.735. The run finished with `status=certified`, 30,959 visited nodes, 7,555 residual-positive leaves, 7,925 Gram-negative or symmetry-excluded leaves, zero pending boxes, maximum depth 34, and 30.37 seconds of subdivision. The full exact model is saved in `three_point_d4_exact_25_735.json`. This was an intermediate completed bound, superseded by 25.745 below. Its gap to the candidate energy is approximately 0.0249865312698, so it does not prove global optimality.

## Elementary verification of kernel positivity

Fix anchor x and choose an orthonormal basis e1,e2 of x-perpendicular. Set ζy=y·e1+i(y·e2). Then Re[(ζy conjugate(ζz))^k]=Qk(x·y,x·z,y·z); this follows directly from the real-part recurrence of powers and |ζy|²=1−(x·y)². For each basis index i put wi=Σy(x·y)^i ζy^k. The anchored Yk matrix sum equals Re(wi conjugate(wj)), a real positive semidefinite Gram matrix of two-dimensional vectors (Re wi, Im wi). For k=0 this is the outer product of the real sums. Summing over anchors preserves PSD. Summing over all ordered triples is unchanged by coordinate permutations, so the same positivity holds for the symmetrized Sk sum. This proves the kernel constraint used above directly, including zero transverse vectors.

The saved rational matrices have sizes 5,4,3,2,1, and minimum exact LDL pivot approximately 1.0019753694581281e−7. The residual has 102 nonzero monomials. Independent evaluation against the original numerical kernel implementation on 100 cube points agreed to maximum floating discrepancy 2.6645352591003757e−15. This numerical assembly crosscheck supplements, and is not part of, the exact certificate.

## Exact-only verification entry point

`verify_three_point_certificate.py` reads only a specified saved rational certificate JSON. It does not read the numerical SDP export. It checks the matrix dimensions, exact symmetry, strict positive rational LDL pivots, the minorant, exact reconstruction of F and R, equality of the reconstructed and stored residual coefficient dictionaries, all six residual permutations, and the exact lower-bound identity. It then redoes the full integer Bernstein domain traversal. It imports only arithmetic/subdivision helper functions from the model-generation script; the latter is protected by a main guard and its model-generation routine is not called. The verifier exits with code 0 only if the whole-domain traversal finishes and writes a separate `_verified.json` report.

For example:

    PYTHONPATH=proof_work/python_deps python3 proof_work/verify_three_point_certificate.py proof_work/three_point_d4_exact_25_735.json --budget 100000 --seconds 120

## Strongest completed certificate: 25.745

The same four-degree rational model has now certified E≥25.745 on the entire Gram domain, without any competitive-configuration distance cutoff. The saved exact model is `three_point_d4_exact_25_745.json`. The traversal completed with 172,137 visited nodes, 43,623 positive residual leaves, 42,446 Gram-negative or symmetry-excluded leaves, zero pending boxes, maximum depth 41, and 208.57 seconds. The gap to the candidate energy is approximately 0.0149865312698. Global optimality remains unproved.

The exact-only verifier has now also independently completed for the strongest 25.745 certificate: all 172,137 nodes, 43,623 positive leaves, 42,446 exclusions, zero pending boxes, maximum depth 41, and exit code 0. The report is `three_point_d4_exact_25_745_verified.json`; total runtime was 237.49 seconds. It previously completed for 25.735 as well. Reproduce the strongest check with:

    PYTHONPATH=proof_work/python_deps python3 proof_work/verify_three_point_certificate.py proof_work/three_point_d4_exact_25_745.json --budget 300000 --seconds 360

Generation and independent verification share exact arithmetic helper functions, so a separate implementation remains valuable for a stronger software audit. No numerical solver output is trusted by the exact-only verifier. All background jobs started for these experiments have been collected.
