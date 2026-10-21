# d12 contact design — preparation only

Status update: after the parent explicitly extended preparation by up to120s, real new-prefix core, solver and validation files were created with bash and confirmed by read. The bounded solver job was launched. The initial paragraph below records the earlier preparation outcome and is superseded by this update. The path d12_contact2026_run.py was later identified by the parent as EPERM and is no longer accessed. The working driver is d12_contact2026_solver.py.

Earlier preparation status: no SDP was started, no validation job was started, no new numeric bound or certificate was obtained. Preparation did not yield a reliably persisted runnable driver within the preparation allowance. The write tool reported creation of d12_contact2026_run.py, but both read and a Python filesystem check returned that it did not exist. This real note was created through bash and must itself be checked with read. All previous core files, parent reports and manifests are untouched.

## Dependencies inspected

- sharp_contact_refinement2026_core.py: exact_candidate, derivative, gram_geometry, original, jets, build.
- sharp_contact_refinement2026_competitive_batch3.py: PSD margins, objective scaling, contact elimination, curvature corrected boundary jets.
- sharp_contact_refinement2026_refine.py: IndependentActual and solver_info. IndependentActual.F reads module-global DEGREE; it MUST explicitly be changed to 12 in the new driver, or copy a degree-parameterized recurrence into the new prefix. Otherwise original-A validation will access a recurrence only computed through degree10.
- sharp_boundary_actualf_v3.py: polynomials, Compiled, full-domain random_cond, boundary_points, near_points. These samplers already enforce Gram PSD and [-1,.56]^3 without competitive filtering.
- candidate_low_rank.py: features(r,k,m), nullspace_two_rows(p,c), exact rational row elimination.

## Construction

Set d=12 and r=Fraction('0.71054833409295381132770417927279124'). For k=0..12, compute p,c=features(r,k,13-k), exact basis columns=nullspace_two_rows(p,c), and reduced QR of their floating-point images N_k. Expected nullities are [11,11,9,9,7,7,5,5,3,3,1,1,0], with 322 independent symmetric B coordinates. These expectations were NOT numerically verified in this preparation-only attempt.

Use polynomials(N,12) and Compiled to obtain the affine residual design. Generate candidate 12 triangle types with exact_candidate(r); exact rational Gram determinant sign distinguishes 9 interior and 3 boundary types. Assemble E from 12 value rows, 27 interior derivative rows, and 6 boundary tangent rows. Use derivative(comp,candidate) for values and derivative(...,(axis,)) for first derivatives. RHS values are sum_i(2-2t_i)^(-1/2)-ENERGY/12; derivative RHS is (2-2t_i)^(-3/2). Boundary tangent rows are T^T Dr and T^T fprime from gram_geometry.

Compute full SVD of E, report all singular values and the chosen numerical threshold, rank, ||E sol-b||_infinity, discarded-left-RHS norm, and ||E Z||_infinity. Rank33 is only an expectation from d10 and MUST NOT be imposed. If compatibility error exceeds the declared tolerance, stop rather than bury incompatibility in a pseudoinverse. A suggested floating-point screening tolerance is 1e-8, with r and E* approximation limitations reported explicitly. x=sol+Z y is permitted only after this audit, and the final solution still needs all 45 contact errors reported.

Do NOT simply set old core.DEGREE=12 and call old build(): its final source-loading block attempts n.T @ a @ n against d10 source A blocks without enlarging them. Build the new d12 objects independently. To lift a d10 seed, first zero-pad A_k from size11-k to13-k, then form B_k=N_k.T A_padded N_k. Lifted blocks are a numerical warmstart, not a proof.

## Correct convex conditions

For all nonempty B: B >= 1e-7 I, sum trace(B)<=5000. At each interior candidate enforce Hess R>=1e-7 I3. At each boundary point let g=grad(1+2uvt-u²-v²-t²), Hg its Hessian and T an orthonormal basis for g-perp. Define lambda=g dot gradR / (g dot g). Enforce lambda>=0 and T.T(HessR-lambda Hg)T>=1e-7 I2. Boundary tangent contact rows ensure normal stationarity; do not impose the full3D HessR PSD at boundary.

Use tau>=0, residual constraints R(training)>=-tau, objective tau+1e-9 trace. If using ts=tau/1e-6, the equivalent objective is ts+.001 trace. Every actual solve must use CLARABEL time_limit90, max3 rounds, no fallback solver. Numerical tau0 is not a proof.

## Full-domain cuts and search

Domain: Gram PSD intersect [-1,.56]^3, no C or kernel competitive filter. Application to n9 still depends on the independently justified .56 pair cutoff; this experiment does not establish that cutoff.

Load at least several thousand old training points from sharp_contact_refinement2026_results.json and optionally sharp_boundary_actualf_d10_v3.json and nonsharp_nullspace_actualf_d10_run2.json. Preserve source names, raw counts, full pool and selected active cuts. Select up to5000 active cuts, retaining all candidate types and the following valleys plus feasible neighborhoods:

T1=(-.759220762336624,-.29211600772137486,.32931701954562287)
T2=(.346480293,.346480553,.346480725)
T3=(-.071348864,.339279344,.339279344)

Sort triples by symmetry, filter Gram determinant>=-declared tolerance, and avoid competitive filters. For each new iterate use fresh full-domain random and boundary points, vectorized constrained DE, and SLSQP polishing of low-residual points. Reserve <=30s total validation, including original-A recurrence audit. A search deadline must include evaluation of the initial pool; an alarm started only after that scan does not enforce the total30s cap. Random points alone are not validation of nonnegativity.

Log minB eigenvalue, all45 contact errors, interior Hessian eigenvalues, boundary lambda, normal stationarity error and corrected tangent Hessian eigenvalues. For every negative residual report original-basis R, exact floating-point coordinates and Gram determinant; original-A versus compiled discrepancy must be audited with recurrence through degree12. Evaluate candidate residuals directly as well.

If successful numerically, save original A/N/B/x/c, F111, E*, r approximation, pool, active cuts, source filenames, solver statistics and all raw search output under d12_contact2026_* only. Exact algebraic reconstruction, certified PSD and exhaustive domain certification remain separate necessary work for the parent. A negative low-order kernel valley is not a Thomson n9 counterexample.

## Result

No d12 rank, tau, eigenvalues, residual minimum or solver feasibility conclusion was measured. Existing rigorous lower bound25.7599205 and candidate25.75998653126983156 are unchanged. No background jobs were launched, hence none remain outstanding. The practical correction for the next authorized attempt is to create the new-prefix driver with bash immediately, confirm it with read before further preparation, and independently rebuild d12 rather than invoking the old source-loading build.
