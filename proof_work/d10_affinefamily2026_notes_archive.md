# Shared exact affine family and negative residual witness

All previous certificates and sources remain frozen. No new global search was launched.

`narrowroot2026_pointcheck.json` proves a strictly negative TRUE residual at the rational point in its negative_witness field. Starting at the guarded midpoint, increasing only u by 10^-12 gives R approximately -2.7909477713506696e-18, Gram approximately .17964>0. Outward I384 Horner and independent exact Fraction monomial summation both have strictly negative upper endpoints. This disproves the current residual nonnegativity certificate, not the Thomson candidate.

`d10_affinefamily2026_build.py` completed in 24.345 seconds with exit 0 and a 120-second hard alarm. The three endpoints correspond respectively to first_batch_original_PSD_seed, third_batch_original_models[0], third_batch_original_models[1] from the saved batch3 original data. Stored x and B entries are checked equal as exact decimal rationals, and the stored nullspace bases are checked equal before construction.

The build performs one shared exact analytic contact-matrix construction and one 33-column LU, recording the row swaps and elimination multipliers. These are reused for all three rational seed residuals. Each endpoint's 33 corrections, all45 interval consistency checks and all reduced-block positive LDLs are recomputed. Exactness of all45 contacts uses the existing rank33/W/stationary-root theorem, not just zero-containing residual intervals.

All three true-root endpoint residuals have 807 terms and use the same narrowroot2026_root.json and fresh narrowroot2026_hermite.json H27 (14 distinct Hermite nodes, each with multiplicity2). The files are d10_affinefamily2026_endpoint{i}_certificate.json and d10_affinefamily2026_endpoint{i}_coefficients.json for i=0,1,2. d10_affinefamily2026_shared.json stores NN, rational basis transforms, root, M, rhs, upper LU, swaps/multipliers, pivots and the Hermite hash. d10_affinefamily2026_result.json stores endpoint hashes and the family theorem.

For rational weights with sum w_j=1, define nonselected coordinates as the weighted rational seeds. The weighted corrected endpoint vectors obey the SAME selected contact equations, because M sum(w_j x_j)=sum(w_j rhs)=rhs. The invertible33submatrix gives uniqueness of the selected coordinates; hence x(w)=sum(w_j x_j). Therefore B,A,F,c and R_H are affine; H is shared and sumweights=1. If weights are nonnegative, strict PSD follows by convexity of the endpoint positive-definite reduced blocks. Signed weights require a separate PSD check.

The helper d10_affinefamily2026_combine.py verifies endpoint hashes and accepts three nonnegative exact rational weights summing to1. It produces compatible R/F/c interval coefficients and reduced x enclosures by outward384bit operations, without rerunning LU or export. It does not claim new local or global residual nonnegativity. Example from workspace root:

PYTHONPATH=proof_work/python_deps python3 proof_work/d10_affinefamily2026_combine.py --weights 112219/500000 0 387781/500000 --output proof_work/new_weight_coefficients.json

At the saved old negative witness, the three endpoints give approximately -6.987726211613006e-9, -3.2857460139872392e-9, +2.0221610815009658e-9. Thus that point alone does not exclude the convex hull.

A numerical midpoint Newton direction at the guarded initial point is (0.0006659877111804839,0.00015566734420174332,0.0007405189639863644), with quadratic predicted drop -2.3564211264894975e-9. This is a diagnostic only; no new minimization was run here.
