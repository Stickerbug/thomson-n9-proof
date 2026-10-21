# Independent arithmetic for twelve complete local boxes

The result is INDEPENDENT_TWELVE_LOCAL_ARITHMETIC_PASS_CONDITIONAL_ON_EXACT_CONTACTS. The single main run took 86.69966144498903 seconds and exited 0. All 9 interior classes and 3 boundary classes pass on the original complete source boxes. No width was reduced. There are 33 strictly positive interval LDL pivots in total. The smallest lower bound is approximately 0.000931228719415449, from CFF. Exact rational endpoints, not these decimal displays, determine every pass.

The construction reads the independently built 640-bit R_H with 807 monomials. It reads the archived local certificate only for labels, kind, box endpoints, center intervals and rational congruence_W. It does not consume archived Hessians, LDL factors, positivity flags or expanded-u boxes. Each new center is reconstructed from the independently refined true-root bracket and its candidate label, and its interval must be contained in the archived center interval. This tighter center interval changes no source-domain endpoint. Rows are classified by kind, since GGB/CFF/DDD are interleaved in the source order; the count is checked to be exactly 9+3.

For each class, the code performs three successive binomial shifts on the full sparse polynomial. An axis shift replaces a degree n term by sum_(k=0)^n binom(n,k)*center^(n-k)*y^k. Outward interval coefficients enclose the exact polynomial translated about the fixed true center. The domain y=sourcebox-center includes every original source point. The full shifted coefficient map is retained in each checkpoint, not represented only by a count or hash. First and second derivatives use direct monomial differentiation. Evaluation sums all shifted terms with outward intervals; even powers use a nonnegative square enclosure.

Each rational W is checked over Fraction to be exactly unit lower triangular. Its full exact inverse is constructed and W*inverse=I verified, so invertibility does not depend on a saved assertion. The interval Hessian is transformed as W*H*W^T. A fresh interval LDL factorization requires every pivot lower endpoint strictly greater than zero. This proves positive definiteness throughout the stated source domain by congruence and the interval inclusion property.

For an interior class, the target is the three-variable Hessian of R_H on the entire source cube. Conditional on the separately justified exact equalities R_H(center)=0 and gradient R_H(center)=0, convexity of the cube and positive definiteness imply R_H>=0 everywhere on that cube. An interval merely containing zero is not used to establish either equality.

For a boundary class, b(v,t)=vt-sqrt(D), D=(1-v^2)(1-t^2), on the full original v,t rectangle. Both v,t intervals must lie strictly inside (-1,1), and both radical factors are proved positive. The code independently derives and evaluates

b_v=t+v(1-t^2)/sqrt(D), b_t=v+t(1-v^2)/sqrt(D),
b_vv=(1-t^2)/((1-v^2)*sqrt(D)),
b_tt=(1-v^2)/((1-t^2)*sqrt(D)), b_vt=1-vt/sqrt(D).

The new u interval is the hull of the entire original source-u interval and the entire b(v,t) interval. R_u>0 is checked on this full expanded hull times the original v,t rectangle, including every segment from a source point down to the graph. The R gradient and full Hessian on that same expanded domain give the pulled-back graph Hessian by J^T*H_R*J+R_u*H_b, with J having rows (b_v,b_t),(1,0),(0,1). This graph Hessian receives the same independently verified W and strict LDL checks. The code saves all radical, graph derivative, expanded hull, R derivative and Hessian enclosures.

The exact boundary centers are on the lower graph by elementary identities: for GGB, sqrt(D)=2r(1-r^2), hence b(G,B)=G when 0<r<1; for CFF, b(F,F)=2F^2-1=C; for DDD, b(-1/2,-1/2)=-1/2. Conditional on the separate exact contact/Hermite theorem, the graph function G(v,t)=R_H(b(v,t),v,t) has value and gradient zero at that center. Strict graph Hessian positivity on the full convex rectangle gives G>=0 there. The Gram determinant identity det= D-(u-vt)^2 shows that a Gram-feasible source point satisfies u>=b(v,t). The proved R_u>0 along the connecting segment then yields R_H(u,v,t)>=G(v,t)>=0. These implications are ordinary mathematical lemmas recorded explicitly, not deductions from zero-containing interval residuals.

| Original row | Labels | Type | Smallest LDL lower endpoint, display |
| --- | --- | --- | ---: |
| 0 | AAA | interior | 0.00901295581302 |
| 1 | CBA | interior | 0.00244653008814 |
| 2 | CCA | interior | 0.00153752929857 |
| 3 | AFF | interior | 0.00184262542866 |
| 4 | GAF | interior | 0.00467366779398 |
| 5 | BFF | interior | 0.00349492636061 |
| 6 | GGB | boundary | 0.00330889054408 |
| 7 | CFF | boundary | 0.000931228719415 |
| 8 | CGF | interior | 0.00240786971274 |
| 9 | DDD | boundary | 0.0306086756277 |
| 10 | DFF | interior | 0.00162440112324 |
| 11 | GDF | interior | 0.00290845818461 |

The main code and per-class result files use new names only. The completion manifest checks that each saved sourcebox endpoint equals the corresponding archived endpoint exactly as a Fraction, all 33 pivots have positive exact rational lower bounds, all 3 expanded hulls contain both the original u domain and graph domain, and R_u is strictly positive on each. It records SHA256 and byte counts for every checkpoint and the code, input, test and documentation bindings. Existing export, pair, candidate, PSD, N/contact/F/c and Hermite artifact manifests are rechecked unchanged.

independent_local_component_tests.py supplies a second arithmetic path: a direct exact Fraction multinomial expansion validates every translated coefficient of a synthetic multivariate polynomial; direct Fraction monomial derivatives validate all 3 gradient and 9 Hessian entries. An independent exact Fraction second-order dual-number implementation evaluates b(v,t) and a pulled-back synthetic polynomial at four rational points whose radicals are exact squares. It checks the closed graph value/gradient/Hessian and complete Hessian chain rule. Six negative cases reject nonunit W, a nonzero upper W entry, wrong W dimensions, a negative LDL pivot, a zero LDL pivot and a pole graph argument. The component-test process exited 0.

## Later Lean continuation (separate from the historical arithmetic run)

The local results are also exported to Lean by `export_local_lean.py` and
`export_local_ldl_replay.py`. Reproducibility checks are:

```
python3 -u proof_work/publication_validation/export_local_lean.py --check
python3 -u proof_work/publication_validation/export_local_lean.py --self-test
python3 -u proof_work/publication_validation/export_local_ldl_replay.py --check
```

The generated data covers 9 interior and 3 boundary classes, 33 strictly
positive LDL pivot lower bounds, and a 147-operation replay (9*15 + 3*4).
The Lean layer currently records generic interval/algebra/convexity semantics,
endpoint ordering, pivot positivity, and box containment. It is in progress and
awaits kernel verification. In particular, this export does not claim an actual
real Hessian evaluation, membership of real Hessian entries, the actual residual binding to the identity
`P = W H W^T`, exact contact or gradient identities, boundary graph chain rules
or derivative bounds, actual residual nonnegativity, tree terminal bindings, or a closed
final theorem.

The independent arithmetic conclusions remain conditional on the exact45
contact compatibility and true Hermite interpolation theorems. This task
supplies local interval arithmetic and full-domain coverage, not those exact
equalities, the main tree away from locals, equality classification of
nine-point configurations, or a Lean theorem. No Lean build or archived-file
edit was performed by the arithmetic run.
