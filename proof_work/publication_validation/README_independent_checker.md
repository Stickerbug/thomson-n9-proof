# Independent conditional coverage checker

`checker_exact.py` uses only the Python standard library, arbitrary precision integers, and exact `Fraction` values. It imports none of the frozen interval, Bernstein, signed128, C, or coverage implementations. The old analytic engine was read only to identify the mathematical inputs and certificate semantics. No Lean installation is needed or performed.

The checker establishes a **complete binary tree partition of the root box** B=[-1,14/25]^3 and **conditional residual nonnegativity on** D={-1 <= u <= v <= t <= 14/25, Gram(u,v,t) >= 0}. Ordering and Gram exclusion leaves show absence of feasible D-points. This is not a complete independent proof of the nine-point Thomson minimum. Local nonnegativity, the intended model's coefficient enclosures, PSD, pair reduction, and reduction to D remain explicit premises. Symmetry of the supplied midpoint itself is checked exactly.

## Exact mathematical reconstruction

The root domain is hardcoded as `[-1,14/25]^3`. Nonzero `delta` is rejected. From `F_mid_sym`, `epsF`, and `c_interval=[c_lo,c_hi]`, the checker constructs

`K = -7 F_mid_sym - c_hi - 10 epsF`, and `d(t) = F_mid_sym(1,t,t)`.

It requires nonnegative `epsF`, ordered c intervals, exact symmetric midpoint coefficients, per-axis degree at most 10, positive integer precision, nonnegative multipliers, and valid center intervals. Stored K/d monomials and root Bernstein arrays, when present in the exported schema, must equal independent reconstruction. Their stored values are never used as the source of a polynomial bound.

For one axis with degree n and box [l,r], the exact transform matrix from power t^k to Bernstein coefficient i is

`M[i,k] = sum_{j=0}^{min(i,k)} binom(k,j) l^(k-j) (r-l)^j binom(i,j)/binom(n,j)`.

The checker applies those rational matrices successively along each coordinate, then floors at scale `S=2^bits` for a lower bound. Its midpoint subdivision computes the exact closed binomial sums before one final floor or ceiling. In particular, for integer Bernstein inputs b,

`left[i] = floor(sum_{j=0}^i binom(i,j)b[j] / 2^i)`,

`right[i] = floor(sum_{j=i}^n binom(n-i,j-i)b[j] / 2^(n-i))`.

The corresponding upper operation uses ceiling. These bounds follow from nonnegative subdivision weights; they do not reproduce the old repeated rounded averaging code.

For every distinct dyadic axis interval, D20 is obtained directly by rational conversion of the exact d polynomial and then coefficientwise ceiling. No inherited rounded D tree or old cache is used. If [l,r] is the axis interval, set `a=(r-l)/(1-l)` and `u=(t-l)/(r-l)`. Here `0<a<1`. The positive Taylor series of `f(t)=(2-2t)^(-1/2)` has coefficient

`f(l) binom(2k,k) a^k / 4^k`.

The integer base `n=isqrt(floor(S^2/(2-2l)))` satisfies `n/S <= f(l)`. Coefficientwise floors of `n binom(2k,k) a^k/4^k`, through degree ten, therefore give a rigorous lower Taylor polynomial. D20 upper Bernstein coefficients are converted exactly to power coefficients A[k]. For u in [0,1], the discarded high-degree part is at most `sum_{k=11}^{20} max(A[k],0)`. Subtracting this constant and A[0:11] from the lower Taylor polynomial gives a valid lower bound for `S*(f-d)`. Conversion to degree-ten Bernstein coefficients ends with coefficientwise floor. (Rigorous lower bound does not mean a strictly positive gap at every endpoint.)

At positive leaves, every tensor coefficient of `K + h(x)+h(y)+h(z)` must be nonnegative. At boundary leaves the same test is applied to `K-lambda*Gram + h(x)+h(y)+h(z)`, where

`Gram = 1 + 2xyz - x^2-y^2-z^2`.

An upper rational Gram tensor and lower K tensor give the first sufficient test. If separate or accumulated rounding makes it fail, the checker independently transforms the exact combined `K-lambda*Gram` polynomial on that leaf and retries; a harmless rounding difference is not misreported as a defective certificate. The exported old integer witness is informational: the checker recomputes the bound and checks its sign, rather than requiring equality to the old weaker-rounding witness.

## Tree and local premises

The JSONL stream must be a complete binary tree in preorder. A stack of expected paths and reconstructed dyadic boxes enforces connectivity, disjoint interiors, no skipped or duplicate child, exact root domain, and exact closed midpoint splitting. Stored `box`, `levels`, and `indices` must match reconstruction at every node. A pending node or unknown reason is rejected; EOF with a nonempty stack is rejected. The final identity is `nodes=2*splits+1`.

Each leaf independently satisfies its claimed reason: strict interval ordering exclusion, strictly negative exact degree-two Gram Bernstein maximum, verified nonnegative polynomial tensor, verified boundary-multiplier tensor, or containment in a supplied conditional local core. A local core is reconstructed as `[center_hi-halfwidth, center_lo+halfwidth]` in every coordinate, and a supplied cached core must equal it. This checks containment under center uncertainty, but does not prove the local nonnegativity premise.

## Running and audit artifacts

Run from the workspace root:

```sh
python3 -u proof_work/publication_validation/test_checker_exact.py
python3 -u proof_work/publication_validation/checker_exact.py --inputs proof_work/publication_validation/sharp_root_inputs.json --tree proof_work/publication_validation/sharp_root_tree.jsonl --output proof_work/publication_validation/independent_full_result.json --expected-input-sha256 3dd4ba639e78cabaa2c3a8182db3724545751ade50635e6d542067338b281066
```

Historical serial job `bash-198` is **UNKNOWN_INCOMPLETE** after the runtime job registry was lost. Its last observed progress was 115000 nodes / 3002.0948615219677 seconds. There is no completed serial report; this progress is not counted toward the replacement verification below. The complete input has 136125 nodes: 68062 splits and 68063 leaves. The exported tree SHA256 is `4712313969755f9fb5126b7a95ced989db5e16710ccddffee5dad1cf91776c12`; a hash identifies data, not mathematical validity. The unchanged exact checker source SHA256 is `9ab4b9810740d1b83c4ecf2e9eef76f7d93c42aaff1ba85e51f8bc24c27a13bc`, matching the initial source manifest.

`independent_selftests.json` records 18 passing groups: exact transform evaluation, closed subdivision enclosure using 170-bit integers, tensor-axis checks, exact rational f-minus-d bound samples including D20 positive tails, valid small complete trees, and deliberately invalid trees/inputs. The negative fixtures cover a missing child, interior gap, duplicate root, illegal pending terminal, unknown leaf reason, nonzero delta, incorrect root domain, incorrect dyadic index, inconsistent root tensor, a mathematically false positive terminal, false Gram exclusion, forged local core, failed local containment, and negative enclosure radius. These are known invalid constructions; there is no assumption that changing an arbitrary integer must invalidate a certificate.

Python assertions are used only in the test program. The verifier uses explicit exceptions and therefore retains its validation under `python -O`.

## File-operation note

The atomic write tool produced a dangling symlink named `independent_checker.py` in this environment. The actual checker is the distinct regular file `checker_exact.py`, created exclusively using Python `open('x')` and immediately read and compiled. The dangling symlink is not a deliverable and was not used for validation. No frozen source was overwritten.

Supplemental tests: `python3 proof_work/publication_validation/test_checker_supplemental.py` reproduces six additional passing groups in `independent_supplemental_tests.json`: valid and mathematically false boundary leaves, negative lambda, asymmetric midpoint, forbidden floating input, and wrong external input digest. Together the two suites contain 24 passing groups.

## Exact source-input and local-premise linkage

`check_model_input_binding.py` independently parses frozen integer-over-power-of-two interval records using `Fraction`, without importing old interval arithmetic. `independent_model_input_binding.json` records nine passing checks. All 756 exported symmetric midpoint coefficients equal the six-permutation averages of frozen interval midpoints. The independently computed raw coefficient L1 error and symmetrized L1 error both equal exported epsF; this supplies the required uniform error bound on [-1,1]^3, including (1,t,t), conditional on the original coefficient enclosures. The c interval agrees exactly.

All twelve exported local cores are contained in the corresponding original local `row.box`, and the locals file explicitly references the same frozen coefficient SHA. The exported center and halfwidth are generally derived from the saved box rather than copied from its nominal original center/width. Core containment in the original certified box is the relevant verified linkage. No original local Hessian, graph or coefficient-generation proof is thereby made independent.

The extra binding script/report have a separate physical hash record in `independent_additional_manifest.json`; the main checker's initial source hash remains fixed throughout the full run.

## Recoverable subtree verification

`sharded_checker.py` imports only our own unchanged `checker_exact.py`, with no frozen engine or C imports. Its source SHA256 is `84fc29d43fe412e7332f799524383c42e97dc33b30f28bf401654b27d5681d3b`. All certificate arithmetic still uses arbitrary precision integers and `Fraction`; multiprocessing is standard-library orchestration.

Before any mathematical workers start, an independent complete geometry walk checks every actual tree node, builds exact contiguous subtree byte spans, and chooses a frontier of complete subtrees with at most 4000 nodes each. The production manifest contains 154 chunks and has SHA256 `7dd936c9d7e91c811924d19e611fb1e2b1aa9437186f4ea9df4530bc89621eff`. Sorted paths are checked for prefix overlap and the exact rational Kraft sum must equal 1. In a fully binary midpoint tree, prefix freedom plus this equality gives complete coverage by the frontier. Early terminal nodes are singleton chunks when appropriate.

Each mathematical chunk starts independently from the global root polynomial K and follows the actual ancestor split axes along its prefix. It does not accept a saved tensor or a pending stack as a certificate. It then rechecks every node, geometry and leaf reason in its entire subtree. Only a finished complete subtree receives a PASS result, bound to the manifest, input/tree/co/local data, both checker sources, and its exact tree byte-slice SHA. Reports are written to exclusive temporary regular files, flushed and fsynced, then published with a non-overwriting atomic hard link. A crash before publication leaves no apparent final PASS file.

The final aggregator walks the actual full tree again, checks every frontier path against actual spans/boxes/ancestor axes, rechecks prefix freedom and exact weight 1, verifies all artifact bindings and chunk byte digests, and sums the leaf reasons. The upper structure contributes exactly `frontier_count-1` split nodes; these are checked geometrically and added back to recover the full node and split counts.

**Execution-record trust boundary:** `--aggregate-only` verifies structure and bindings of execution reports; it does not recompute leaf arithmetic. `--resume` trusts only complete reports produced by a prior trusted local execution. Arbitrary external PASS JSON files can be forged; hashes are not mathematical evidence. An external reviewer must run a fresh directory, which recomputes every chunk, rather than download reports and call aggregate-only. Resume only after the previous workers have stopped; never run two coordinators in one run directory. The default refuses an existing run directory.

Fresh complete verification, from the workspace root, with a never-used output directory:

```sh
python3 -u proof_work/publication_validation/run_sharded_subprocess.py --run-dir proof_work/publication_validation/sharded_reproduction_NEW --workers 4 --chunk-nodes 4000
```

The first four-process attempt, job `bash-44`, failed before any chunk ran: Python multiprocessing could not create a POSIX named semaphore (`FileNotFoundError: [Errno 2] No such file or directory` in SemLock). Its failure log is preserved as `sharded_full_v1.log`. The mathematical checker source remains unchanged. The successful two-worker toy end-to-end transport test is recorded in `independent_subprocess_transport_tests.json`.

The replacement uses `run_sharded_subprocess.py` and `subprocess_shard_worker.py`: persistent subprocess pipes and a selectors event loop dynamically distribute work, using no shared named semaphore. They invoke precisely the frozen mathematical worker/aggregation functions. Their physical source hashes and child PIDs are recorded in `sharded_run_v1/subprocess-execution-v1.json`. No software was installed and no permission workaround was used.

The actual full execution uses `sharded_run_v1/`, managed job `bash-56`, four workers, physical log `sharded_subprocess_v1.log`, and PID record `sharded_run_v1/subprocess_wrapper_launch.json`. Its manifest was prepared separately; before using `--resume` to execute it, the launcher explicitly checked there were **zero** prior chunk results. All 154 mathematical chunks are therefore newly computed. The old unknown serial job's outputs, if ever produced, have a distinct path and are not used. Final status: **PASS_INDEPENDENT_CONDITIONAL_COVERAGE**, confirmed by completed job `bash-56` (exit 0) and publication audit `bash-91` (exit 0). All 154 chunks were freshly computed. Total mathematical execution elapsed 2854.251 seconds (about 47 minutes 34 seconds).

## Exact integer Gram optimization and additional tests

On one degree-n axis interval [a/d,(a+39)/d], n>=2, the exact Bernstein coefficients of x and x^2 are

`Bx[i]=(n*a+39*i)/(n*d)`

`Bx2[i]=(n*(n-1)*a^2+2*(n-1)*a*39*i+39^2*i*(i-1))/(n*(n-1)*d^2)`.

Here d=25*2^level and a=39*index-d. Tensor Gram coefficients are exactly `1+2*Bx*By*Bz-Bx2-By2-Bz2`. A common positive integer denominator gives pure integer numerators; ceiling of `lambda*S*Gram` is one exact integer division per coefficient. Degree two handles negative Gram leaves, while degree ten handles the boundary correction. This replaces no bound by an approximation. A negative first sufficient test still invokes the original independent exact combined-polynomial fallback.

`independent_sharded_selftests_v2.json` records **24 additional passing groups**, bound to both checker source hashes. They compare all n=2/n=10 coefficients against the independent generic Fraction transform on three deterministic dyadic geometries, test three lambda values and exact ceil results, execute toy chunks from the full root through aggregation, and reject missing/duplicate/overlapping/illegal frontiers, missing/extra tree children, illegal terminals, wrong geometry/ancestor axes/byte spans, and altered status/count/hash/binding reports. Together with the original 18+6 groups, there are **48 passing test groups**. The earlier unbound `independent_sharded_selftests.json` is historical; v2 is authoritative. The test script creates an exclusive output file; to rerun without overwriting reports, place copies of the three Python sources (`checker_exact.py`, `sharded_checker.py`, `test_sharded_checker.py`) in a fresh temporary directory and run the test script there.

`check_known_failed_kernel.py` and `independent_known_failed_kernel.json` independently confirm the old failed rational kernel at its existing exact negative point (-296937/1000000, 84507/200000, 84507/200000); all exact equality and negativity checks pass. No random integer mutation assumption is used. This regression is separate from the conditional sharp certificate check.


The persisted transport test is `test_subprocess_transport.py`. Its source-bound report `independent_subprocess_transport_selftests.json` adds two passing groups: complete two-worker toy verification and a mathematically false positive leaf that must fail in a worker, propagate a nonzero supervisor exit, and prevent an aggregate PASS. It has an `--output` argument for reproducible non-overwriting output. These two groups bring the current total to **50 passing groups** (18+6+24+2). The earlier one-case transport smoke report is preserved separately and is not counted twice. For example:

```sh
python3 proof_work/publication_validation/test_subprocess_transport.py --output proof_work/publication_validation/transport_reproduction_NEW.json
```

`audit_sharded_publication.py` is the final binding audit entry point after the production aggregate exists. It repeats structure/report aggregation in a separate directory, compares physical evidence and all source bindings, checks the 50 passing test groups and all154 freshly computed chunks, and writes `independent_publication_final.json`. It will refuse a missing or mismatched aggregate. This final audit does not replace fresh mathematical computation of the chunks.


## Final audited production result

`independent_publication_final.json` records **PASS_INDEPENDENT_CONDITIONAL_COVERAGE**. All 17 final physical binding/evidence checks passed, the initial exact checker source is unchanged, and the four-worker execution freshly recomputed all 154 chunks. `sharded_run_v1/aggregate.json` is the raw production report; `sharded_run_v1/publication_reaggregation/aggregate.json` repeats the complete structural/report aggregation in a separate directory. The full tree has **136125 nodes, 68062 split nodes and 68063 leaves**.

| Independently verified leaf reason | Count |
|---|---:|
| boundary_multiplier | 10518 |
| gram_negative | 26797 |
| local_region | 78 |
| ordered_disjoint | 3278 |
| positive | 27392 |

The tree partitions all of B=[-1,14/25]^3. The residual nonnegativity conclusion applies conditionally to D={-1 <= u <= v <= t <= 14/25, Gram(u,v,t) >= 0}; exclusions certify no feasible D-point in those boxes. The original algebraic coefficient enclosures, local nonnegativity on the frozen local boxes, PSD, pair reduction and reduction to D remain explicit premises. This completed independent arithmetic validation is **not an independent complete proof of the nine-point Thomson minimum**.

The production aggregate SHA256 is `a0b3a353758119ddd4d2b39b5b2d32eee6d6b127c62b9169dd2482c1f6fdd13c`. Root-input, tree, frozen coefficient/local and all mathematical/transport source digests are in the final JSON. The accompanying `independent_delivery_manifest.json` hashes the final deliverables, documentation and completed execution records. Historical serial job `bash-198` remains UNKNOWN_INCOMPLETE and contributes no work to this PASS.
