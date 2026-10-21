# Independent interval LDL for the reduced blocks

This checker reads only indices and reduced_solution_enclosures as mathematical inputs from d10_relative_normal_exact2026_certificate.json. It does not consult PSD_LDL, saved pivots, or status strings. Source SHA256, checker SHA256 and independent arithmetic-module SHA256 are retained. Original certificates, engines and other checkers are not edited.

The fixed reduced-block dimensions for k=0,...,10 are (9,9,7,7,5,5,3,3,1,1,0). Their upper triangles have 190 coordinates in total. The checker constructs the complete expected set {(k,i,j):0<=i<=j<dimension[k]}, requires exactly 190 input records and 190 raw enclosures, and rejects noninteger or noncanonical indices, duplicates and out-of-range coordinates. Equality of the actual and expected sets proves no coordinate was omitted. These fixed dimensions are a validation specification for the provided reduced representation; deriving them from kernel complements and verifying the complements themselves remains outside this sublayer.

Each enclosure is decoded directly as rational numerator/2^384, with both endpoints checked for correct order, and embedded in the independent 640-bit outward interval implementation from independent_candidate_bounds.py. No old I384 implementation or model helper is imported. A symmetric matrix is built by reflecting its upper triangle. The standalone LDL routine also checks exact equality of opposite interval entries before factorization.

For each j in order the checker computes

D_j = B_jj - sum_{k<j} L_jk L_jk D_k,
L_ij = (B_ij - sum_{k<j} L_ik L_jk D_k) / D_j for i>j,
L_jj = 1.

All operations use outward endpoint rounding at 640 bits. Every pivot is required to have strictly positive lower endpoint before division. Reciprocal rejects zero-containing intervals. All full reconstructed B enclosures, L enclosures and D enclosures are saved, together with each block's dimension and exact minimum pivot lower bound. Empty k=10 is reported as VACUOUS_EMPTY_PSD and has no pivot/minimum.

Why this verifies a whole family of matrices: fix any real symmetric matrix whose upper-triangle entries belong to the supplied enclosures. Inductively, its exact scalar LDL calculations are contained in the interval operations. Strict positive pivot lower endpoints imply its exact D entries are positive. Its exact unit lower triangular L is invertible, so x^T B x=(L^T x)^T D (L^T x)>0 for x!=0. Thus every nonempty B in the provided interval family is positive definite, regardless of dependencies between enclosure coordinates. Rounding/dependency overestimation weakens the test; it cannot turn a nonpositive exact pivot into a certified positive one.

Six mathematical negative tests cover duplicate indices, noncanonical lower-triangle indices, deletion of one coordinate, an explicitly nonsymmetric interval matrix, a forced negative first diagonal, and an inverted raw interval. They must fail before any success report, independently of hashes.

The claim is conditional: all symmetric reduced B matrices in these supplied enclosures are PD. Membership of the actual constructed contact-compatible solution in the enclosures still requires an independent verification of the 33LU construction. This checker does not verify those contact equations or their kernel model. The algebraic implication N B N^T is PSD for every real N follows from y^T N B N^T y=(N^T y)^T B (N^T y)>=0, but this implication and the link to the full model have not been Lean formalized here. This is a PSD arithmetic sublayer, not a complete final nine-point proof.

Run once with python3 proof_work/publication_validation/independent_psd_blocks.py. The result and log are new files; exclusive creation prevents overwriting an earlier result. Output artifacts are independent_psd_blocks_result.json, independent_psd_blocks.log, and independent_psd_blocks_completion.json. Exact rational strings are proof data; decimals in the completion manifest are display-only approximations. No Lean is installed.
