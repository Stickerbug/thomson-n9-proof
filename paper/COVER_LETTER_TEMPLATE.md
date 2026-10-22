# Cover letter template

Replace the bracketed fields before sending to a journal.

Dear [Editor-in-Chief/Handling Editor],

Please consider our manuscript, “A Lean-Verified Computer-Assisted Proof of the Nine-Point Thomson Minimum,” for publication in [Journal]. The manuscript is authored by Jingxing Huang (Qian Xuesen College, Xi'an Jiaotong University; ORCID 0009-0002-9805-0331; adult-huang@outlook.com).

The paper gives a reproducible computer-assisted proof of the frozen nine-point Thomson minimum claim. The mathematical argument reduces the problem to an exact three-variable residual on the physical ordered Gram domain and combines positive-semidefinite three-point bounds, contact equations, local Hermite/Hessian certificates, and a complete Bernstein subdivision certificate. The full theorem is formalized in Lean 4.34.1. The recorded validation contains 2390 modules, 1507 ordered axiom audits, all 807 distinct archived coefficient targets, and a complete fresh Lean-kernel replay.

The companion repository provides the Lean sources, exact certificate data, validation scripts, recorded logs, the independent conditional Python checker, and the review bundle. The manuscript states the validation boundary explicitly: Lean's own kernel replay is not an external independent proof kernel, the Python checker is conditional on the stated model and local premises, and the paper does not claim congruence uniqueness of all minimizers.

The author received no external funding and declares no competing interests. Language-model assistance was used for proof discovery, formal-code engineering, validation-script engineering, and manuscript editing. The models used were DeepSeek-V4.1-Flash-1017, ChatGPT-6.1 Sol, and ChatGPT-6 Astra. Jingxing Huang is responsible for the mathematical statement, formal code, validation records, and release artifacts.

This manuscript is currently a preprint/research archive and is not under consideration elsewhere. The code and validation release is available at https://github.com/Stickerbug/thomson-n9-proof/releases/tag/n9-proof-2026-10-23 and is archived at https://doi.org/10.5281/zenodo.23573472. No arXiv identifier has been assigned.

Thank you for your consideration.

Sincerely,

Jingxing Huang  \\
Qian Xuesen College  \\
Xi'an Jiaotong University  \\
adult-huang@outlook.com
