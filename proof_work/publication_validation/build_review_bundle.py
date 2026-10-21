#!/usr/bin/env python3
"""Rebuild the referee-facing Thomson n=9 review bundle.

The bundle contains the frozen proof candidate, the exact arithmetic evidence,
the independent checkers and their recorded results, the coverage-tree export,
and the Lean sources. It intentionally excludes the Lean build cache, the
toolchain binaries, and per-shard intermediate contact files.
"""
import hashlib
import json
import os
import zipfile
from datetime import datetime, timezone

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
PROOF = os.path.join(ROOT, "proof_work")
PV = os.path.join(PROOF, "publication_validation")
OLD_BUNDLE = os.path.join(PROOF, "THOMSON_N9_REVIEW_BUNDLE.zip")
NEW_BUNDLE = os.path.join(PROOF, "THOMSON_N9_REVIEW_BUNDLE_v2.zip")
MANIFEST = os.path.join(PROOF, "SHARP_N9_REVIEW_MANIFEST.json")

# Frozen source list for the root of the canonical review archive.  Keep this
# explicit so a rebuild cannot silently drop baseline documents/data when an
# archive is unavailable.  Compiled shared objects are deliberately excluded.
BASELINE_ROOT_FILES = [
    "THOMSON_N9_CURRENT_zh.md", "THOMSON_N9_PROOF_CANDIDATE_zh.md",
    "analytic10_2026_sum.c", "analytic10_sharp2026_engine.py",
    "analytic10_sharp2026_run1.json", "analytic10_sharp2026_run1_inputs.json",
    "candidate_low_rank.py", "candidate_triple_types_v1.json",
    "certify_pair_moments.py", "certify_three_point_d4.py",
    "contact_minorant_curvature_v1.json", "contact_minorant_factor_v1.json",
    "d10_contact_left_geometry_v1.json", "d10_exact_contact_jets_v1.json",
    "d10_exact_contact_jets_v1.py", "d10_exact_contact_psd_seed1_v1.json",
    "d10_exact_contact_psd_seed1_v1.py",
    "d10_relative_normal2026_contact_geometry_checks.py",
    "d10_relative_normal2026_contact_geometry_review.json",
    "d10_relative_normal2026_contact_geometry_review.md",
    "d10_relative_normal2026_results.json",
    "d10_relative_normal_exact2026_certificate.json",
    "d10_relative_normal_exact2026_coefficients.json",
    "d10_relative_normal_exact2026_locals.json",
    "d10_relative_normal_exact2026_locals.py",
    "d10_relative_normal_exact2026_seed.json",
    "d10_sharpconvex_exact2026_certificate.json",
    "d10_sharpconvex_exact2026_coefficients.json",
    "d10_sharpconvex_exact2026_export.py",
    "d10_sharpconvex_exact2026_kernel.py",
    "d10_sharpconvex_exact2026_local.json",
    "d10_sharpconvex_exact2026_local.py",
    "d10_singleendpoint2026_kernel.py", "dyadic_interval.py",
    "exact128_2026.c", "exact128_2026.py", "exact128_2026_test.py",
    "exact128_2026_test_results.json", "exact_tensor_bernstein.py",
    "narrowroot2026_certificate.json", "narrowroot2026_coefficients.json",
    "narrowroot2026_export.py", "narrowroot2026_hermite.json",
    "narrowroot2026_hermite.py", "narrowroot2026_kernel.py",
    "narrowroot2026_local_formulas.py", "narrowroot2026_precondition.py",
    "narrowroot2026_root.json", "pair056_optimized_certificate.json",
    "pair_moments_certificate.json", "relative_normal2026_replay2.py",
    "sharp2026_final_linkage.json", "sharp_contact_refinement2026_results.json",
    "three_point_export.json", "verify_pair056_saved.py",
    "verify_sharp2026_final_linkage.py", "verify_thomson_n9_sharp.py",
]

FORBIDDEN_PARTS = {".lake", "toolchain", "__pycache__"}
FORBIDDEN_SUFFIXES = (".pyc", ".olean", ".ilean", ".so")


def source_safe(name):
    """Accept only workspace-relative source/data files, never build output."""
    normalized = name.replace("\\", "/")
    parts = normalized.split("/")
    return (normalized and not normalized.startswith("/") and ".." not in parts
            and not any(part in FORBIDDEN_PARTS for part in parts)
            and not normalized.endswith(FORBIDDEN_SUFFIXES))


LEAN_MODULES = [
    "Statement", "CoverageSoundness", "DomainCoverage", "TaylorTen",
    "LeafSemantics", "ReducedPSD", "Family", "CandidateMem", "HermiteFactor",
    "TransverseCoordinates", "Axioms", "Derivative", "Stationary",
    "SecondDerivative", "Minimum", "StrictConvex", "EnergyContinuity",
    "Applications", "ContactInner", "EnergyBounds", "DistanceValues", "GramBound",
    "EnergyValue", "EnergyForms", "PairDeriv", "EnergyGradient", "EnergyPath", "GradientZero", "EnergyOptimality", "EnergySymmetry", "Minimizer", "ThreePoint",
    "ThreePointBound", "TreeSemantics", "PSDSemantics", "FinalAssembly", "DomainChamber",
    "Interval", "IntervalTensor", "IntervalMul", "IntervalEval",
    "IntervalSum", "IntervalTensorEval", "LeafCert",
    "LocalCerts", "LocalLDLSemantics", "LocalLDLFactorization",
    "LocalLDLData", "LocalNonneg", "IntervalLocalOps", "LocalLDLReplay",
    "LocalVerification", "GramBoundary",
    "IntervalLinear", "LocalHessianBridge", "IntervalSparsePolynomial",
    "IntervalPowerReplay", "IntervalSparseDerivative",
    "LocalSparseHessianAAABase",
    "LocalSparseHessianAAAChunk00", "LocalSparseHessianAAAChunk01",
    "LocalSparseHessianAAAChunk02", "LocalSparseHessianAAAChunk03",
    "LocalSparseHessianAAAChunk04", "LocalSparseHessianAAAChunk05",
    "LocalSparseHessianAAAChunk06", "LocalSparseHessianAAAChunk07",
    "LocalSparseHessianAAA", "SparseTranslation", "TargetBinding", "TwoSourceBindings",
    "ChainBindings", "GatheredBinding", "MultiCornerBindings", "MultiCornerPowBindings", "MultiCornerPBindings", "GroupedT114", "Grouped124", "Grouped321", "Grouped329", "Grouped396", "Grouped403", "Grouped583", "Grouped590", "Grouped612", "Grouped647", "Grouped739", "Grouped103", "Grouped123", "Grouped224", "Grouped242", "Grouped312", "Grouped328", "Grouped463", "Grouped469", "Grouped517", "Grouped531", "Grouped547", "Grouped574", "Grouped615", "Grouped629", "GatheredTwoSource", "GatheredChain", "SingleSourceBindings", "FiveSourceBindings", "ChainRestBindings",
    "SevenSourceBindings",
    "EightSourceBindings",
    "NineSourceBindings",
    "TenSourceBindings", "ElevenSourceBindings",
    "TwelveSourceBindings", "ThirteenSourceBindings", "FourteenSourceBindings",
    "FifteenSourceBindings", "SixteenSourceBindings", "SeventeenSourceBindings",
]

# These are explicit because they are the review-facing reproducibility
# interface, rather than incidental files matching a broad directory glob.
PV_EXPLICIT_REQUIRED = (
    "export_local_lean.py", "local_lean_export_manifest.json",
    "export_local_ldl_replay.py", "local_ldl_replay_manifest.json",
    "verify_local_lean.py",
    "export_local_hessian_bridge.py", "local_hessian_bridge_manifest.json",
    "export_local_sparse_hessian.py", "local_sparse_hessian_manifest.json",
    "local_lean_verification.json", "local_lean_build_stamp.json",
)
PV_EXPLICIT_OPTIONAL = (
    "README_local_lean.md",
    "CONTINUATION_2026-10-19_zh.md",
    "AAA_PARTIAL_STATUS_2026-10-19_zh.md",
    "verify_aaa_shift_binding.py",
    "export_two_source_bindings.py", "export_chain_bindings.py", "export_multi_corner.py", "export_multi_pow.py", "export_multi_p.py",
)


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()

def validate_verification_report():
    """Refuse to pack a stale or failed Lean verification report.

    The report is evidence, not decoration: every source/artifact hash it
    records must still match disk, its module set must match the stamp, and the
    audit must cover the current 606+ directives.  This prevents the bundle from
    shipping an old PASS after the Lean tree has changed.
    """
    report_path = os.path.join(PV, "local_lean_verification.json")
    stamp_path = os.path.join(PV, "local_lean_build_stamp.json")
    if not os.path.isfile(report_path) or not os.path.isfile(stamp_path):
        raise SystemExit("missing local_lean_verification.json or local_lean_build_stamp.json; run verify_local_lean.py first")
    with open(report_path) as f:
        report = json.load(f)
    with open(stamp_path) as f:
        stamp = json.load(f)
    if report.get("status") != "LOCAL_LEAN_COMPILER_AXIOMS_AND_KERNEL_PASS":
        raise SystemExit("verification report is not PASS: " + repr(report.get("status")) + " / " + repr(report.get("error")))
    if int(report.get("axiom_audits", 0)) < 644:
        raise SystemExit("verification report has too few axiom audits: " + repr(report.get("axiom_audits")))
    modules = set(report.get("modules", []))
    required = {"ThomsonNine.LocalVerification", "ThomsonNine.Axioms", "ThomsonNine",
                "ThomsonNine.LocalSparseHessianAAA", "ThomsonNine.SparseTranslation",
                "ThomsonNine.LocalHessianBridge", "ThomsonNine.Family",
                "ThomsonNine.FinalAssembly"}
    missing = sorted(required - modules)
    if missing:
        raise SystemExit("verification report misses required modules: " + repr(missing))
    if set(stamp.get("modules", [])) != modules:
        raise SystemExit("build stamp module set differs from the verification report")
    for rel, expected in report.get("sources_sha256", {}).items():
        path = os.path.join(PV, rel)
        if not os.path.isfile(path) or sha256(path) != expected:
            raise SystemExit("verification source hash mismatch: " + rel)
    for rel, expected in report.get("artifacts_sha256", {}).items():
        path = os.path.join(PV, rel)
        if not os.path.isfile(path) or sha256(path) != expected:
            raise SystemExit("verification artifact hash mismatch: " + rel)
    for module, expected in stamp.get("sources", {}).items():
        rel = "formal/ThomsonNine.lean" if module == "ThomsonNine" else "formal/" + module.replace(".", "/") + ".lean"
        if report.get("sources_sha256", {}).get(rel) != expected:
            raise SystemExit("build stamp source differs from verification report: " + module)
    for module, expected in stamp.get("artifacts", {}).items():
        rel = "formal/.lake/build/lib/lean/" + module.replace(".", "/") + ".olean"
        if report.get("artifacts_sha256", {}).get(rel) != expected:
            raise SystemExit("build stamp artifact differs from verification report: " + module)
    return report


validate_verification_report()

# ---- file list -----------------------------------------------------------
files = []

def add_file(name, required=False):
    if source_safe(name) and os.path.isfile(os.path.join(ROOT, name)):
        files.append(name)
    elif required and source_safe(name):
        files.append(name)

# The canonical archive is the preferred seed.  If it is absent, preserve the
# existing v2 output instead of starting from an empty inherited file set.
seed_bundle = OLD_BUNDLE if os.path.exists(OLD_BUNDLE) else NEW_BUNDLE
if os.path.exists(seed_bundle):
    with zipfile.ZipFile(seed_bundle) as z:
        for name in z.namelist():
            if name in ("README_REVIEW.txt", "proof_work/SHARP_N9_REVIEW_MANIFEST.json"):
                continue
            if source_safe(name) and os.path.isfile(os.path.join(ROOT, name)):
                files.append(name)

# Root baseline entries are explicit and are always considered, even when a
# prior archive is unavailable.  They are rooted at proof_work/ in the bundle.
for name in BASELINE_ROOT_FILES:
    add_file(os.path.join("proof_work", name), required=True)

pv_names = []
for name in sorted(os.listdir(PV)):
    full = os.path.join(PV, name)
    if not os.path.isfile(full):
        continue
    if name in ("README_%s" % "",):  # never
        continue
    if name.startswith("README_") and name.endswith(".md"):
        pv_names.append(name)
    elif name in ("VALIDATION_STATUS_zh.md",):
        pv_names.append(name)
    elif name in ("sharp_root_inputs.json", "sharp_root_tree.jsonl",
                  "checker_exact.py", "sharded_checker.py",
                  "run_sharded_subprocess.py", "subprocess_shard_worker.py",
                  "test_checker_exact.py", "test_checker_supplemental.py",
                  "test_sharded_checker.py", "test_subprocess_transport.py",
                  "audit_independent_result.py", "audit_sharded_publication.py",
                  "check_known_failed_kernel.py", "check_model_input_binding.py",
                  "finalize_independent_run.py", "independent_delivery_manifest.json",
                  "independent_publication_audit.log",
                  "SUBMISSION_MANUSCRIPT_en.md", "SUBMISSION_CHECKLIST_zh.md",
                  "build_review_bundle.py"):
        pv_names.append(name)
    elif name.startswith("independent_") and name.endswith(".json"):
        if name.startswith("independent_architecture"):
            continue
        pv_names.append(name)
for name in PV_EXPLICIT_REQUIRED:
    add_file(os.path.join("proof_work", "publication_validation", name), required=True)
for name in PV_EXPLICIT_OPTIONAL:
    if os.path.isfile(os.path.join(PV, name)):
        add_file(os.path.join("proof_work", "publication_validation", name))
# Verification logs are generated by the serial verifier; include only log
# files, never a broad directory walk that could pull caches into the bundle.
log_dir = os.path.join(PV, "local_lean_verification_logs")
if os.path.isdir(log_dir):
    for name in sorted(os.listdir(log_dir)):
        if name.endswith(".log") and os.path.isfile(os.path.join(log_dir, name)):
            pv_names.append(os.path.join("local_lean_verification_logs", name))
for name in pv_names:
    add_file(os.path.join("proof_work", "publication_validation", name))

for n in ("aggregate.json", "manifest.json",
          "publication_reaggregation/aggregate.json",
          "subprocess-execution-v1.json", "subprocess_wrapper_launch.json"):
    add_file(os.path.join("proof_work", "publication_validation",
                          "sharded_run_v1", n))

for m in LEAN_MODULES:
    add_file(os.path.join("proof_work", "publication_validation", "formal",
                          "ThomsonNine", m + ".lean"), required=True)
for n in ("README_build.md", "build_direct.sh", "lakefile.toml", "lean-toolchain",
          "lake-manifest.json", "ThomsonNine.lean"):
    add_file(os.path.join("proof_work", "publication_validation", "formal", n),
             required=True)

# Deduplicate and reject any inherited entry that was not source-safe.
files = sorted(set(f for f in files if source_safe(f)))
missing = [f for f in files if not os.path.exists(os.path.join(ROOT, f))]
if missing:
    raise SystemExit("missing files:\n" + "\n".join(missing))

manifest_files = {}
for f in files:
    p = os.path.join(ROOT, f)
    manifest_files[f] = {"sha256": sha256(p), "bytes": os.path.getsize(p)}

readme = """Thomson n=9 proof candidate -- review bundle (regenerated)
===========================================================

SCOPE.  This package records a locally closed computer-assisted proof chain for
the frozen statement described in THOMSON_N9_PROOF_CANDIDATE_zh.md.  It is a
proof CANDIDATE: it has not been externally peer reviewed, the nine-point
energy theorem has not been formally verified, and no statement about the
global uniqueness of the minimizer is made.

START HERE
  1. proof_work/THOMSON_N9_PROOF_CANDIDATE_zh.md   (frozen statement + proof)
  2. proof_work/THOMSON_N9_CURRENT_zh.md           (full technical record)
  3. proof_work/publication_validation/VALIDATION_STATUS_zh.md
                                                   (what has been verified)
  4. proof_work/publication_validation/README_independent_checker.md
  5. proof_work/publication_validation/SUBMISSION_MANUSCRIPT_en.md
  6. proof_work/publication_validation/SUBMISSION_CHECKLIST_zh.md

REQUIREMENTS.  Python 3, numpy, sympy; a little-endian 64-bit machine and GCC
with signed __int128 for the historical shared objects.  The independent
checker itself is pure Python stdlib.

(T1) INDEPENDENT EXACT ARITHMETIC CHECK (fresh recomputation of the whole tree)
  python3 -u proof_work/publication_validation/test_checker_exact.py
  python3 -u proof_work/publication_validation/checker_exact.py \\
    --inputs proof_work/publication_validation/sharp_root_inputs.json \\
    --tree proof_work/publication_validation/sharp_root_tree.jsonl \\
    --output proof_work/publication_validation/independent_full_result.json \\
    --expected-input-sha256 3dd4ba639e78cabaa2c3a8182db3724545751ade50635e6d542067338b281066
  Recorded sharded replay: proof_work/publication_validation/sharded_run_v1/
  (154 shards, 136125 nodes, 68063 leaves, pending=0).

(T2) NEGATIVE / FAILURE-PROPAGATION TESTS
  python3 -u proof_work/publication_validation/test_checker_exact.py
  python3 -u proof_work/publication_validation/test_checker_supplemental.py

(T3) HISTORICAL FULL REPLAY (same implementation, not an independent kernel)
  OPENBLAS_NUM_THREADS=1 python3 proof_work/verify_thomson_n9_sharp.py \\
    --outdir proof_work/new_external_replay

(T4) LEAN 4 SOURCES (partial formalization; final theorem NOT formalized)
  proof_work/publication_validation/formal/README_build.md explains the pinned
  Lean 4.34.1 / Mathlib d13f23b7 toolchain.  The modules Statement, Family,
  CandidateMem, DomainCoverage, LeafSemantics, Derivative, Stationary,
  SecondDerivative, Minimum, StrictConvex, EnergyContinuity, Applications and
  ContactInner compile; the axiom audit and the coverage lemmas are included.
  Applications.lean proves isometry invariance, the inner-product form of the
  energy and a crude unconditional lower bound; ContactInner.lean computes the
  six candidate-family inner products A, B, C, D, F, G.  Stationary.lean formalizes the endpoint signs, continuity and the
  existence of the family stationary point; SecondDerivative.lean formalizes
  positivity of the second derivative and Rolle-theorem uniqueness
  (exists_unique_stationary_point); Minimum.lean formalizes strict monotonicity
  of the derivative and the unique strict global minimum of the family energy
  (exists_unique_familyEnergy_min); EnergyPath.lean proves the multi-point path
  derivative, GradientZero.lean the equivalence of vanishing gradient and
  stationarity, EnergyOptimality.lean first-order optimality, EnergySymmetry.lean
  relabeling invariance, and Minimizer.lean the existence of a global minimizer
  (exists_global_minimizer, exists_global_minimizer_lt_26).  ThreePoint.lean is
  an attributed adaptation of the Bachoc-Vallentin three-point positivity from
  the N=7 Lean project (quad_Y3_nonneg, bv_positivity); its general-PSD pairing
  lemma is explicitly deferred.  ThreePointBound.lean ports the reduced-kernel
  combinatorics (dsum, Rs, dsum_Rs, dsum_H, Rk, sum4_swap) and the exact
  three_point_identity from the same project; three_point_bound still awaits the
  PSD moment inequality matDot_moment_nonneg.  FinalAssembly.lean proves the frozen claim is
  equivalent to the global lower bound (thomsonNineClaim_iff_global_lower_bound);
  the unformalized part is exactly that bound.  DomainChamber.lean sorts any
  physical inner-product triple into the ordered chamber with the Gram constraint
  preserved.  There is no Lean proof of the nine-point energy
  statement, and `sorry`/`axiom` are absent from the sources. The independent
  `verify_aaa_shift_binding.py` replays the formal three-axis interval
  algorithm exactly and checks 807/807 archived shifted-coefficient targets.
  `TwoSourceBindings.lean` and `ChainBindings.lean` prove 32 two-source plus
  54 three/four-source target interval bounds (together with TargetBinding
  .t126, 87 of the 807 targets), and `MultiCornerBindings.lean` adds 15
  five-source multi-axis delta≤1 targets and `MultiCornerPowBindings.lean` adds 9
  delta≥2 five-source multi-axis targets, `MultiCornerPBindings.lean` adds 13
  eight-source multi-axis targets whose per-source intervals are contained; for 254 of the 807 targets; these are
  interval arithmetic certificates.  `GatheredBinding.lean` additionally
  proves that the full 807-term gathered coefficient for `.t126` equals its two
  contributing binomial terms and lies in the archived interval.

(T5) LEAN LOCAL CERTIFICATE (conditional; NOT the global theorem)
  The 12-class LDL replay and the AAA H00 sparse Hessian certificate are
  compiled and checked by the unified local verifier:
  python3 -B proof_work/publication_validation/verify_local_lean.py --adopt-build
  Recorded result (2026-10-20 14:08 UTC): status
  LOCAL_LEAN_COMPILER_AXIOMS_AND_KERNEL_PASS, 644 #print axioms directives,
  90-module closure, and leanchecker ThomsonNine.LocalVerification exit 0.
  See proof_work/publication_validation/local_lean_verification.json and
  local_lean_build_stamp.json.  The AAA theorem assumes a fixed real
  coefficient family in coefficientInterval and a point in relativeBox; its
  binding to the true residual/shifted coefficients is NOT proved.  Other
  classes, the 45 contact equations, the 68,063-leaf coverage instantiation,
  and the final ThomsonNineClaim remain unformalized.  This is a local,
  conditional certificate, not an external review or a solution of the
  nine-point problem.

CAVEATS.  The manuscript-style links in THOMSON_N9_CURRENT_zh.md use original
absolute paths; open the corresponding extracted files instead.  The full
replay uses the same implementation, not an independent proof checker.  Files
were hashed at packing time; see proof_work/SHARP_N9_REVIEW_MANIFEST.json.

Generated %s UTC.
""" % datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M")

manifest = {
    "status": "PUBLICATION_CANDIDATE_PACKAGE_UNREVIEWED",
    "scope": ("Frozen Thomson n=9 proof candidate, exact arithmetic evidence, "
              "independent exact checker and recorded results, coverage-tree "
              "export, and Lean 4 sources. Not peer reviewed, not formally "
              "verified as a whole; no global uniqueness claim."),
    "generated_utc": datetime.now(timezone.utc).isoformat(),
    "file_count": len(files) + 2,
    "files": manifest_files,
}

with open(MANIFEST, "w", encoding="utf-8") as f:
    json.dump(manifest, f, ensure_ascii=False, indent=2, sort_keys=True)

# The canonical baseline archive is intentionally never moved or deleted.
with zipfile.ZipFile(NEW_BUNDLE, "w", zipfile.ZIP_DEFLATED, compresslevel=6) as z:
    z.writestr("README_REVIEW.txt", readme)
    z.writestr("proof_work/SHARP_N9_REVIEW_MANIFEST.json",
               json.dumps(manifest, ensure_ascii=False, indent=2, sort_keys=True))
    for f in files:
        z.write(os.path.join(ROOT, f), arcname=f)

print("files:", len(files) + 2)
print("bundle bytes:", os.path.getsize(NEW_BUNDLE))
