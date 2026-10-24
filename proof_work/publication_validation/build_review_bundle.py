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
from verify_local_lean import (kernel_coverage, local_closure, LOCAL_ROOT,
                               ROOT_MODULE, AUDIT_MODULE)

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
PROOF = os.path.join(ROOT, "proof_work")
PV = os.path.join(PROOF, "publication_validation")
EXPECTED = json.load(open(os.path.join(PV, "local_lean_expected.json")))
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


PV_EXPLICIT_REQUIRED = (
    "export_local_lean.py", "local_lean_export_manifest.json",
    "export_local_ldl_replay.py", "local_ldl_replay_manifest.json",
    "verify_local_lean.py", "export_grouped_generic.py",
    "CONTINUATION_2026-10-21_zh.md", "local_lean_expected.json",
    "NEXT13_INTEGRATION_zh.md",
    "OPTIMIZATION_2026-10-21_zh.md", "grouped_optimization_benchmark.json",
    "export_grouped_compact.py", "benchmark_grouped_compact.py",
    "compact_grouped_manifest.json", "compact_inputs/GroupedT114.lean",
    "COMPACT45_INTEGRATION_2026-10-22_zh.md", "compact_grouped_result.json",
    "test_compact_validation.py",
    "export_aaa_grouped_data.py", "aaa_grouped_data_manifest.json",
    "GROUPED_BRIDGE_2026-10-22_zh.md", "aaa_grouped_bridge_result.json",
    "check_cached_grouped_numeric.py", "aaa_cached_grouped_feasibility.json",
    "export_aaa_fixed_tree.py", "aaa_fixed_tree_manifest.json",
    "fixed_inputs/AAAFixedData.lean.in", "fixed_inputs/AAAIndexedData.lean.in",
    "fixed_inputs/AAATreeData.lean.in", "fixed_inputs/baseline_targets.json",
    "FIXED_TREE_807_2026-10-22_zh.md", "aaa_fixed_tree_result.json",
    "export_semantic_inputs.py", "semantic_inputs_manifest.json",
    "semantic_inputs/AAASupport.lean.in", "semantic_inputs/ActualHermite.lean.in",
    "semantic_inputs/RadiusEndpoint.lean.in", "semantic_inputs/radius_inputs.json",
    "independent_kernel_refined_result.json",
    "SEMANTIC_RADIUS_HERMITE_2026-10-22_zh.md", "semantic_radius_hermite_result.json",
    "export_hermite_coefficients.py", "hermite_coefficients_manifest.json",
    "export_actual_construction.py", "actual_construction_manifest.json",
    "ACTUAL_CONSTRUCTION_2026-10-22_zh.md", "actual_construction_result.json",
    "hermite_inputs/ActualHermiteScalar.lean.in", "hermite_inputs/ActualHermiteBounds.lean.in",
    "hermite_inputs/ActualQuotientBernstein.lean.in",
    "ACTUAL_HERMITE_MINORANT_2026-10-22_zh.md", "actual_hermite_minorant_result.json",
    "export_local_hessian_bridge.py", "local_hessian_bridge_manifest.json",
    "export_local_sparse_hessian.py", "local_sparse_hessian_manifest.json",
    "local_lean_verification.json", "local_lean_build_stamp.json",
    "GENERIC_CERTIFICATE_FRAMEWORK_ROADMAP_zh.md",
    "GENERIC_FRAMEWORK_VALIDATION_2026-10-24_zh.md",
    "GENERIC_CERTIFICATE_PIPELINE_zh.md",
    "N9_ADAPTER_VALIDATION_2026-10-24_zh.md",
    "CROSS_INSTANCE_ADAPTER_AUDIT_2026-10-24_zh.md",
    "run_certificate_pipeline.py",
    "certificate_manifests/n9_structured.json",
    "certificate_manifests/n9_structured_run.json",
    "certificate_manifests/n10_candidate_only.json",
    "certificate_manifests/n9_global_claim.json",
    "certificate_manifests/n9_global_claim_run.json",
    "certificate_manifests/n10_candidate_only_run.json",
    "CROSS_INSTANCE_REUSE_AUDIT_2026-10-23_zh.md",
    "N10_PRIORITY_SCREEN_2026-10-23_zh.md",
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

PV_EXPLICIT_REQUIRED += tuple(item['template'] for item in json.load(open(os.path.join(PV, 'actual_construction_manifest.json')))['files'].values())
PV_EXPLICIT_REQUIRED += tuple(item['formal'] for item in json.load(open(os.path.join(PV, 'actual_construction_manifest.json')))['files'].values())
PACKED_PATH = os.path.join(PV, 'packed_coverage_manifest.json')
PACKED = json.load(open(PACKED_PATH)) if os.path.exists(PACKED_PATH) else None
if PACKED:
    PV_EXPLICIT_REQUIRED += ('export_packed_coverage.py', 'packed_coverage_manifest.json')
    PV_EXPLICIT_REQUIRED += tuple(item['template'] for item in PACKED['files'].values())
    if EXPECTED.get('global_theorem'):
        PV_EXPLICIT_REQUIRED += ('GLOBAL_THEOREM_2026-10-22_zh.md', 'global_theorem_result.json')

def validate_verification_report():
    """Refuse to pack a stale or failed Lean verification report.

    The report is evidence, not decoration: every source/artifact hash it
    records must still match disk, its module set must match the stamp, and the
    audit must match the registered expectations and the full fresh replay. This prevents the bundle from
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
    if EXPECTED.get('global_theorem'):
        theorem = report.get('frozen_global_theorem', {})
        statement_hash = sha256(os.path.join(PV, 'formal/ThomsonNine/Statement.lean'))
        if (theorem.get('declaration') != EXPECTED['global_theorem']
                or theorem.get('type') != 'ThomsonNine.ThomsonNineClaim'
                or theorem.get('statement_sha256') != statement_hash
                or EXPECTED.get('frozen_statement_sha256') != statement_hash
                or theorem.get('compiler_axioms_and_complete_fresh_kernel_pass') is not True):
            raise SystemExit('missing verified frozen global theorem')
    if int(report.get("axiom_audits", 0)) != EXPECTED["axiom_audits"]:
        raise SystemExit("verification report has an unexpected axiom audit count: " + repr(report.get("axiom_audits")))
    modules = set(report.get("modules", []))
    required = {"ThomsonNine.LocalVerification", "ThomsonNine.Axioms", "ThomsonNine",
                "ThomsonNine.LocalSparseHessianAAA", "ThomsonNine.SparseTranslation",
                "ThomsonNine.LocalHessianBridge", "ThomsonNine.Family",
                "ThomsonNine.FinalAssembly"}
    required.update(EXPECTED["required_root_modules"])
    if len(modules) != EXPECTED["modules"]:
        raise SystemExit("module closure differs from local_lean_expected.json")
    coverage = report.get("conditional_coverage", {})
    if coverage.get("covered") != len(EXPECTED["conditional_targets"]) or coverage.get("total") != EXPECTED["total_targets"]:
        raise SystemExit("conditional coverage differs from local_lean_expected.json")
    if coverage.get("targets") != EXPECTED["conditional_targets"]:
        raise SystemExit("coverage target list is missing or duplicated")
    if set(report.get("root_modules", [])) != set(EXPECTED["required_root_modules"]):
        raise SystemExit("formal root closure differs from registered expectations")
    expected_hash = sha256(os.path.join(PV, "local_lean_expected.json"))
    if report.get("expected_configuration_sha256") != expected_hash or stamp.get("expected_configuration_sha256") != expected_hash:
        raise SystemExit("verification expectations do not match report and stamp")
    actual_local = local_closure(LOCAL_ROOT)
    actual_root = local_closure(ROOT_MODULE)
    actual_all = actual_local | actual_root | local_closure(AUDIT_MODULE)
    actual_coverage = kernel_coverage(actual_local, actual_root, actual_all)
    if EXPECTED.get('kernel_replay_policy') != actual_coverage['policy']:
        raise SystemExit("unexpected registered kernel replay policy")
    if actual_all != modules or set(report.get("root_modules", [])) != actual_root:
        raise SystemExit("reported module sets differ from actual imports")
    if report.get("local_verification_modules") != sorted(actual_local):
        raise SystemExit("reported fresh closure differs from actual imports")
    if report.get("kernel_replay_coverage") != actual_coverage or stamp.get("kernel_replay_coverage") != actual_coverage:
        raise SystemExit("fresh replay does not cover every proof-bearing module")
    if report.get("kernel_replay_modules") != [LOCAL_ROOT] or stamp.get("kernel_replay_modules") != [LOCAL_ROOT]:
        raise SystemExit("unexpected fresh replay roots")
    stages = {stage["name"]: stage for stage in report.get("stages", [])}
    if len(stages) != len(report.get("stages", [])):
        raise SystemExit("duplicate verification stages")
    for name in ("validation_self_tests", "export_data", "export_replay", "export_hessian_bridge", "export_sparse_hessian",
                 "export_compact_grouped", "export_aaa_grouped_data", "export_aaa_fixed_tree", "export_semantic_inputs", "export_hermite_coefficients", "export_actual_construction", "root", "build_ThomsonNine.LocalVerification",
                 "axioms", "kernel_local_fresh"):
        stage = stages.get(name, {})
        if stage.get("exit_code") != 0:
            raise SystemExit("missing successful verification stage: " + name)
        log = os.path.join(PV, stage.get("log", ""))
        if not os.path.isfile(log) or sha256(log) != stage.get("log_sha256"):
            raise SystemExit("verification log hash mismatch: " + name)
    if PACKED:
        stage = stages.get('export_packed_coverage', {})
        if stage.get('exit_code') != 0:
            raise SystemExit('missing successful packed coverage export check')
        log = os.path.join(PV, stage.get('log', ''))
        if not os.path.isfile(log) or sha256(log) != stage.get('log_sha256'):
            raise SystemExit('packed coverage export log hash mismatch')
    for name, module in (("kernel_local_fresh", LOCAL_ROOT),):
        if stages[name].get("command", [])[1:] != ["--fresh", module]:
            raise SystemExit("fresh replay command mismatch: " + name)
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
        rel = "formal/" + module.replace(".", "/") + ".lean"
        if report.get("sources_sha256", {}).get(rel) != expected:
            raise SystemExit("build stamp source differs from verification report: " + module)
    for module, expected in stamp.get("artifacts", {}).items():
        rel = "formal/.lake/build/lib/lean/" + module.replace(".", "/") + ".olean"
        if report.get("artifacts_sha256", {}).get(rel) != expected:
            raise SystemExit("build stamp artifact differs from verification report: " + module)
    return report


verification = validate_verification_report()
LEAN_SOURCES = [m.replace(".", "/") + '.lean' for m in verification["modules"]]

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
            if name.startswith("proof_work/publication_validation/local_lean_verification_logs/"):
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
for source_manifest in [json.load(open(os.path.join(PV, 'actual_construction_manifest.json'))), PACKED]:
    if source_manifest is None:
        continue
    for relative, expected_hash in source_manifest['input_sha256'].items():
        absolute = os.path.realpath(os.path.join(PV, relative))
        if os.path.commonpath([absolute, os.path.realpath(PROOF)]) != os.path.realpath(PROOF):
            raise SystemExit('bound input escapes proof directory: ' + relative)
        if not os.path.isfile(absolute) or sha256(absolute) != expected_hash:
            raise SystemExit('bound input hash changed: ' + relative)
        add_file(os.path.relpath(absolute, ROOT), required=True)
for name in PV_EXPLICIT_OPTIONAL:
    if os.path.isfile(os.path.join(PV, name)):
        add_file(os.path.join("proof_work", "publication_validation", name))
# Include only logs bound to stages in the current PASS report.
for stage in verification["stages"]:
    pv_names.append(stage["log"])
for name in pv_names:
    add_file(os.path.join("proof_work", "publication_validation", name))

for n in ("aggregate.json", "manifest.json",
          "publication_reaggregation/aggregate.json",
          "subprocess-execution-v1.json", "subprocess_wrapper_launch.json"):
    add_file(os.path.join("proof_work", "publication_validation",
                          "sharded_run_v1", n))

for relative in LEAN_SOURCES:
    add_file(os.path.join("proof_work", "publication_validation", "formal", relative), required=True)
for n in ("README_build.md", "build_direct.sh", "lakefile.toml", "lean-toolchain",
          "lake-manifest.json", "lake-manifest.original_git.json", "ThomsonNine.lean",
          "ThomsonCertificate/GenericBernstein.lean",
          "ThomsonCertificate/GenericCoverage.lean",
          "ThomsonCertificate/GenericFramework.lean",
          "ThomsonCertificate/GenericCertificate.lean",
          "ThomsonCertificate/GenericLowerBound.lean",
          "ThomsonCertificate/GenericMinimum.lean",
          "ThomsonCertificate/GenericUniqueness.lean",
          "ThomsonCertificate/GenericPSD.lean",
          "ThomsonCertificate/ThomsonNineAdapter.lean",
          "ThomsonCertificate/ThomsonNineMinimumAdapter.lean",
          "ThomsonCertificate/ThomsonNineStructuredAdapter.lean"):
    add_file(os.path.join("proof_work", "publication_validation", "formal", n),
             required=True)

# Include the publication manuscript as a reviewable artifact.  Keep the
# selection explicit so LaTeX auxiliary files and local build logs do not
# silently enter the canonical source archive.
for name in ("paper/main.tex", "paper/README.md", "paper/main.pdf",
             "paper/THOMSON_N9_MANUSCRIPT_SOURCE.zip",
             "paper/COVER_LETTER_TEMPLATE.md"):
    add_file(name, required=True)

# Deduplicate and reject any inherited entry that was not source-safe.
files = sorted(set(f for f in files if source_safe(f)))
missing = [f for f in files if not os.path.exists(os.path.join(ROOT, f))]
if missing:
    raise SystemExit("missing files:\n" + "\n".join(missing))

manifest_files = {}
for f in files:
    p = os.path.join(ROOT, f)
    manifest_files[f] = {"sha256": sha256(p), "bytes": os.path.getsize(p)}

readme = f"""Thomson n=9 proof candidate -- review bundle
===========================================

SCOPE: Partial, conditional Lean formalization and recorded exact-arithmetic
checks. The final ThomsonNineClaim is UNPROVED. No external independent
verification or peer review of the whole theorem is claimed. Global uniqueness
of the minimizer is also unproved.

START HERE
  proof_work/publication_validation/SEMANTIC_RADIUS_HERMITE_2026-10-22_zh.md
  proof_work/publication_validation/FIXED_TREE_807_2026-10-22_zh.md
  proof_work/publication_validation/GROUPED_BRIDGE_2026-10-22_zh.md
  proof_work/publication_validation/COMPACT45_INTEGRATION_2026-10-22_zh.md
  proof_work/publication_validation/NEXT13_INTEGRATION_zh.md
  proof_work/publication_validation/CONTINUATION_2026-10-21_zh.md
  proof_work/publication_validation/VALIDATION_STATUS_zh.md
  proof_work/publication_validation/README_local_lean.md
  proof_work/publication_validation/formal/README_build.md
  proof_work/THOMSON_N9_PROOF_CANDIDATE_zh.md

CURRENT LEAN CHECK
  Status: {verification['status']}
  Lean 4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
  {len(verification["modules"])} local modules, {verification["axiom_audits"]} distinct #print axioms directives.
  Allowed axioms: propext, Classical.choice, Quot.sound; no sorryAx.
  Fresh replay: leanchecker --fresh ThomsonNine.LocalVerification
  The entire ThomsonNine root closure is contained in this fresh replay.
  Axioms is separately compiled and restricted to imports/axiom-print directives.
  leanchecker uses Lean's own kernel; it is NOT an external independent verifier.
  LocalVerification imports the formal root, including all integrated grouped
  certificates. Exact expected counts and targets are in local_lean_expected.json.
  45 grouped modules now use compact proofs, preserving their statements and
  interval definitions. See compact_grouped_result.json for measured sizes.
  Fixed integer intervals and a shared grouping tree now check all 807 archived
  coefficient bounds using ordinary kernel reduction. The all_gathered theorem
  supplies the full coefficient premises for the existing AAA H00 certificate.
  Actual N/contact33/190X/PSD/F/c construction and physical R_H identification
  now discharge all807 archived source interval premises. All12 actual residual
  contact values and the weighted moment value/derivative are proved.
  The full45 contact equations additionally compile in the isolated workspace;
  they are outside this unified checkpoint. The final global theorem remains open.

CONDITIONAL COVERAGE
  {verification["conditional_coverage"]["covered"]} DISTINCT gathered-coefficient targets out of 807.
  Historical baseline: 279 declarations represented only 272 distinct targets;
  seven targets had duplicate declarations. The prior seven-target integration
  gave 286 declarations and 279 distinct targets. The subsequent thirteen-target
  integration gave 299 declarations and 292 distinct targets.
  All 21 eleven-source, three-axis grouped targets are integrated.
  The previous coefficient batch added t597, t381/t409/t653, and all nine thirteen-source multi-axis
  targets (286, 334, 703, 388, 402, 456, 475, 589, 596).
  This does not identify the source coefficient family with the true residual.

REPRODUCE
  Set LEAN_BIN_DIR to the pinned toolchain's bin directory (or put it on PATH).
  Keep/reuse formal/.lake; see formal/README_build.md for dependency caches.
  python3 -B proof_work/publication_validation/verify_local_lean.py
  A matching prior PASS stamp permits --reuse-local-build. Explicit adoption
  of externally compiled artifacts uses --adopt-build and is reported as such.
  After PASS: python3 proof_work/publication_validation/build_review_bundle.py
  The builder checks current source/artifact/log hashes and refuses stale PASS.

HISTORICAL EXACT-ARITHMETIC EVIDENCE
  The independent Python int/Fraction checker, archived tree (136125 nodes,
  68063 leaves), recorded sharded results, and tests are included. This update
  did not rerun the entire tree. See README_independent_checker.md for details.

OPEN PROOF OBLIGATIONS
  Actual residual/shifted-coefficient binding; complete Hessians for the other
  classes; 45 contact equations and rank-33/W compatibility; instantiation of
  the 68063-leaf coverage; final energy lower bound and ThomsonNineClaim.

INTEGRITY
  proof_work/SHARP_N9_REVIEW_MANIFEST.json records every payload file's SHA-256
  and size. Build caches and toolchain binaries are intentionally excluded.
  Generated {datetime.now(timezone.utc).isoformat()} UTC.
"""

if verification.get('frozen_global_theorem'):
    readme = f"""Thomson n=9 -- frozen global theorem, Lean proof and review sources
==================================================================

The exact, unchanged ThomsonNineClaim is proved by
  ThomsonNine.thomsonNineClaim_proved : ThomsonNine.ThomsonNineClaim

The theorem states that the specified three-ring candidate at the unique
stationary radius r in (0,1) lies on the unit sphere, has the stated energy,
and has energy no greater than every injective nine-point sphere configuration.
It does not state that all minimizing configurations are congruent.

START HERE
  proof_work/publication_validation/GLOBAL_THEOREM_2026-10-22_zh.md
  proof_work/publication_validation/formal/ThomsonNine/Statement.lean
  proof_work/publication_validation/formal/MainCoverage/Final.lean
  proof_work/publication_validation/local_lean_verification.json
  proof_work/publication_validation/README_local_lean.md

VERIFICATION
  {verification['status']}
  {len(verification['modules'])} modules in the complete import closure.
  {verification['axiom_audits']} distinct, ordered axiom audits.
  Only propext, Classical.choice and Quot.sound are allowed; no sorryAx.
  All 807 archived coefficient targets and all 12 actual local neighborhoods
  are connected to the actual residual. The archived 136125-node tree has
  68063 leaves and is checked through 498 certified frontier subtrees.
  Complete replay: leanchecker --fresh ThomsonNine.LocalVerification
  The formal root and final theorem are contained in that replay closure.
  Original module names and exact existing compiler artifacts were explicitly
  adopted, then the entire imported proof was replayed in a fresh kernel.

Lean 4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 are pinned.
leanchecker uses Lean's own kernel. This is not an external independent
implementation or peer review. Earlier Python exact-arithmetic evidence is
included with its original scope; it is not a substitute for that distinction.

REPRODUCE
  Set LEAN_BIN_DIR to the pinned Lean bin directory, preserve formal/.lake,
  then run python3 -B proof_work/publication_validation/verify_local_lean.py
  A prior matching PASS stamp permits --reuse-local-build. --adopt-build
  explicitly adopts existing artifacts with source/artifact hash checks.
  The verifier discovers owned modules through packed_coverage_manifest.json,
  checks source templates and input hashes, rejects unregistered local imports,
  audits all declared conclusions, and runs one complete fresh kernel replay.
  After PASS: python3 proof_work/publication_validation/build_review_bundle.py

The earlier ThomsonNine/Construction copies remain as historical reproducibility
sources. They are superseded by the original-name modules and are not imported
alongside them. Exact current import counts are in local_lean_expected.json.
Progress documents dated before the final theorem describe historical stages.

INTEGRITY
  proof_work/SHARP_N9_REVIEW_MANIFEST.json hashes every payload file.
  Compiled caches and toolchain binaries are excluded from this source archive.
  Generated {datetime.now(timezone.utc).isoformat()} UTC.
"""

manifest = {
    "status": "PUBLICATION_CANDIDATE_PACKAGE_UNREVIEWED",
    "scope": ("Frozen Thomson n=9 proof candidate, exact arithmetic evidence, "
              "independent exact checker and recorded results, coverage-tree "
              "export, and Lean 4 sources. Not peer reviewed, not formally "
              "verified as a whole; no global uniqueness claim."),
    "generated_utc": datetime.now(timezone.utc).isoformat(),
    "file_count": len(files) + 2,
    "lean_verification": {"status": verification["status"], "modules": len(verification["modules"]),
                          "axiom_audits": verification["axiom_audits"],
                          "distinct_conditional_targets": verification["conditional_coverage"]["covered"],
                          "total_targets": 807, "external_independent_verification": False},
    "files": manifest_files,
}
if verification.get('frozen_global_theorem'):
    manifest['scope'] = ('Unchanged frozen ThomsonNineClaim proved in Lean; complete compiler, axiom and fresh Lean-kernel replay PASS. '
                         'No external independent verification or peer review; no theorem of congruence uniqueness of all minimizers.')
    manifest['lean_verification']['frozen_global_theorem'] = verification['frozen_global_theorem']

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
