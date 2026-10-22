#!/usr/bin/env python3
"""Sequential compiler, axiom, and Lean built-in kernel validation of local work.

The verifier discovers the explicitly owned local
import closure of `LocalVerification`, `Axioms`, and the root module, parses
imports strictly, audits every axiom-print directive in `Axioms.lean`, rejects
proof escapes in all reachable local sources, and runs Lean built-in
`leanchecker --fresh` once on the complete LocalVerification import closure.
The formal root must be contained in that closure. Axioms is compiled and
strictly restricted to imports and axiom-print directives.

Reuse is hash-stamped: `--reuse-local-build` accepts only artifacts bound to a
stamp written by a prior PASS.  `--adopt-build` is the explicit first-run mode
for a build produced outside this script (e.g. the detached AAA split build);
it checks source/artifact mtimes and hashes before writing a stamp, but it is a
trust decision and is reported as such.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

PV = Path(__file__).resolve().parent
FORMAL = PV / 'formal'
def toolchain_bin():
    explicit = os.environ.get('LEAN_BIN_DIR')
    if explicit:
        return Path(explicit).resolve()
    lean = shutil.which('lean')
    if lean:
        return Path(lean).resolve().parent
    arch = os.uname().machine
    archive = 'lean-4.34.1-linux_aarch64' if arch == 'aarch64' else 'lean-4.34.1-linux'
    return PV / 'toolchain' / archive / 'bin'


BIN = toolchain_bin()
OUT = FORMAL / '.lake/build/lib/lean'
LOCAL_ROOT = 'ThomsonNine.LocalVerification'
AUDIT_MODULE = 'ThomsonNine.Axioms'
ROOT_MODULE = 'ThomsonNine'
REPORT = PV / 'local_lean_verification.json'
STAMP = PV / 'local_lean_build_stamp.json'
LOGS = PV / 'local_lean_verification_logs'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
EXPECTED_PATH = PV / 'local_lean_expected.json'
EXPECTED = json.loads(EXPECTED_PATH.read_text())
MIN_AXIOM_AUDITS = EXPECTED['axiom_audits']
NEW_GROUPED_TARGETS = tuple(EXPECTED['required_grouped_targets'])
REPLAY_POLICY = 'single_fresh_local_closure_v1'

KEY_AUDITS = {
    'ThomsonNine.Family.candidate_eq_p',
    'ThomsonNine.Family.energy_candidate',
    'ThomsonNine.Family.exists_unique_stationary_point',
    'ThomsonNine.Family.exists_unique_familyEnergy_min',
    'ThomsonNine.Coverage.coverage_sound_on_domain',
    'ThomsonNine.thomsonNineClaim_iff_global_lower_bound',
    'ThomsonNine.Interval.RatInterval.evalTensor_sound',
    'ThomsonNine.LocalLDL.Replay.psd_00_AAA',
    'ThomsonNine.LocalLDL.Replay.psd_11_GDF',
    'ThomsonNine.LocalLDL.HessianBridge.psd_original_00_AAA',
    'ThomsonNine.LocalLDL.HessianBridge.psd_original_11_GDF',
    'ThomsonNine.Interval.SparsePolynomial.axisDeriv_axisDeriv_eval',
    'ThomsonNine.LocalSparseHessianAAA.actual_h00_mem',
    'ThomsonNine.Interval.SparsePolynomial.expandedCoefficient_mem',
}

KEY_AUDITS.update(f'ThomsonNine.Grouped{i}.t{i}_gathered' for i in NEW_GROUPED_TARGETS)
KEY_AUDITS.update({
    'ThomsonNine.Interval.SparsePolynomial.Grouped.groupedCoeff_eq_gatheredOn',
    'ThomsonNine.Interval.SparsePolynomial.Grouped.groupedInterval_mem',
    'ThomsonNine.AAAGroupedData.computed_mem_gathered',
    'ThomsonNine.AAAGroupedPilot.bounds000',
    'ThomsonNine.AAAGroupedPilot.t000_gathered',
    'ThomsonNine.FixedInterval.mem_mul',
    'ThomsonNine.FixedInterval.treeCoeff_eq',
    'ThomsonNine.FixedInterval.treeCompute_mem',
    'ThomsonNine.AAATreeData.computed_mem',
    'ThomsonNine.AAAFixedComplete.bounds',
    'ThomsonNine.AAAFixedComplete.all_gathered',
    'ThomsonNine.AAAFixedComplete.gathered_h00_mem',
    'ThomsonNine.Interval.SparsePolynomial.Collected.eval_shift_collected',
    'ThomsonNine.AAASupport.support_lower_closed',
    'ThomsonNine.AAACollected.eval_shift_gathered',
    'ThomsonNine.AAACollected.source_h00_mem',
    'ThomsonNine.RefinedRadius.radius_mem',
    'ThomsonNine.RefinedRadius.radius_mem_tight',
    'ThomsonNine.RefinedRadius.radius_stationary',
    'ThomsonNine.RefinedRadius.source_h00_at_actual_center',
    'ThomsonNine.ActualHermite.H_eval',
    'ThomsonNine.ActualHermite.CertifiedCoefficients.H_coefficient_mem',
    'ThomsonNine.ActualHermite.QuotientStructure.Q_natDegree',
    'ThomsonNine.IntervalMonicSolve.solveTail_mem',
    'ThomsonNine.ActualHermite.QuotientCoefficients.fixed_coefficient_mem',
    'ThomsonNine.ActualHermite.QuotientBernstein.Q_nonnegative',
    'ThomsonNine.ActualHermite.QuotientBernstein.H_minorant',
    'ThomsonNine.ActualHermite.H_derivative_eval',
    'ThomsonNine.ActualHermite.H_natDegree',
    'ThomsonNine.ActualHermite.exists_quotient',
    'ThomsonNine.HermiteFactor.minorant_of_factor',
    'ThomsonNine.ListPolynomial.mem_coeff',
})

KEY_AUDITS.update(json.loads((PV / 'actual_construction_manifest.json').read_text())['key_audits'])
PACKED_MANIFEST = PV / 'packed_coverage_manifest.json'
PACKED = json.loads(PACKED_MANIFEST.read_text()) if PACKED_MANIFEST.exists() else None
REGISTERED_MODULES = set(PACKED['files']) if PACKED else set()
if PACKED:
    KEY_AUDITS.update(PACKED['key_audits'])

BANNED = ('sorry', 'admit', 'axiom', 'native_decide', '#eval', 'run_cmd',
          'run_tac', 'initialize', 'unsafe')
IMPORT_RE = re.compile(r'^\s*(?:(?:public|meta)\s+)?import\s+(?:all\s+)?([A-Za-z_][\w.\']*)\s*$')


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def strip_comments(text):
    """Remove line/block comments and string literals for source scanning."""
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth == 0 and text.startswith('--', i):
            j = text.find('\n', i)
            i = n if j < 0 else j
            continue
        if text.startswith('/-', i):
            depth += 1
            i += 2
            continue
        if depth and text.startswith('-/', i):
            depth -= 1
            i += 2
            continue
        if depth:
            i += 1
            continue
        if text[i] == '"':
            out.append(' ')
            i += 1
            while i < n:
                if text[i] == '\\':
                    i += 2
                    continue
                if text[i] == '"':
                    i += 1
                    break
                i += 1
            continue
        out.append(text[i])
        i += 1
    if depth:
        raise RuntimeError('unterminated block comment')
    return ''.join(out)


def source_of(module):
    if module == ROOT_MODULE:
        return FORMAL / 'ThomsonNine.lean'
    if module in REGISTERED_MODULES:
        return FORMAL / (module.replace('.', '/') + '.lean')
    parts = module.split('.')
    if len(parts) < 2 or parts[0] != 'ThomsonNine':
        raise RuntimeError('not a local module: ' + module)
    return FORMAL / 'ThomsonNine' / Path(*parts[1:]).with_suffix('.lean')


def artifact_of(module):
    return OUT / (module.replace('.', '/') + '.olean')


def kernel_coverage(local_modules, root_modules, all_modules):
    """Require one fresh replay to cover every local proof-bearing module."""
    local_modules, root_modules, all_modules = map(set, (local_modules, root_modules, all_modules))
    if LOCAL_ROOT not in local_modules or ROOT_MODULE not in root_modules:
        raise RuntimeError('integration entry missing from its own import closure')
    if not root_modules <= local_modules:
        raise RuntimeError('formal root closure is not covered by LocalVerification')
    if all_modules != local_modules | {AUDIT_MODULE}:
        raise RuntimeError('local proof modules fall outside the fresh replay closure')
    return {'policy': REPLAY_POLICY, 'fresh_roots': [LOCAL_ROOT],
            'checked_local_modules': sorted(local_modules),
            'covered_integration_roots': [LOCAL_ROOT, ROOT_MODULE],
            'audit_only_module': AUDIT_MODULE}


def parse_imports(module):
    source = source_of(module)
    if not source.is_file():
        raise RuntimeError('missing local source: ' + str(source))
    code = strip_comments(source.read_text())
    imports = []
    for number, line in enumerate(code.splitlines(), 1):
        if 'import' not in line:
            continue
        match = IMPORT_RE.match(line)
        if not match:
            raise RuntimeError('unrecognized import syntax at %s:%d: %r' % (source, number, line))
        dependency = match.group(1)
        owned = dependency == ROOT_MODULE or dependency.startswith('ThomsonNine.') or dependency in REGISTERED_MODULES
        if not owned and (FORMAL / (dependency.replace('.', '/') + '.lean')).is_file():
            raise RuntimeError('unregistered local import: ' + dependency)
        imports.append(dependency)
    return imports


def local_closure(module, seen=None):
    if seen is None:
        seen = set()
    if module in seen:
        return seen
    seen.add(module)
    for imp in parse_imports(module):
        if imp == ROOT_MODULE or imp.startswith('ThomsonNine.') or imp in REGISTERED_MODULES:
            local_closure(imp, seen)
    return seen


def build_order(modules):
    order, state = [], {}

    def visit(module):
        if state.get(module) == 'done':
            return
        if state.get(module) == 'active':
            raise RuntimeError('local import cycle through ' + module)
        state[module] = 'active'
        for imp in parse_imports(module):
            if imp in modules:
                visit(imp)
        state[module] = 'done'
        order.append(module)

    for module in sorted(modules):
        visit(module)
    return order


def scan_source(path):
    code = strip_comments(path.read_text())
    found = [token for token in BANNED
             if re.search(r'(?<![\w.])' + re.escape(token) + r'(?![\w])', code)]
    return found


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--reuse-local-build', action='store_true',
                       help='accept local artifacts only when they match a prior PASS hash stamp')
    group.add_argument('--adopt-build', action='store_true',
                       help='explicitly adopt an externally produced build after mtime/hash checks and write a stamp')
    args = parser.parse_args()
    env = os.environ.copy()
    libs = [OUT, FORMAL / '.lake/packages/mathlib/.lake/build/lib/lean']
    libs += [FORMAL / '.lake/pinned_sources' / n / '.lake/build/lib/lean'
             for n in ['aesop', 'batteries', 'Qq', 'plausible', 'importGraph',
                       'proofwidgets', 'LeanSearchClient', 'Cli']]
    env['LEAN_PATH'] = ':'.join(map(str, libs))
    env['PATH'] = str(BIN) + os.pathsep + env.get('PATH', '')
    LOGS.mkdir(exist_ok=True)
    report = {'status': 'RUNNING',
              'scope': 'Local certificate implications only; final ThomsonNineClaim is unproved.',
              'started_unix': time.time(), 'stages': [],
              'build_mode': 'reuse' if args.reuse_local_build else 'adopt' if args.adopt_build else 'full',
              'kernel_verifier': 'Lean built-in leanchecker --fresh; not an external independent verifier',
              'toolchain_bin': str(BIN)}

    def save_report():
        temporary = REPORT.with_suffix('.json.tmp')
        temporary.write_text(json.dumps(report, indent=2) + '\n')
        temporary.replace(REPORT)

    report['expected_configuration_sha256'] = digest(EXPECTED_PATH)
    save_report()

    def run(name, command):
        log = LOGS / (name + '.log')
        start = time.time()
        print('START', name, flush=True)
        with log.open('w') as stream:
            proc = subprocess.run(list(map(str, command)), cwd=FORMAL, env=env,
                                  stdout=stream, stderr=subprocess.STDOUT)
        report['stages'].append({'name': name, 'exit_code': proc.returncode,
                                 'seconds': time.time() - start, 'command': list(map(str, command)),
                                 'log': str(log.relative_to(PV)), 'log_sha256': digest(log)})
        save_report()
        print('END', name, 'exit', proc.returncode, flush=True)
        if proc.returncode:
            raise RuntimeError(name + ' failed; inspect ' + str(log))
        return log.read_text()

    try:
        version = subprocess.check_output([str(BIN / 'lean'), '--version'], env=env, text=True).strip()
        if not re.search(r'version 4\.34\.1[,)]', version):
            raise RuntimeError('expected Lean 4.34.1, got ' + version)
        report['lean_version'] = version
        run('validation_self_tests', [sys.executable, '-B', PV / 'test_compact_validation.py'])
        run('export_data', [sys.executable, '-B', PV / 'export_local_lean.py', '--check', '--self-test'])
        run('export_replay', [sys.executable, '-B', PV / 'export_local_ldl_replay.py', '--check'])
        run('export_hessian_bridge', [sys.executable, '-B', PV / 'export_local_hessian_bridge.py', '--check', '--self-test'])
        run('export_sparse_hessian', [sys.executable, '-B', PV / 'export_local_sparse_hessian.py', '--check', '--self-test'])
        run('export_compact_grouped', [sys.executable, '-B', PV / 'export_grouped_compact.py', '--check'])
        run('export_aaa_grouped_data', [sys.executable, '-B', PV / 'export_aaa_grouped_data.py', '--check', '--self-test'])
        run('export_aaa_fixed_tree', [sys.executable, '-B', PV / 'export_aaa_fixed_tree.py', '--check', '--self-test'])
        run('export_semantic_inputs', [sys.executable, '-B', PV / 'export_semantic_inputs.py', '--check', '--self-test'])
        run('export_hermite_coefficients', [sys.executable, '-B', PV / 'export_hermite_coefficients.py', '--check', '--self-test'])

        run('export_actual_construction', [sys.executable, '-B', PV / 'export_actual_construction.py', '--check', '--self-test'])
        if PACKED:
            run('export_packed_coverage', [sys.executable, '-B', PV / 'export_packed_coverage.py', '--check', '--self-test'])

        lv = local_closure(LOCAL_ROOT)
        ax = local_closure(AUDIT_MODULE)
        root = local_closure(ROOT_MODULE)
        all_modules = lv | ax | root
        if len(all_modules) != EXPECTED['modules']:
            raise RuntimeError('module closure differs from local_lean_expected.json')
        if set(root) != set(EXPECTED['required_root_modules']):
            raise RuntimeError('formal root closure differs from the required integrated proof modules')
        if EXPECTED.get('kernel_replay_policy') != REPLAY_POLICY:
            raise RuntimeError('unexpected kernel replay policy')
        report['kernel_replay_coverage'] = kernel_coverage(lv, root, all_modules)
        report['local_verification_modules'] = sorted(lv)
        report['root_modules'] = sorted(root)
        order = build_order(all_modules)
        build_modules = [m for m in order if m not in (LOCAL_ROOT, AUDIT_MODULE, ROOT_MODULE)]
        report['modules'] = order
        report['build_modules'] = build_modules
        print('LOCAL_CLOSURE', len(all_modules), 'modules;', len(build_modules), 'to build', flush=True)

        module_sources = {m: source_of(m) for m in all_modules}
        reused_modules = [m for m in all_modules if m not in (AUDIT_MODULE, ROOT_MODULE)]
        pre_sources = {m: digest(p) for m, p in module_sources.items()}
        pre_sources['__root__'] = digest(source_of(ROOT_MODULE))
        pre_sources['__axioms__'] = digest(source_of(AUDIT_MODULE))

        if args.reuse_local_build:
            if not STAMP.is_file():
                raise RuntimeError('no build stamp; run a full build or use --adopt-build explicitly')
            stamp = json.loads(STAMP.read_text())
            if stamp.get('expected_configuration_sha256') != report['expected_configuration_sha256']:
                raise RuntimeError('build stamp expectations differ from current configuration')
            if set(stamp.get('modules', [])) != set(all_modules):
                raise RuntimeError('build stamp module set differs from current closure')
            problems = []
            for module in all_modules:
                if stamp.get('sources', {}).get(module) != pre_sources[module]:
                    problems.append('source hash changed ' + module)
            for module in reused_modules:
                artifact = artifact_of(module)
                if not artifact.is_file():
                    problems.append('missing artifact ' + module)
                elif stamp.get('artifacts', {}).get(module) != digest(artifact):
                    problems.append('artifact hash changed ' + module)
            if problems:
                raise RuntimeError('build stamp mismatch: ' + repr(problems[:8]))
            print('REUSE', len(all_modules), 'modules via hash stamp', flush=True)
        elif args.adopt_build:
            stale = []
            for module in reused_modules:
                artifact = artifact_of(module)
                if not artifact.is_file() or artifact.stat().st_mtime_ns < module_sources[module].stat().st_mtime_ns:
                    stale.append(module)
            if stale:
                raise RuntimeError('cannot adopt stale artifacts: ' + repr(stale[:8]))
            print('ADOPT', len(all_modules), 'modules via mtime/hash checks', flush=True)
        else:
            for module in build_modules:
                target = artifact_of(module)
                run('build_' + module,
                    [BIN / 'lean', '-o', target, '-i', target.with_suffix('.ilean'),
                     module_sources[module].relative_to(FORMAL)])

        run('root', [BIN / 'lean', '-o', OUT / 'ThomsonNine.olean',
                     '-i', OUT / 'ThomsonNine.ilean', 'ThomsonNine.lean'])
        target = artifact_of(LOCAL_ROOT)
        run('build_' + LOCAL_ROOT,
            [BIN / 'lean', '-o', target, '-i', target.with_suffix('.ilean'),
             module_sources[LOCAL_ROOT].relative_to(FORMAL)])
        pre_artifacts = {m: digest(artifact_of(m)) for m in reused_modules}

        audit = run('axioms', [BIN / 'lean', '-o', artifact_of(AUDIT_MODULE),
                               '-i', artifact_of(AUDIT_MODULE).with_suffix('.ilean'),
                               'ThomsonNine/Axioms.lean'])

        # Strictly parse the audit source: imports and #print axioms only.
        axioms_text = strip_comments(source_of(AUDIT_MODULE).read_text())
        directives = []
        for number, line in enumerate(axioms_text.splitlines(), 1):
            stripped = line.strip()
            if not stripped:
                continue
            match = re.match(r'^#print axioms (\S+)$', stripped)
            if match:
                directives.append(match.group(1))
            elif IMPORT_RE.match(line):
                continue
            else:
                raise RuntimeError('unexpected command in Axioms.lean:%d: %r' % (number, line))
        if len(directives) != len(set(directives)):
            raise RuntimeError('duplicate #print axioms directives in Axioms.lean')
        if len(directives) != MIN_AXIOM_AUDITS:
            raise RuntimeError('axiom audit count differs from registered expectations: %d directives' % len(directives))
        missing_required = sorted(KEY_AUDITS - set(directives))
        if missing_required:
            raise RuntimeError('required audit directives missing: ' + repr(missing_required))

        printed = re.findall(r"^'(.+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",
                             audit, re.M)
        names = [n for n, _ in printed]
        if names != directives:
            missing = [d for d in directives if d not in names]
            extra = [n for n in names if n not in directives]
            raise RuntimeError('axiom audit mismatch: missing=%r extra=%r duplicate=%r' % (
                missing[:5], extra[:5], len(names) - len(set(names))))
        found = {a.strip() for _, group in printed for a in group.split(',') if a.strip()}
        if found - ALLOWED_AXIOMS:
            raise RuntimeError('unexpected axioms: ' + repr(sorted(found - ALLOWED_AXIOMS)))
        if 'sorryAx' in found:
            raise RuntimeError('sorryAx reached an audited conclusion')

        # Scan every reachable local source (not Mathlib) for proof escapes.
        banned = {}
        for module, source in module_sources.items():
            found_tokens = scan_source(source)
            if found_tokens:
                banned[str(source.relative_to(FORMAL))] = found_tokens
        if banned:
            raise RuntimeError('forbidden proof escape in reachable sources: ' + repr(banned))
        report['axiom_audits'] = len(names)
        report['audited_declarations_sha256'] = hashlib.sha256(
            '\n'.join(names).encode()).hexdigest()
        report['axioms'] = sorted(found)
        coverage_names = {}
        for name in directives:
            match = re.search(r'\.t(\d+)_gathered(?:_mem)?$', name)
            if match:
                coverage_names.setdefault(int(match.group(1)), []).append(name)
        report['conditional_coverage'] = {
            'covered': len(coverage_names), 'total': EXPECTED['total_targets'],
            'targets': sorted(coverage_names),
            'gathered_audit_declarations': sum(map(len, coverage_names.values())),
            'duplicate_targets': {str(k): v for k, v in sorted(coverage_names.items()) if len(v) > 1},
            'scope': ('Historical gathered declarations deduplicated by target; actual residual binding is discharged by the integrated construction proof.'
                      if EXPECTED.get('global_theorem') else 'Distinct conditional gathered-coefficient targets; no binding to the actual residual.')}
        if sorted(coverage_names) != EXPECTED['conditional_targets']:
            raise RuntimeError('distinct conditional target set differs from local_lean_expected.json')
        report['kernel_replay_modules'] = [LOCAL_ROOT]
        run('kernel_local_fresh', [BIN / 'leanchecker', '--fresh', LOCAL_ROOT])

        if digest(EXPECTED_PATH) != report['expected_configuration_sha256']:
            raise RuntimeError('verification expectations changed during verification')
        post_sources = {m: digest(p) for m, p in module_sources.items()}
        post_sources['__root__'] = digest(source_of(ROOT_MODULE))
        post_sources['__axioms__'] = digest(source_of(AUDIT_MODULE))
        if post_sources != pre_sources:
            raise RuntimeError('local sources changed during verification')
        post_artifacts = {m: digest(artifact_of(m)) for m in all_modules}
        if any(post_artifacts[m] != pre_artifacts[m] for m in reused_modules):
            raise RuntimeError('local artifacts changed during verification')

        sources = list(module_sources.values())
        sources += [source_of(ROOT_MODULE), Path(__file__).resolve(), FORMAL / 'build_direct.sh',
                    EXPECTED_PATH, PV / 'export_grouped_generic.py',
                    PV / 'export_grouped_compact.py', PV / 'compact_grouped_manifest.json',
                    PV / 'test_compact_validation.py',
                    PV / 'export_aaa_grouped_data.py', PV / 'aaa_grouped_data_manifest.json',
                    PV / 'export_aaa_fixed_tree.py', PV / 'aaa_fixed_tree_manifest.json',
                    PV / 'export_semantic_inputs.py', PV / 'semantic_inputs_manifest.json',
                    PV / 'export_hermite_coefficients.py', PV / 'hermite_coefficients_manifest.json',
                    PV / 'independent_kernel_refined_result.json',
                    PV / 'compact_inputs/GroupedT114.lean',
                    PV / 'independent_hermite_RH_result.json', PV / 'independent_local_00_AAA.json']
        sources += [PV / n for n in ['export_local_lean.py', 'local_lean_export_manifest.json',
                                     'export_local_ldl_replay.py', 'local_ldl_replay_manifest.json',
                                     'export_local_hessian_bridge.py', 'local_hessian_bridge_manifest.json',
                                     'export_local_sparse_hessian.py', 'local_sparse_hessian_manifest.json']]
        sources += sorted((PV / 'fixed_inputs').glob('*'))
        sources += sorted((PV / 'semantic_inputs').glob('*'))
        sources += sorted((PV / 'hermite_inputs').glob('*'))
        sources += [PV / 'export_actual_construction.py', PV / 'actual_construction_manifest.json']
        sources += sorted((PV / 'construction_inputs').rglob('*.in'))
        sources += [PV / item['formal'] for item in json.loads((PV / 'actual_construction_manifest.json').read_text())['files'].values()]
        if PACKED:
            sources += [PV / 'export_packed_coverage.py', PACKED_MANIFEST]
            sources += sorted((PV / 'packed_inputs').rglob('*.in'))
        report['sources_sha256'] = {str(p.relative_to(PV)): digest(p) for p in sources}
        report['artifacts_sha256'] = {str(artifact_of(m).relative_to(PV)): post_artifacts[m]
                                      for m in all_modules}
        report['status'] = 'LOCAL_LEAN_COMPILER_AXIOMS_AND_KERNEL_PASS'
        if PACKED and 'ThomsonNine.thomsonNineClaim_proved' in directives:
            report['frozen_global_theorem'] = {
                'declaration': 'ThomsonNine.thomsonNineClaim_proved',
                'type': 'ThomsonNine.ThomsonNineClaim',
                'statement_sha256': digest(FORMAL / 'ThomsonNine/Statement.lean'),
                'compiler_axioms_and_complete_fresh_kernel_pass': True,
                'external_independent_verification': False,
            }

        STAMP.write_text(json.dumps({
            'scope': 'Hash stamp written only after compiler, axiom, and Lean built-in fresh kernel PASS.',
            'conditional_coverage': report['conditional_coverage'],
            'expected_configuration_sha256': report['expected_configuration_sha256'],
            'kernel_replay_modules': report['kernel_replay_modules'],
            'kernel_replay_coverage': report['kernel_replay_coverage'],
            'created_unix': time.time(),
            'modules': order,
            'sources': {m: pre_sources[m] for m in all_modules},
            'artifacts': {m: post_artifacts[m] for m in reused_modules},
            'axioms': sorted(found),
            'axiom_audits': len(names),
            'audited_declarations_sha256': report['audited_declarations_sha256'],
            'root_source_sha256': pre_sources['__root__'],
            'axioms_source_sha256': pre_sources['__axioms__'],
        }, indent=2) + '\n')
    except Exception as exc:
        report['status'] = 'FAIL'
        report['error'] = str(exc)
    report['finished_unix'] = time.time()
    save_report()
    print(report['status'], flush=True)
    return 0 if report['status'].endswith('_PASS') else 1


if __name__ == '__main__':
    raise SystemExit(main())
