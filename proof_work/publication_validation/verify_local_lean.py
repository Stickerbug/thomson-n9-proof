#!/usr/bin/env python3
"""Sequential compiler, axiom, and independent-kernel validation of local work.

The final Thomson theorem is NOT asserted.  The verifier discovers the local
import closure of `LocalVerification`, `Axioms`, and the root module, parses
imports strictly, audits every axiom-print directive in `Axioms.lean`, rejects
proof escapes in all reachable local sources, and runs `leanchecker`.

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
import subprocess
import sys
import time

PV = Path(__file__).resolve().parent
FORMAL = PV / 'formal'
BIN = PV / 'toolchain' / 'lean-4.34.1-linux_aarch64' / 'bin'
OUT = FORMAL / '.lake/build/lib/lean'
LOCAL_ROOT = 'ThomsonNine.LocalVerification'
AUDIT_MODULE = 'ThomsonNine.Axioms'
ROOT_MODULE = 'ThomsonNine'
REPORT = PV / 'local_lean_verification.json'
STAMP = PV / 'local_lean_build_stamp.json'
LOGS = PV / 'local_lean_verification_logs'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
MIN_AXIOM_AUDITS = 273

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
    parts = module.split('.')
    if len(parts) < 2 or parts[0] != 'ThomsonNine':
        raise RuntimeError('not a local module: ' + module)
    return FORMAL / 'ThomsonNine' / Path(*parts[1:]).with_suffix('.lean')


def artifact_of(module):
    return OUT / (module.replace('.', '/') + '.olean')


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
        imports.append(match.group(1))
    return imports


def local_closure(module, seen=None):
    if seen is None:
        seen = set()
    if module in seen:
        return seen
    seen.add(module)
    for imp in parse_imports(module):
        if imp == ROOT_MODULE or imp.startswith('ThomsonNine.'):
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
              'started_unix': time.time(), 'stages': []}

    def run(name, command):
        log = LOGS / (name + '.log')
        start = time.time()
        print('START', name, flush=True)
        with log.open('w') as stream:
            proc = subprocess.run(list(map(str, command)), cwd=FORMAL, env=env,
                                  stdout=stream, stderr=subprocess.STDOUT)
        report['stages'].append({'name': name, 'exit_code': proc.returncode,
                                 'seconds': time.time() - start,
                                 'log': str(log.relative_to(PV)), 'log_sha256': digest(log)})
        print('END', name, 'exit', proc.returncode, flush=True)
        if proc.returncode:
            raise RuntimeError(name + ' failed; inspect ' + str(log))
        return log.read_text()

    try:
        run('export_data', [sys.executable, '-B', PV / 'export_local_lean.py', '--check', '--self-test'])
        run('export_replay', [sys.executable, '-B', PV / 'export_local_ldl_replay.py', '--check'])
        run('export_hessian_bridge', [sys.executable, '-B', PV / 'export_local_hessian_bridge.py', '--check', '--self-test'])
        run('export_sparse_hessian', [sys.executable, '-B', PV / 'export_local_sparse_hessian.py', '--check', '--self-test'])

        lv = local_closure(LOCAL_ROOT)
        ax = local_closure(AUDIT_MODULE)
        root = local_closure(ROOT_MODULE)
        all_modules = lv | ax | root
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
            for module in build_modules + [LOCAL_ROOT]:
                target = artifact_of(module)
                run('build_' + module,
                    [BIN / 'lean', '-o', target, '-i', target.with_suffix('.ilean'),
                     module_sources[module].relative_to(FORMAL)])

        pre_artifacts = {m: digest(artifact_of(m)) for m in reused_modules}

        run('root', [BIN / 'lean', '-o', OUT / 'ThomsonNine.olean',
                     '-i', OUT / 'ThomsonNine.ilean', 'ThomsonNine.lean'])
        audit = run('axioms', [BIN / 'lean', 'ThomsonNine/Axioms.lean'])

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
        if len(directives) < MIN_AXIOM_AUDITS:
            raise RuntimeError('axiom audit too small: %d directives' % len(directives))
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
        run('kernel', [BIN / 'leanchecker', LOCAL_ROOT])

        post_sources = {m: digest(p) for m, p in module_sources.items()}
        post_sources['__root__'] = digest(source_of(ROOT_MODULE))
        post_sources['__axioms__'] = digest(source_of(AUDIT_MODULE))
        if post_sources != pre_sources:
            raise RuntimeError('local sources changed during verification')
        post_artifacts = {m: digest(artifact_of(m)) for m in all_modules}
        if any(post_artifacts[m] != pre_artifacts[m] for m in reused_modules):
            raise RuntimeError('local artifacts changed during verification')

        sources = list(module_sources.values())
        sources += [source_of(ROOT_MODULE), Path(__file__).resolve(), FORMAL / 'build_direct.sh']
        sources += [PV / n for n in ['export_local_lean.py', 'local_lean_export_manifest.json',
                                     'export_local_ldl_replay.py', 'local_ldl_replay_manifest.json',
                                     'export_local_hessian_bridge.py', 'local_hessian_bridge_manifest.json',
                                     'export_local_sparse_hessian.py', 'local_sparse_hessian_manifest.json']]
        report['sources_sha256'] = {str(p.relative_to(PV)): digest(p) for p in sources}
        report['artifacts_sha256'] = {str(artifact_of(m).relative_to(PV)): post_artifacts[m]
                                      for m in all_modules}
        report['status'] = 'LOCAL_LEAN_COMPILER_AXIOMS_AND_KERNEL_PASS'

        STAMP.write_text(json.dumps({
            'scope': 'Hash stamp written only after compiler, axiom, and kernel PASS.',
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
    REPORT.write_text(json.dumps(report, indent=2) + '\n')
    print(report['status'], flush=True)
    return 0 if report['status'].endswith('_PASS') else 1


if __name__ == '__main__':
    raise SystemExit(main())
