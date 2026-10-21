"""Export checked 640-bit LDL replay, conditional on real matrix entry enclosures.

No polynomial differentiation or contact identity is asserted. Each stored
operation is checked against exact rational corner bounds before Lean emission.
"""
from pathlib import Path
from fractions import Fraction as Q
from hashlib import sha256
import argparse
import json
from export_local_lean import load, validate, lean_interval, LABELS, BASE, need

OUT = BASE / 'formal/ThomsonNine/LocalLDLReplay.lean'
MANIFEST = BASE / 'local_ldl_replay_manifest.json'
S = 1 << 640


def rounded(lo, hi):
    return Q((lo * S).__floor__(), S), Q((hi * S).__ceil__(), S)


def square(iv):
    lo, hi = iv
    return rounded(0 if lo <= 0 <= hi else min(lo * lo, hi * hi), max(lo * lo, hi * hi))


def product(iv, jv):
    corners = [a * b for a in iv for b in jv]
    return rounded(min(corners), max(corners))


def divide(iv, jv):
    need(jv[0] > 0, 'division denominator not positive')
    # Match Box.__truediv__: rounded reciprocal, THEN rounded multiplication.
    return product(iv, rounded(1 / jv[1], 1 / jv[0]))


def check_step(kind, iv, jv, kv):
    if kind == 'square':
        low = 0 if iv[0] <= 0 <= iv[1] else min(a * a for a in iv)
        high = max(a * a for a in iv)
    else:
        if kind == 'div':
            need(jv[0] > 0, 'division denominator not positive')
        corners = [a / b if kind == 'div' else a * b for a in iv for b in jv]
        low, high = min(corners), max(corners)
    need(kv[0] <= low <= high <= kv[1], 'operation not outward enclosed')


def render(rows):
    lines = ['import ThomsonNine.IntervalLocalOps', 'import ThomsonNine.LocalLDLData',
             'import ThomsonNine.LocalLDLFactorization', '',
             '/-! Generated rounded LDL replay. Premises are REAL entries in the saved',
             'preconditioned-Hessian intervals. No actual polynomial Hessian is asserted. -/', '',
             'namespace ThomsonNine.LocalLDL.Replay', '', 'open ThomsonNine.Interval', '']
    stats = []
    for index, row in enumerate(rows):
        n = validate(row, index)
        tag = f'{index:02d}_{LABELS[index]}'
        cert = f'Data.cert_{tag}'
        entries = [(0, 0, 'a'), (0, 1, 'b'), (1, 1, 'd')] if n == 2 else [
            (0, 0, 'a'), (0, 1, 'b'), (0, 2, 'c'), (1, 1, 'd'), (1, 2, 'e'), (2, 2, 'f')]
        vals, names, proofs, exprs, decls, steps = {}, {}, {}, {}, [], []
        for i, j, key in entries:
            vals[key] = tuple(map(Q, row['preconditioned_Hessian'][i][j]))
            names[key] = f'entry_{tag}_{key}'
            proofs[key] = f'h{key}'
            exprs[key] = key
            decls += [f'def {names[key]} : RatInterval := {lean_interval(list(vals[key]))}']
        def op(key, kind, left, right=None):
            iv = vals[left]
            jv = vals.get(right)
            if kind == 'square':
                kv = square(iv)
                expr = f'({exprs[left]}) ^ 2'
            elif kind == 'mul':
                kv = product(iv, jv)
                expr = f'({exprs[left]}) * ({exprs[right]})'
            elif kind == 'div':
                kv = divide(iv, jv)
                expr = f'({exprs[left]}) / ({exprs[right]})'
            elif kind == 'sub':
                kv = iv[0] - jv[1], iv[1] - jv[0]
                expr = f'({exprs[left]}) - ({exprs[right]})'
            else:
                raise ValueError(kind)
            if kind != 'sub':
                check_step(kind, iv, jv, kv)
            name = f'step_{tag}_{key}'
            decls.append(f'def {name} : RatInterval := {lean_interval(list(kv))}')
            vals[key], names[key], exprs[key], proofs[key] = kv, name, expr, 'h' + key
            simp = ', '.join([names[left]] + ([names[right]] if right else []) + [name])
            endpoint = f'(by norm_num [{simp}])'
            if kind == 'square':
                # Three implications selecting the sign case, then two upper bounds.
                call = f'RatInterval.mem_square_of_bounds {proofs[left]} ' + ' '.join([endpoint] * 5)
            elif kind in ('div', 'mul'):
                prefix = 'RatInterval.mem_div_pos_of_bounds' if kind == 'div' else 'RatInterval.mem_mul_of_bounds'
                call = prefix + (' ' + endpoint if kind == 'div' else '') + f' {proofs[left]} {proofs[right]} ' + ' '.join([endpoint] * 8)
            else:
                call = f'RatInterval.mem_subset (RatInterval.mem_sub {proofs[left]} {proofs[right]}) {endpoint} {endpoint}'
                # Sub interval has definitional endpoints; include its definitions.
                call = call.replace(f'[{simp}]', f'[{simp}, RatInterval.sub, RatInterval.add, RatInterval.neg]')
            steps.append(f'  have h{key} : {name}.mem ({expr}) :=\n    {call}')
        op('l21', 'div', 'b', 'a')
        if n == 3:
            op('l31', 'div', 'c', 'a')
        op('s21', 'square', 'l21')
        op('m21', 'mul', 's21', 'a')
        op('d2', 'sub', 'd', 'm21')
        if n == 3:
            op('m3121', 'mul', 'l31', 'l21')
            op('m3121a', 'mul', 'm3121', 'a')
            op('numer32', 'sub', 'e', 'm3121a')
            op('l32', 'div', 'numer32', 'd2')
            op('s31', 'square', 'l31')
            op('m31', 'mul', 's31', 'a')
            op('s32', 'square', 'l32')
            op('m32', 'mul', 's32', 'd2')
            op('partial3', 'sub', 'f', 'm31')
            op('d3', 'sub', 'partial3', 'm32')
        need(vals['a'] == tuple(map(Q, row['LDL_pivots'][0])), 'first pivot differs')
        for key in ['d2'] + (['d3'] if n == 3 else []):
            need(vals[key] == tuple(map(Q, row['LDL_pivots'][int(key[1]) - 1])), 'replayed pivot differs ' + tag + key)
        for key, i, j in [('l21', 1, 0)] + ([('l31', 2, 0), ('l32', 2, 1)] if n == 3 else []):
            need(vals[key] == tuple(map(Q, row['LDL_L'][i][j])), 'replayed L differs ' + tag + key)
        lines += decls + ['']
        variables = 'a b d x y' if n == 2 else 'a b c d e f x y z'
        lines += [f'theorem psd_{tag} ({variables} : ℝ)']
        lines += [f'    (h{k} : {names[k]}.mem {k})' for _, _, k in entries]
        conclusion = '0 ≤ a * x ^ 2 + 2 * b * x * y + d * y ^ 2' if n == 2 else '0 ≤ symmetricQuadratic a b c d e f x y z'
        lines += [f'    : {conclusion} := by'] + steps
        for k, source in [(1, 'a'), (2, 'd2')] + ([(3, 'd3')] if n == 3 else []):
            target = f'{cert}.d{k}'
            expr = exprs[source]
            lines += [f'  have hp{k} : {target}.mem ({expr}) :=',
                      f'    RatInterval.mem_subset {proofs[source]} (by norm_num [{cert}, {names[source]}])',
                      f'      (by norm_num [{cert}, {names[source]}])']
        if n == 3:
            lines += [f'  exact {cert}.entries_nonneg a b c d e f hp1 hp2 hp3 x y z', '']
        else:
            lines += [f'  exact {cert}.entries_nonneg a b d hp1 hp2 x y', '']
        stats.append({'row': index, 'labels': LABELS[index], 'dimension': n,
                      'interval_operations': len(steps), 'saved_pivots_and_L_matched_exactly': True})
    lines += ['end ThomsonNine.LocalLDL.Replay', '']
    text = '\n'.join(lines)
    report = {'status': 'ROUNDED_LDL_REPLAY_EXPORT_ONLY', 'bits': 640, 'rows': stats,
              'interval_operations': sum(s['interval_operations'] for s in stats),
              'generated_sha256': sha256(text.encode()).hexdigest(),
              'exporter_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
              'remaining_premise': 'Actual real preconditioned Hessian entries belong to the saved input intervals. No polynomial/graph differentiation or exact contacts proved here.'}
    return text, json.dumps(report, indent=2) + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    rows, _ = load()
    text, report = render(rows)
    if args.check:
        need(OUT.read_text() == text and MANIFEST.read_text() == report, 'replay export differs')
        print('LOCAL_LDL_REPLAY_EXPORT_CHECK_PASS:', len(rows), 'rows,', json.loads(report)['interval_operations'], 'operations')
    else:
        OUT.write_text(text)
        MANIFEST.write_text(report)
        print('LOCAL_LDL_REPLAY_EXPORT_WRITTEN')


if __name__ == '__main__':
    main()
