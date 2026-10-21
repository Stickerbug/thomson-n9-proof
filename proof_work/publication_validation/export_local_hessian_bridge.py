"""Export exact target-Hessian interval -> congruence -> rounded LDL PSD bridges.

The original Hessian entry memberships remain explicit real premises. This does
not assert that a polynomial or a Gram graph has those Hessian entries.
"""
from pathlib import Path
from fractions import Fraction as Q
from hashlib import sha256
from copy import deepcopy
import argparse
import json
from export_local_lean import BASE, LABELS, load, validate, need, interval, lean_interval, rat

OUT = BASE / 'formal/ThomsonNine/LocalHessianBridge.lean'
MANIFEST = BASE / 'local_hessian_bridge_manifest.json'
KEYS = [('a', 0, 0), ('b', 0, 1), ('c', 0, 2), ('d', 1, 1), ('e', 1, 2), ('f', 2, 2)]


def checked_maps(row, index):
    n = validate(row, index)
    H, P, W = row['target_Hessian'], row['preconditioned_Hessian'], row['congruence_W']
    for M in [H, P]:
        need(len(M) == n and all(len(r) == n for r in M), 'Hessian dimension')
        for i in range(n):
            for j in range(n):
                need(interval(M[i][j]) == interval(M[j][i]), 'Hessian not symmetric')
    a = Q(W[1][0])
    b, c = (Q(W[2][0]), Q(W[2][1])) if n == 3 else (Q(0), Q(0))
    coeff = [[1,0,0,0,0,0], [a,1,0,0,0,0], [b,c,1,0,0,0],
             [a*a,2*a,0,1,0,0], [a*b,a*c+b,a,c,1,0],
             [b*b,2*b*c,2*b,c*c,2*c,1]]
    inputs = [interval(H[i][j]) if i < n and j < n else (Q(0),Q(0)) for _,i,j in KEYS]
    checks = []
    for k, (key,i,j) in enumerate(KEYS):
        if i >= n or j >= n:
            continue
        lo = sum(min(q*x for x in iv) for q,iv in zip(coeff[k],inputs))
        hi = sum(max(q*x for x in iv) for q,iv in zip(coeff[k],inputs))
        target = interval(P[i][j])
        need(target[0] <= lo <= hi <= target[1], 'preconditioning enclosure failed '+key)
        checks.append(key)
    return n, inputs, checks


def render(rows, sources):
    lines = ['import ThomsonNine.IntervalLinear', 'import ThomsonNine.LocalLDLReplay', '',
             '/-! Generated original-entry interval bridges. Actual Hessian evaluation',
             'and exact contacts are still explicit, unproved upstream obligations. -/', '',
             'namespace ThomsonNine.LocalLDL.HessianBridge', '',
             'open ThomsonNine.Interval', '']
    stats = []
    for index,row in enumerate(rows):
        n, inputs, checks = checked_maps(row,index)
        tag = f'{index:02d}_{LABELS[index]}'
        a,b,c = [f'w{tag}_{k}' for k in ['21','31','32']]
        for name,value in [(a,row['congruence_W'][1][0])] + ([(b,row['congruence_W'][2][0]),(c,row['congruence_W'][2][1])] if n==3 else []):
            lines.append(f'def {name} : ℚ := {rat(value)}')
        coeff = [['1','0','0','0','0','0'], [a,'1','0','0','0','0'], [b,c,'1','0','0','0'],
                 [f'{a} ^ 2',f'2 * {a}','0','1','0','0'],
                 [f'{a} * {b}',f'{a} * {c} + {b}',a,c,'1','0'],
                 [f'{b} ^ 2',f'2 * {b} * {c}',f'2 * {b}',f'{c} ^ 2',f'2 * {c}','1']]
        names = [f'original_{tag}_{key}' for key,_,_ in KEYS]
        for name,iv in zip(names,inputs):
            lines.append(f'def {name} : RatInterval := {lean_interval(list(iv))}')
        real_args = 'A B C D E F' if n==3 else 'A B 0 D 0 0'
        vars = 'A B C D E F' if n==3 else 'A B D'
        h = ['hA','hB','hC','hD','hE','hF'] if n==3 else ['hA','hB','h0','hD','h0','h0']
        present = list(range(6)) if n==3 else [0,1,3]
        premises = [f'    (h{"ABCDEF"[k]} : {names[k]}.mem {"ABCDEF"[k]})' for k in present]
        for k,(key,i,j) in enumerate(KEYS):
            if key not in checks:
                continue
            cs = ' '.join('('+x+')' for x in coeff[k])
            expr = f'RatInterval.linear6 {cs} {real_args}'
            lines += [f'theorem entry_mem_{tag}_{key} ({vars} : ℝ)'] + premises
            lines += [f'    : Replay.entry_{tag}_{key}.mem ({expr}) := by']
            if n==2:
                lines += [f'  have h0 : {names[2]}.mem (0 : ℝ) := by norm_num [{names[2]}, RatInterval.mem]']
                # All three dummy intervals have identical endpoints and proofs.
            simp = ', '.join(names + [a] + ([b,c] if n==3 else []) + [f'Replay.entry_{tag}_{key}',
                         'RatInterval.linearInterval6','RatInterval.signedScale','RatInterval.scale',
                         'RatInterval.add','RatInterval.neg'])
            lines += [f'  exact RatInterval.mem_subset (RatInterval.mem_linear6 {cs} '+ ' '.join(h) + ')',
                      f'    (by norm_num [{simp}]) (by norm_num [{simp}])', '']
        maps = []
        for k,(key,_,_) in enumerate(KEYS):
            if key in checks:
                maps.append('RatInterval.linear6 '+' '.join('('+x+')' for x in coeff[k])+' '+real_args)
        lines += [f'theorem psd_original_{tag} ({vars} '+('x y z' if n==3 else 'x y')+' : ℝ)'] + premises
        conclusion = '0 ≤ symmetricQuadratic A B C D E F x y z' if n==3 else '0 ≤ A * x ^ 2 + 2 * B * x * y + D * y ^ 2'
        lines += [f'    : {conclusion} := by']
        if n==3:
            lines += ['  apply congruence_nonneg (symmetricQuadratic A B C D E F)',
                      '    (symmetricQuadratic '+' '.join('('+v+')' for v in maps)+f') {a} {b} {c}',
                      '  · intro u v w',
                      '    simp only [RatInterval.linear6, Rat.cast_zero, Rat.cast_one, Rat.cast_add,',
                      '      Rat.cast_mul, Rat.cast_pow, zero_mul, one_mul, add_zero, zero_add]',
                      '    exact symmetricQuadratic_congruence A B C D E F _ _ _ u v w',
                      f'  · intro u v w', f'    exact Replay.psd_{tag} '+' '.join('('+v+')' for v in maps)+(' u v w' if n==3 else ' u v')]
        else:
            lines += ['  apply congruence2_nonneg (fun u v => A * u ^ 2 + 2 * B * u * v + D * v ^ 2)',
                      '    (fun u v => ('+maps[0]+') * u ^ 2 + 2 * ('+maps[1]+') * u * v + ('+maps[2]+f') * v ^ 2) {a}',
                      '  · intro u v',
                      '    simp only [RatInterval.linear6, Rat.cast_zero, Rat.cast_one, Rat.cast_add,',
                      '      Rat.cast_mul, Rat.cast_pow, zero_mul, one_mul, add_zero, zero_add]',
                      '    ring', '  · intro u v', f'    exact Replay.psd_{tag} '+' '.join('('+v+')' for v in maps)+(' u v w' if n==3 else ' u v')]
        for key in checks:
            lines += [f'      (entry_mem_{tag}_{key} {vars} '+' '.join(h[k] for k in present)+')']
        lines += ['']
        stats.append({'index':index,'label':LABELS[index],'dimension':n,'entry_enclosures':len(checks),
                      'source':sources[index], 'theorem':f'ThomsonNine.LocalLDL.HessianBridge.psd_original_{tag}'})
    lines += ['end ThomsonNine.LocalLDL.HessianBridge','']
    text = '\n'.join(lines)
    report = {'status':'ORIGINAL_HESSIAN_INTERVAL_TO_PSD_EXPORT_ONLY', 'rows':stats,
              'entry_enclosures':sum(r['entry_enclosures'] for r in stats),
              'generated_sha256':sha256(text.encode()).hexdigest(),
              'exporter_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
              'remaining_premise':'Actual original Hessian entries belong to target_Hessian intervals. No real residual differentiation or exact contact identities proved.'}
    return text,json.dumps(report,indent=2)+'\n'


def self_test(rows):
    tests = [(0,'target_Hessian'),(6,'target_Hessian'),(0,'preconditioned_Hessian'),(6,'preconditioned_Hessian')]
    for index,key in tests:
        bad=deepcopy(rows[index])
        if key=='target_Hessian':
            bad[key][0][1]=['2','1']
        else:
            bad[key][0][0]=['0','0']
        try:
            checked_maps(bad,index)
        except ValueError:
            continue
        raise AssertionError('bad Hessian accepted')
    print('HESSIAN_BRIDGE_NEGATIVE_TESTS_PASS',len(tests))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    parser.add_argument('--self-test',action='store_true')
    args=parser.parse_args()
    rows,sources=load()
    text,report=render(rows,sources)
    if args.self_test:
        self_test(rows)
    if args.check:
        need(OUT.read_text()==text and MANIFEST.read_text()==report,'Hessian bridge export differs')
        print('LOCAL_HESSIAN_BRIDGE_CHECK_PASS: 12 rows, 63 entry enclosures')
    else:
        OUT.write_text(text)
        MANIFEST.write_text(report)
        print('LOCAL_HESSIAN_BRIDGE_WRITTEN: 12 rows, 63 entry enclosures')


if __name__=='__main__':
    main()
