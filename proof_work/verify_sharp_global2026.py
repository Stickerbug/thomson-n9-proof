"""Replay sharp prerequisites and a new complete-root hybrid search.

A global result is emitted ONLY when every root branch has closed. Mathematical
geometric/contact identities listed by the prerequisite verifier remain explicit
proof dependencies; this is not a Lean formalization or an independent arithmetic
implementation. No frontier is resumed and no saved completion status is trusted.
"""
if not __debug__:
    raise RuntimeError('Assertions are required; do not run with -O')
import argparse
import hashlib
import itertools
import json
import time
from fractions import Fraction as F
from pathlib import Path
from verify_sharp_prerequisites2026 import run as prerequisites
from sharp_global_hybrid2026_engine import check_away

BASE = Path(__file__).resolve().parent

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def interval(data):
    scale = 1 << int(data['denominator_power_of_two'])
    lo = F(int(data['lo_numerator']), scale)
    hi = F(int(data['hi_numerator']), scale)
    assert lo <= hi
    return lo, hi

def regions_from_verified_local(data):
    assert data['status'] == 'CERTIFIED_POSITIVE_WIDTH_CONTACT_NEIGHBORHOODS'
    assert len(data['rows']) == 12
    regions, seen, inscriptions = [], set(), []
    for index, row in enumerate(data['rows']):
        box = tuple(interval(c) for c in row['box'])
        width = min((hi-lo)/2 for lo, hi in box)
        center = tuple((((lo+hi)/2),)*2 for lo, hi in box)
        assert width > 0
        core = tuple((cc[0]-width, cc[0]+width) for cc in center)
        assert all(lo <= a <= b <= hi for (lo,hi),(a,b) in zip(box,core))
        inscriptions.append({'row':index, 'source_box':[[str(a),str(b)] for a,b in box],
                             'inscribed_core':[[str(a),str(b)] for a,b in core]})
        for perm in itertools.permutations(range(3)):
            cc = tuple(center[j] for j in perm)
            bb = tuple(core[j] for j in perm)
            if any(bb[a][0] > bb[b][1] for a in range(3) for b in range(a+1,3)):
                continue
            key = cc, width
            if key not in seen:
                seen.add(key)
                regions.append({'id':f'local-{index}-'+''.join(map(str,perm)),
                                'center':cc, 'halfwidth':width})
    return regions, inscriptions

def run(outdir, seconds=600, budget=300000):
    start = time.monotonic()
    outdir = Path(outdir).resolve()
    assert not outdir.exists(), 'Choose a new output directory'
    outdir.mkdir(parents=True)
    proofdir = outdir/'prerequisites'
    pre = prerequisites(proofdir)
    assert pre['status'] == 'CERTIFIED_SHARP_PREREQUISITES_NOT_GLOBAL'
    coefpath, localpath = proofdir/'coefficients.json', proofdir/'local.json'
    coef, local = json.loads(coefpath.read_text()), json.loads(localpath.read_text())
    assert local['source_sha256'] == digest(coefpath)
    assert all(pre['math_array_identity'].values()) and pre['local_rows_identical']
    assert coef['bits'] == 384
    poly = {tuple(p):interval(c) for p,c in coef['R_coefficients']}
    regions, inscriptions = regions_from_verified_local(local)
    # These are search strategy coefficients only: every nonnegative lambda is
    # valid for the implication R_lower-lambda*g>=0, g>=0 => R_true>=0.
    jets_path = BASE/'d10_sharpconvex_exact2026_jets.json'
    jets = json.loads(jets_path.read_text())
    boundaries = []
    for row in jets['rows']:
        if 'lambda' not in row:
            continue
        item = next(c for c in coef['local_centers'] if sorted(c['labels']) == sorted(row['labels']))
        center = tuple(sorted((interval(z) for z in item['center_intervals']), key=lambda z:sum(z)))
        lo, hi = interval(row['lambda'])
        lam = F(round((lo+hi)*10**25/2), 10**25)
        assert lam >= 0
        boundaries.append({'id':'boundary-'+''.join(row['labels']), 'centerI':center,
                           'lambda':lam, 'activation_radius':F(1,20)})
    assert len(boundaries) == 3
    engine_path = BASE/'sharp_global_hybrid2026_engine.py'
    frozen_engine = digest(engine_path)
    print('Starting new complete-root hybrid verification', flush=True)
    away = check_away(poly, regions, boundaries, budget=budget, seconds=seconds, bits=80)
    assert frozen_engine == digest(engine_path), 'Engine changed during replay'
    (outdir/'away.json').write_text(json.dumps(away,indent=2)+'\n')
    closed = away['status'] == 'away_certified_given_local_regions' and away['pending_count'] == 0
    assert away['restart_from_full_root'] and not away['frontier_resumed']
    assert away['root_coverage']['visited_equals_terminal_plus_splits']
    assert away['root_coverage']['terminal_plus_pending_equals_splits_plus_one']
    result = {'status':'COMPUTER_ASSISTED_ENERGY_PROOF_COMPLETE_GIVEN_STATED_GEOMETRIC_LEMMAS' if closed else 'INCOMPLETE_GLOBAL_COVERAGE',
              'global_energy_equality':bool(closed), 'uniqueness_claimed':False,
              'conclusion':'E_min(9)=E_D3h(r_star)' if closed else 'No global optimality conclusion',
              'method':'fresh exact prerequisites and complete-root hybrid Bernstein tree; shared arithmetic implementation',
              'mathematical_dependencies':'Exact geometric kernel moment/nullspace identities, twelve left relations and stationary compatibility as stated in closure checklist; Hermite remainder; ordered PSD energy identity',
              'symmetry_proof':'True F is the six-permutation average; sum of three copies of the same H, diagonal terms and constants are symmetric',
              'boundary_lambda_role':'Arbitrary nonnegative search coefficients, not assumed exact derivatives',
              'prerequisites_status':pre['status'], 'local_inscriptions':inscriptions,
              'away_status':away['status'], 'pending_count':away['pending_count'],
              'source_sha256':{p.name:digest(p) for p in [Path(__file__),engine_path,BASE/'verify_sharp_prerequisites2026.py',jets_path]},
              'artifact_sha256':{str(p.relative_to(outdir)):digest(p) for p in [proofdir/'prerequisites.json',coefpath,localpath,outdir/'away.json']},
              'seconds':time.monotonic()-start}
    (outdir/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['local_inscriptions','source_sha256','artifact_sha256']}),flush=True)
    return result

if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--outdir',required=True)
    parser.add_argument('--seconds',type=float,default=600)
    parser.add_argument('--budget',type=int,default=300000)
    args=parser.parse_args()
    run(args.outdir,args.seconds,args.budget)
