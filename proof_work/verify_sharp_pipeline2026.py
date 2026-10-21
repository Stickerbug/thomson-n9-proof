"""Exact prerequisites plus fresh-root coverage; no completion status is trusted."""
if not __debug__:
 raise RuntimeError('Assertions required')
import argparse,hashlib,itertools,json,time
from fractions import Fraction as F
from pathlib import Path
from verify_sharp_prerequisites2026 import run as prerequisites
from sharp_global_native128_2026_engine import check_away
from local_precondition2026_verify import run as enlarge_local
BASE=Path(__file__).resolve().parent

def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def interval(d):
 scale=1<<int(d['denominator_power_of_two']);lo,hi=F(int(d['lo_numerator']),scale),F(int(d['hi_numerator']),scale);assert lo<=hi;return lo,hi

def run(outdir,seconds=600,budget=300000):
 start=time.monotonic();outdir=Path(outdir).resolve();assert not outdir.exists(),'Use a fresh output directory';outdir.mkdir(parents=True)
 pre=prerequisites(outdir/'prerequisites');assert pre['status']=='CERTIFIED_SHARP_PREREQUISITES_NOT_GLOBAL'
 cp=outdir/'prerequisites/coefficients.json';lp=outdir/'prerequisites/local.json'
 co=json.loads(cp.read_text());local=json.loads(lp.read_text());assert local['source_sha256']==digest(cp);assert co['bits']==384
 assert all(pre['math_array_identity'].values()) and pre['local_rows_identical'] and len(local['rows'])==12
 xp=outdir/'local_preconditioned.json';local=enlarge_local(cp,xp,ctx=co)
 assert local['status']=='CERTIFIED_PRECONDITIONED_POSITIVE_WIDTH_LOCAL_BOXES_NOT_GLOBAL' and local['source_sha256']==digest(cp) and len(local['rows'])==12
 poly={tuple(p):interval(c)for p,c in co['R_coefficients']};regions=[];seen=set();inscriptions=[]
 for i,row in enumerate(local['rows']):
  box=tuple(interval(c)for c in row['box']);width=min((hi-lo)/2 for lo,hi in box);center=tuple((((lo+hi)/2),)*2 for lo,hi in box);assert width>0
  core=tuple((cc[0]-width,cc[0]+width)for cc in center);assert all(lo<=a<=b<=hi for (lo,hi),(a,b)in zip(box,core))
  inscriptions.append({'row':i,'source_box':[[str(a),str(b)]for a,b in box],'inscribed_core':[[str(a),str(b)]for a,b in core]})
  for pm in itertools.permutations(range(3)):
   cc=tuple(center[j]for j in pm);bb=tuple(core[j]for j in pm)
   if any(bb[a][0]>bb[b][1]for a in range(3)for b in range(a+1,3)):continue
   key=cc,width
   if key not in seen:seen.add(key);regions.append({'id':f'local-{i}-'+''.join(map(str,pm)),'center':cc,'halfwidth':width})
 jets_path=BASE/'d10_sharpconvex_exact2026_jets.json';jets=json.loads(jets_path.read_text());boundaries=[]
 # Any nonnegative lambda is valid; exact derivative status is not a premise.
 for row in jets['rows']:
  if 'lambda'not in row:continue
  item=next(c for c in co['local_centers']if sorted(c['labels'])==sorted(row['labels']));center=tuple(sorted((interval(z)for z in item['center_intervals']),key=lambda z:sum(z)))
  lo,hi=interval(row['lambda']);lam=F(round((lo+hi)*10**25/2),10**25);assert lam>=0
  boundaries.append({'id':'boundary-'+''.join(row['labels']),'centerI':center,'lambda':lam,'activation_radius':F(1,20)})
 assert len(boundaries)==3
 engine=BASE/'sharp_global_native128_2026_engine.py';frozen=digest(engine)
 print('Starting fresh complete-root native128 check',flush=True)
 away=check_away(poly,regions,boundaries,budget=budget,seconds=seconds,bits=80);assert frozen==digest(engine),'Frozen engine changed'
 ap=outdir/'away.json';ap.write_text(json.dumps(away,indent=2)+'\n')
 assert away['restart_from_full_root']and not away['frontier_resumed']
 assert away['root_coverage']['visited_equals_terminal_plus_splits']and away['root_coverage']['terminal_plus_pending_equals_splits_plus_one']
 closed=away['status']=='away_certified_given_local_regions'and away['pending_count']==0
 result={'status':'COMPUTER_ASSISTED_ENERGY_PROOF_COMPLETE_GIVEN_STATED_GEOMETRIC_LEMMAS'if closed else'INCOMPLETE_GLOBAL_COVERAGE','global_energy_equality':bool(closed),'uniqueness_claimed':False,'conclusion':'E_min(9)=E_D3h(r_star)'if closed else'No global optimality conclusion','method':'fresh exact prerequisites, freshly preconditioned local boxes, and full-root native128 Bernstein tree; shared arithmetic implementation','mathematical_dependencies':'Exact geometric kernel moment/nullspace identities,12 left relations and stationary compatibility in closure checklist; Hermite remainder; ordered PSD energy identity','symmetry_proof':'F is six-permutation average; H and diagonal sums are symmetric','boundary_lambda_role':'arbitrary nonnegative strategy constants','prerequisites_status':pre['status'],'local_inscriptions':inscriptions,'away_status':away['status'],'pending_count':away['pending_count'],'source_sha256':{p.name:digest(p)for p in[Path(__file__),engine,BASE/'verify_sharp_prerequisites2026.py',BASE/'local_precondition2026_verify.py',BASE/'exact128_2026.c',BASE/'exact128_2026.py',jets_path]},'artifact_sha256':{str(p.relative_to(outdir)):digest(p)for p in[outdir/'prerequisites/prerequisites.json',cp,lp,xp,ap]},'seconds':time.monotonic()-start}
 (outdir/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'],result['pending_count'],flush=True);return result

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--outdir',required=True);p.add_argument('--seconds',type=float,default=600);p.add_argument('--budget',type=int,default=300000);a=p.parse_args();run(a.outdir,a.seconds,a.budget)
