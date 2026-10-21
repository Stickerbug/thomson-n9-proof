"""One bounded full-root GUARDED diagnostic attempt; local certificates are explicit unverified inputs here."""
from fractions import Fraction as F
from itertools import permutations
from pathlib import Path
from hashlib import sha256
import json
from sharp_global_subsetdiag2026_engine import diagnose_subsets
ROOT=Path(__file__).parent
OUT=ROOT/'sharp_global_subsetdiag2026_run1.json';assert not OUT.exists()
def read(name):
 p=ROOT/name;return json.loads(p.read_text()),sha256(p.read_bytes()).hexdigest()
def interval(d):
 n=1<<int(d['denominator_power_of_two']);lo,hi=F(int(d['lo_numerator']),n),F(int(d['hi_numerator']),n);assert lo<=hi;return lo,hi
coef,cohash=read('sharp_prerequisites2026_parent_replay2/coefficients.json');local,lohash=read('local_precondition2026_parent_boxes.json');jets,jehash=read('d10_sharpconvex_exact2026_jets.json')
assert local['source_sha256']==cohash and len(local['rows'])==12 and coef['bits']==384
poly={tuple(p):interval(c)for p,c in coef['R_coefficients']}
regions=[];seen=set();retained_box_assertions=[]
for i,row in enumerate(local['rows']):
 box=tuple(interval(c)for c in row['box']);width=min((hi-lo)/2 for lo,hi in box);center=tuple(((lo+hi)/2,)*2 for lo,hi in box);assert width>0
 # An inscribed exact rational cube, irrespective of true-center enclosure.
 core=tuple((cc[0]-width,cc[0]+width)for cc in center);assert all(lo<=cl<=ch<=hi for (lo,hi),(cl,ch)in zip(box,core));retained_box_assertions.append({'row':i,'labels':row['labels'],'source_box':[[str(lo),str(hi)]for lo,hi in box],'inscribed_cube_core':[[str(lo),str(hi)]for lo,hi in core]})
 for pm in permutations(range(3)):
  cc=tuple(center[j]for j in pm);bb=tuple(core[j]for j in pm)
  if any(bb[a][0]>bb[b][1]for a in range(3)for b in range(a+1,3)):continue
  key=(cc,width)
  if key not in seen:seen.add(key);regions.append({'center':cc,'halfwidth':width,'id':f'local-{i}-'+''.join(map(str,pm))})
boundaries=[]
for j,row in enumerate(jets['rows']):
 if 'lambda'not in row:continue
 centerrow=next(c for c in coef['local_centers']if sorted(c['labels'])==sorted(row['labels']));center=tuple(interval(z)for z in centerrow['center_intervals']);center=tuple(sorted(center,key=lambda z:sum(z)))
 lo,hi=interval(row['lambda']);assert lo>0;den=10**25;lam=F(round((lo+hi)*den/2),den);assert lam>0
 boundaries.append({'centerI':center,'lambda':lam,'activation_radius':F(1,20),'id':'boundary-'+''.join(row['labels'])})
assert len(boundaries)==3
inputs={'coefficient_source_sha256':cohash,'local_source_sha256':lohash,'jets_source_sha256':jehash,'local_regions':[{**r,'center':[[str(a),str(b)]for a,b in r['center']],'halfwidth':str(r['halfwidth'])}for r in regions],'boundary_multipliers':[{**r,'centerI':[[str(a),str(b)]for a,b in r['centerI']],'lambda':str(r['lambda']),'activation_radius':str(r['activation_radius'])}for r in boundaries],'source_local_boxes_and_exact_inscription':retained_box_assertions,'premise':'caller must independently replay local proofs and true symmetric coefficient enclosure; status metadata is never treated as independent verification'}
ip=ROOT/'sharp_global_subsetdiag2026_run1_inputs.json';assert not ip.exists();ip.write_text(json.dumps(inputs,indent=2)+'\n');print(json.dumps({'stage':'starting_only_actual_run','regions':len(regions),'boundary_terms':len(boundaries),'budget':80000,'seconds':120,'bits':80,'inputs_sha256':sha256(ip.read_bytes()).hexdigest()}),flush=True)
engine=ROOT/'sharp_global_subsetdiag2026_engine.py';frozen=sha256(engine.read_bytes()).hexdigest()
subset_source=ROOT/'sharp_global_guarddiag2026_run1.json';subset_data=json.loads(subset_source.read_text());paths=[{'path':r['path'],'box':r['box']}for r in subset_data['pending']]
result=diagnose_subsets(poly,regions,boundaries,paths,budget=80000,seconds=120,bits=80)
result['selected_paths_source_sha256']=sha256(subset_source.read_bytes()).hexdigest()
assert frozen==sha256(engine.read_bytes()).hexdigest()
result.update({'input_sources':{'coefficients_sha256':cohash,'local_sha256':lohash,'jets_sha256':jehash},'adapter_selfhash':sha256(Path(__file__).read_bytes()).hexdigest(),'regionJSONhash':sha256(json.dumps(inputs['local_regions'],sort_keys=True,separators=(',',':')).encode()).hexdigest(),'inputs_artifact':str(ip),'inputs_artifact_sha256':sha256(ip.read_bytes()).hexdigest(),'local_proofs_replayed_here':False,'coefficient_enclosure_replayed_here':False,'single_actual_attempt_no_resume':True})
OUT.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k not in ['pending','local_regions','boundary_multipliers']}),flush=True)
