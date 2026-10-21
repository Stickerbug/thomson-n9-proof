"""One authorized fresh-root sharp attempt for the NEW model only."""
from pathlib import Path
from hashlib import sha256
from fractions import Fraction as Q
from itertools import permutations
import json
from dyadic_interval import I,S
from analytic10_sharp2026_engine import check_analytic,AxisCache,ROOT_BOX,coefficients
BASE=Path(__file__).parent;OUT=BASE/'analytic10_sharp2026_run1.json';assert not OUT.exists()
def read(n):
 p=BASE/n;return json.loads(p.read_text()),sha256(p.read_bytes()).hexdigest()
def endpoints(v):
 assert v['denominator_power_of_two']==384
 return Q(int(v['lo_numerator']),S),Q(int(v['hi_numerator']),S)
def raw(v):return I(int(v['lo_numerator']),int(v['hi_numerator']),raw=True)
co,ch=read('d10_relative_normal_exact2026_coefficients.json');loc,lh=read('d10_relative_normal_exact2026_locals.json');assert loc['source_sha256']==ch and len(loc['rows'])==12
for path,h in co['source_sha256'].items():assert sha256(Path(path).read_bytes()).hexdigest()==h
regions=[];retained=[];seen=set()
for j,row in enumerate(loc['rows']):
 assert row['status']=='CERTIFIED_LOCAL_POSITIVE_WIDTH'
 bb=tuple(endpoints(v)for v in row['box']);width=min((hi-lo)/2 for lo,hi in bb);center=tuple(((lo+hi)/2,)*2 for lo,hi in bb);core=tuple((c[0]-width,c[0]+width)for c in center);assert width>0 and all(lo<=cl<=chh<=hi for (lo,hi),(cl,chh)in zip(bb,core));retained.append({'row':j,'labels':row['labels'],'source_box':[[str(a),str(b)]for a,b in bb],'core':[[str(a),str(b)]for a,b in core]})
 for pm in permutations(range(3)):
  cc=tuple(center[k]for k in pm);bc=tuple(core[k]for k in pm);key=(cc,width)
  if any(bc[a][0]>bc[b][1]for a in range(3)for b in range(a+1,3))or key in seen:continue
  seen.add(key);regions.append({'center':cc,'halfwidth':width,'id':f'new-local-{j}-'+''.join(map(str,pm))})
# Boundary multipliers are optimization constants only. No normal/jet premise.
rp={tuple(p):raw(v)for p,v in co['R_coefficients']};boundaries=[]
for row in loc['rows']:
 if not row['kind'].startswith('lower_Gram_graph'):continue
 crow=next(c for c in co['local_centers']if sorted(c['labels'])==sorted(row['labels']));center=tuple(endpoints(v)for v in crow['center_intervals']);center=tuple(sorted(center,key=lambda x:sum(x)));pt=[I((a+b)/2)for a,b in center];powers=[[x**j for j in range(28)]for x in pt];du=I(0)
 for (i,j,k),v in rp.items():
  if i:du+=i*v*powers[0][i-1]*powers[1][j]*powers[2][k]
 gu=2*(pt[1]*pt[2]-pt[0]);ratio=du/gu;den=10**25;lam=max(Q(0),Q(round(Q(ratio.lo+ratio.hi,2*S)*den),den));assert lam>=0
 boundaries.append({'centerI':center,'lambda':lam,'activation_radius':Q(1,20),'id':'new-boundary-'+''.join(crow['labels'])})
assert len(boundaries)==3
Fints={tuple(p):endpoints(v)for p,v in co['F_coefficients']};fm={p:(a+b)/2 for p,(a,b)in Fints.items()};sym={}
for pm in permutations(range(3)):
 for p,v in fm.items():
  pp=tuple(p[k]for k in pm);sym[pp]=sym.get(pp,Q(0))+v/6
fm=sym;eps=sum((b-a)/2 for a,b in Fints.values());dm={}
for (i,j,k),v in fm.items():dm[j+k]=dm.get(j+k,Q(0))+v
K={p:-7*v for p,v in fm.items()};ci=endpoints(co['c']);K[(0,0,0)]=K.get((0,0,0),0)-ci[1]-10*eps
KB=coefficients(K,ROOT_BOX,degrees=(10,10,10),bits=96);maxK=max(abs(int(x))for x in KB.flat);assert maxK<1<<124;hroot=AxisCache(dm,96).H(0,0);maxH=max(abs(v)for v in hroot[1]);assert maxH<1<<124
engine=BASE/'analytic10_sharp2026_engine.py';freeze={str(p):sha256(p.read_bytes()).hexdigest()for p in [engine,BASE/'analytic10_2026_sum.c',BASE/'analytic10_2026_sum.so',BASE/'exact128_2026.py',BASE/'exact128_2026.c',BASE/'d10_relative_normal_exact2026_coefficients.json',BASE/'d10_relative_normal_exact2026_locals.json']}
inputs={'source_coefficient_sha256':ch,'source_local_sha256':lh,'frozen_sha256':freeze,'bits':96,'delta':'0','root_K_absmax':str(maxK),'root_K_absmax_bitlength':maxK.bit_length(),'root_H_absmax_bitlength':maxH.bit_length(),'regions':[dict(r,center=[[str(a),str(b)]for a,b in r['center']],halfwidth=str(r['halfwidth']))for r in regions],'boundaries':[dict(b,centerI=[[str(a),str(v)]for a,v in b['centerI']],**{'lambda':str(b['lambda']),'activation_radius':str(b['activation_radius'])})for b in boundaries],'source_box_inscriptions':retained,'premises':'All local boxes pertain to exactly this NEW coefficient source. Local proof and exact45 contact compatibility theorem are external premises; metadata status is not replay.'};ip=BASE/'analytic10_sharp2026_run1_inputs.json';assert not ip.exists();ip.open('x').write(json.dumps(inputs,indent=2)+'\n');print(json.dumps({'stage':'unique_sharp_root_start','bits':96,'delta':0,'budget':200000,'seconds':180,'regions':len(regions),'K_bits':maxK.bit_length(),'H_bits':maxH.bit_length(),'boundary_lambdas':{b['id']:str(b['lambda'])for b in boundaries}}),flush=True)
result=check_analytic(Fints,ci,regions,boundaries,budget=200000,seconds=180,delta=Q(0),bits=96)
assert all(sha256(Path(p).read_bytes()).hexdigest()==h for p,h in freeze.items());result.update(input_sources_sha256={'coefficients':ch,'locals':lh},input_artifact=str(ip),inputs_sha256=sha256(ip.read_bytes()).hexdigest(),adapter_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),new_local_premises_replayed_here=False,exact_contact_theorem_replayed_here=False,single_root_attempt=True);OUT.open('x').write(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k not in ['rootinputs','pending']}),flush=True)
