if not __debug__:raise RuntimeError('No -O')
import json,time,hashlib,signal,runpy
from pathlib import Path
from fractions import Fraction as Q
from itertools import permutations
from dyadic_interval import I,S
from certify_pair_moments import L,U,derivative
from d10_singleendpoint2026_kernel import run as kernel
from narrowroot2026_export import export,raw
import narrowroot2026_hermite as nh
import narrowroot2026_local_formulas as loc
import narrowroot2026_precondition as pre
from analytic10_sharp2026_engine import check_analytic
BASE=Path(__file__).resolve().parent
OUT=BASE/'relative_normal2026_replay2'
def load(p):return json.loads(Path(p).read_text())
def save(n,o):
 p=OUT/n;assert not p.exists();p.write_text(json.dumps(o,indent=2)+'\n');return p
def endpoints(v):return Q(int(v['lo_numerator']),S),Q(int(v['hi_numerator']),S)
def main():
 start=time.monotonic();assert not OUT.exists();OUT.mkdir();signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('fresh proof chain hard235second budget')));signal.alarm(235)
 names=['analytic10_sharp2026_engine.py','analytic10_2026_sum.c','analytic10_2026_sum.so','exact128_2026.py','exact128_2026.c','dyadic_interval.py','exact_tensor_bernstein.py','candidate_low_rank.py','certify_pair_moments.py','certify_three_point_d4.py','narrowroot2026_hermite.py','narrowroot2026_hermite.json','narrowroot2026_root.json','narrowroot2026_export.py','d10_singleendpoint2026_kernel.py','d10_relative_normal_exact2026_seed.json','d10_relative_normal_exact2026_certificate.json','d10_relative_normal_exact2026_coefficients.json','d10_relative_normal_exact2026_locals.json','narrowroot2026_local_formulas.py','narrowroot2026_precondition.py','d10_exact_contact_jets_v1.py','verify_pair056_saved.py','pair056_optimized_certificate.json','analytic10_sharp2026_run1.json',Path(__file__).name];frozen={n:hashlib.sha256((BASE/n).read_bytes()).hexdigest()for n in names}
 runpy.run_path(str(BASE/'verify_pair056_saved.py'),run_name='relative_normal2026_replay_pair');print('PASS pair replay',flush=True)
 left,right=Q(L),Q(U);assert derivative(I(left)).hi<0<derivative(I(right)).lo;steps=0
 while right-left>Q(1,2**350):
  steps+=1;mid=(left+right)/2;v=derivative(I(mid))
  if v.hi<0:left=mid
  elif v.lo>0:right=mid
  else:
   rad=Q(max(abs(v.lo),abs(v.hi)),S);assert rad>0;old=right-left;left=max(left,mid-rad);right=min(right,mid+rad);assert right-left<old
 assert derivative(I(left)).hi<0<derivative(I(right)).lo;assert [str(left),str(right)]==load(BASE/'narrowroot2026_root.json')['root_refined'];r=I(left,right);E=I(3).sqrt()+2*I(3).sqrt()/r+I('1.5')/(1-r*r).sqrt()+6/(4-r*r).sqrt()+12/(2-r).sqrt()+6/(2+2*r).sqrt();assert E.hi<I(Q(load(BASE/'pair056_optimized_certificate.json')['U'])).lo;save('root.json',{'root_refined':[str(left),str(right)],'steps':steps,'E':E.bounds(),'stationary_derivative_signs_verified':True,'uniqueness_reason':'Esecond>4sqrt3/r^3>1 on(0,1)'})
 extras=list(map(Q,['-1','-.9','-.4','-.2','.1','.45','.52','.56']));herm=[nh.run(),nh.run(extras)];assert herm==load(BASE/'narrowroot2026_hermite.json')['cases'];save('hermite.json',{'cases':herm,'minorant_proof':'f28>0 times product14 squared factors; true stationary root; numerical K unused'});print('PASS strict root350 and fresh Hermite cases',time.monotonic()-start,flush=True)
 seed=save('seed.json',load(BASE/'d10_relative_normal_exact2026_seed.json'));cert=OUT/'kernel.json';ctx=kernel(str(cert),str(BASE/'d10_relative_normal_exact2026_certificate.json'),True,str(seed));co=export(str(cert),str(OUT/'coefficients.json'),ctx);old=load(BASE/'d10_relative_normal_exact2026_coefficients.json');keys=['R_coefficients','F_coefficients','H_coefficients_ascending','E_star','c','F111','local_centers'];assert all(co[k]==old[k]for k in keys);print('PASS fresh newkernel/newcoefficients',time.monotonic()-start,flush=True)
 poly={tuple(a):raw(v)for a,v in co['R_coefficients']};rows=[]
 for item in co['local_centers']:
  center=[raw(v)for v in item['center_intervals']];mid=[I((v.lo+v.hi)//2,raw=True)for v in center];q=loc.shift(poly,mid);_,Hc=pre.evaluate_box(q,center,'0',item['kind']);W=pre.center_transform(Hc);attempts=[]
  for power in range(3,19):
   width=Q(1,10**power)
   try:row,H=pre.evaluate_box(q,center,width,item['kind'],W);break
   except AssertionError as e:attempts.append({'halfwidth':str(width),'failure':str(e)})
  else:raise AssertionError(('no local width',item['labels']))
  row.update({'labels':item['labels'],'center_intervals':item['center_intervals'],'congruence_W':[[str(v)for v in rr]for rr in W],'preconditioned_Hessian':[[v.bounds()for v in rr]for rr in pre.transform(H,W)],'failed_larger_widths':attempts,'status':'CERTIFIED_LOCAL_POSITIVE_WIDTH'});rows.append(row);print('PASS fresh local',item['labels'],str(width),flush=True)
 prior=load(BASE/'d10_relative_normal_exact2026_locals.json');assert len(rows)==12
 for row,oldrow in zip(rows,prior['rows']):
  for key in ['box','halfwidth','center_intervals','congruence_W','preconditioned_Hessian','kind']:assert row[key]==oldrow[key]
 save('locals.json',{'status':'TWELVE_LOCAL_CERTIFICATES_REBUILT_NOT_TRANSFERRED','source_sha256':hashlib.sha256((OUT/'coefficients.json').read_bytes()).hexdigest(),'rows':rows});regions=[];seen=set();retained=[]
 for j,row in enumerate(rows):
  bb=tuple(endpoints(v)for v in row['box']);width=min((hi-lo)/2 for lo,hi in bb);center=tuple(((lo+hi)/2,)*2 for lo,hi in bb);core=tuple((c[0]-width,c[0]+width)for c in center);assert width>0 and all(lo<=cl<=ch<=hi for (lo,hi),(cl,ch)in zip(bb,core));retained.append({'labels':row['labels'],'source_box':[[str(a),str(b)]for a,b in bb],'core':[[str(a),str(b)]for a,b in core]})
  for pm in permutations(range(3)):
   cc=tuple(center[k]for k in pm);bc=tuple(core[k]for k in pm);key=(cc,width)
   if any(bc[a][0]>bc[b][1]for a in range(3)for b in range(a+1,3))or key in seen:continue
   seen.add(key);regions.append({'center':cc,'halfwidth':width,'id':f'new-local-{j}-'+''.join(map(str,pm))})
 boundaries=[]
 for row in rows:
  if not row['kind'].startswith('lower_Gram_graph'):continue
  crow=next(c for c in co['local_centers']if sorted(c['labels'])==sorted(row['labels']));center=tuple(sorted((endpoints(v)for v in crow['center_intervals']),key=lambda x:sum(x)));pt=[I((a+b)/2)for a,b in center];powers=[[x**j for j in range(28)]for x in pt];du=I(0)
  for (i,j,k),v in poly.items():
   if i:du+=i*v*powers[0][i-1]*powers[1][j]*powers[2][k]
  gu=2*(pt[1]*pt[2]-pt[0]);ratio=du/gu;den=10**25;lam=max(Q(0),Q(round(Q(ratio.lo+ratio.hi,2*S)*den),den));assert lam>=0;boundaries.append({'centerI':center,'lambda':lam,'activation_radius':Q(1,20),'id':'new-boundary-'+''.join(crow['labels'])})
 assert len(boundaries)==3;print('START fresh root96 after new prerequisites seconds',time.monotonic()-start,'localregions',len(regions),flush=True);Fints={tuple(p):endpoints(v)for p,v in co['F_coefficients']};result=check_analytic(Fints,endpoints(co['c']),regions,boundaries,budget=200000,seconds=min(180,230-(time.monotonic()-start)),delta=Q(0),bits=96);save('root_replay.json',result);assert result['status']=='CONDITIONAL_SHARP_CLOSED'and result['pending_count']==0 and result['pending']==[] and result['guard_reason']is None and all(result['coverage'].values());oldroot=load(BASE/'analytic10_sharp2026_run1.json');match=['visited_nodes','split_nodes','counts','local_counts','boundary_counts','maxdepth','transcript_sha256','root_inputs_sha256','h_range_skipped_nodes'];assert all(result[k]==oldroot[k]for k in match);assert all(hashlib.sha256((BASE/n).read_bytes()).hexdigest()==h for n,h in frozen.items());save('prerequisites_and_root.json',{'status':'FRESH_NEW_MODEL_PREREQUISITES_AND_SHARP_ROOT_REPLAYED_PENDING_MATHEMATICAL_AUDIT','old_kernel_or_local_proof_called':False,'pair_root_Hermite_PSD_coefficients_locals_rebuilt':True,'coefficient_arrays_exactly_match':keys,'all12locals_rebuilt':True,'local_core_inscriptions':retained,'fresh_root':{'status':result['status'],'visited_nodes':result['visited_nodes'],'pending_count':0,'bits':96,'delta':'0','matching_fields':match,'transcript_sha256':result['transcript_sha256']},'same_implementation_replay_not_independent_implementation':True,'geometric_WM_compatibility_and_energy_identity_require_human_audit':True,'source_sha256':frozen,'artifacts_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in OUT.iterdir()if p.is_file()},'seconds':time.monotonic()-start});signal.alarm(0);print('PASS FRESH_PROOF_CHAIN_REPLAY',result['visited_nodes'],'seconds',time.monotonic()-start,flush=True)
if __name__=='__main__':main()
