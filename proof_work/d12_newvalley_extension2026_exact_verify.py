#!/usr/bin/env python3
"""Finite exact two-chart lower-bound coverage for one fixed rational triangle."""
if not __debug__:raise RuntimeError('Assertions required')
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
from math import lcm
import numpy as np,json,time,hashlib
from exact_tensor_bernstein import coefficients
from dyadic_interval import I,S,BITS as IBITS
from verify_fixed_triangle_two_caps_widened_v1 import add,mul,split
BASE=Path(__file__).resolve().parent;P='d12_newvalley_extension2026_exact_';Q=1<<128;BITS=64;TAU=F(1,10000);EPS=F(1,10**25);LOW=F(-9957,10000);HIGH=F(14,25)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ahash(a):return hashlib.sha256(json.dumps(a.tolist(),separators=(',',':')).encode()).hexdigest()
def area(location):return F(4,1<<(location[1]+location[3]))
def run(seconds=180,node_budget=50000,depth_limit=40):
 start=time.monotonic();deadline=start+seconds;out=BASE/(P+'result.json');assert not out.exists();modelpath=BASE/'nonsharp_d10_root25_7599205_v10.json';oldreport=BASE/'nonsharp_d10_root25_7599205_v10_result.json';upperpath=BASE/'pair056_optimized_certificate.json';lowerpath=BASE/'antipodal_anchor2580_2026_symmetric9957_exact.json';model=json.loads(modelpath.read_text());cert=json.loads(oldreport.read_text());upper=json.loads(upperpath.read_text());lower=json.loads(lowerpath.read_text());assert sha(modelpath)=='6ebdebad61e4ba26f044b07b2ed56bcacdfe8c584b6007561bc17b2cd23b52d0';assert cert['status']=='certified'and cert['pending']==0 and cert['model_sha256']==sha(modelpath);assert F(lower['global_minimizer_pair_dot_lower'])==LOW and lower['status']=='certified_exact_Fraction_comparisons'
 U,V,T=map(F,['-.9457080898901464','-.6695418187936286','.39181335775890314']);g=1+2*U*V*T-U*U-V*V-T*T;assert g>0;s=I(1-U*U).sqrt();actual=[[I(1),I(0),I(0)],[I(U),s,I(0)],[I(V),I(T-U*V)/s,I(g).sqrt()/s]];anchors=[]
 for ar in actual:
  row=[]
  for x in ar:
   k=(x.lo*Q)//S;assert F(k,Q)<=F(x.lo,S)<=F(x.hi,S)<F(k+1,Q);row.append(k)
  anchors.append(row)
 terms=[(tuple(e),F(c))for e,c in model['residual_monomial']];assert all(sum(e)<=27 for e,c in terms);deriv=sum(abs(c)*(e[1]+e[2])for e,c in terms);assert(1+F(3,Q))**26<2;err=F(18,Q)*deriv;assert err<EPS
 rtri=sum(c*U**i*V**j*T**k for(i,j,k),c in terms);budget=7*(F(upper['U'])-F(model['target']))-rtri;assert budget>0 and 6*TAU>budget
 cs=[];den=1
 for edge in(U,V,T):
  c={}
  for(i,j,k),z in terms:c[j,k]=c.get((j,k),F(0))+z*edge**i
  cs.append(c)
  for z in c.values():den=lcm(den,z.denominator)
 cs=[{e:z.numerator*(den//z.denominator)for e,z in c.items()}for c in cs];d={(0,0):Q,(2,0):Q,(0,2):Q};dp=[np.ones((1,1),dtype=object)]
 for _ in range(27):dp.append(mul(dp[-1],d))
 box=[(F(-1),F(1))]*2;D27={(i,j):F(int(z),Q**27)for(i,j),z in np.ndenumerate(dp[27])if z};du=coefficients(D27,box,degrees=(54,54),bits=BITS,upper=True);rows=[];processed_total=0
 print('PREP',time.monotonic()-start,'rounding_error',float(err),flush=True)
 for sign in(1,-1):
  if time.monotonic()>=deadline:
   rows.append({'sign':sign,'root_built':False,'processed_nodes':0,'counts':{'budget_pending':1},'areas':{'budget_pending':'4'},'leaves':[{'location':[0,0,0,0],'path':'','depth':0,'kind':'budget_pending'}]});continue
  buildstart=time.monotonic();ns=[{(0,0):sign*c,(1,0):2*a,(0,1):2*b,(2,0):-sign*c,(0,2):-sign*c}for a,b,c in anchors];p=np.zeros((1,1),dtype=object)
  for(ii,jj),c in zip([(0,1),(0,2),(1,2)],cs):
   outer=np.zeros((1,1),dtype=object)
   for j in range(27,-1,-1):
    n=27-j;h=np.zeros((1,1),dtype=object)
    for k in range(n,-1,-1):
     if k<n:h=mul(h,ns[jj])
     cc=c.get((j,k),0)
     if cc:h=add(h,dp[n-k]*cc)
    outer=add(mul(outer,ns[ii]),h)
   p=add(p,outer)
  assert p.shape==(55,55);poly={(i,j):F(int(z),den*Q**27)for(i,j),z in np.ndenumerate(p)if z};bp=coefficients(poly,box,degrees=(54,54),bits=BITS);threshold=TAU+EPS;br=bp-np.array([-((-int(z)*threshold.numerator)//threshold.denominator)for z in du.flat],dtype=object).reshape(du.shape);cuts=[];labels=['phi_ge_tau']
  for index,ni in enumerate(ns):
   cc={e:F(z,Q)for e,z in ni.items()};cap=HIGH+F(3,Q)
   for e in d:cc[e]=cc.get(e,F(0))-cap
   cuts.append(coefficients(cc,box,degrees=(2,2),bits=BITS));labels.append('upper_anchor_'+str(index))
  for index,ni in enumerate(ns):
   cc={e:-F(z,Q)for e,z in ni.items()};lo=LOW-F(3,Q)
   for e in d:cc[e]=cc.get(e,F(0))+lo
   cuts.append(coefficients(cc,box,degrees=(2,2),bits=BITS));labels.append('lower_anchor_'+str(index))
  cuts.append(coefficients({(2,0):F(1),(0,2):F(1),(0,0):F(-1)},box,degrees=(2,2),bits=BITS));labels.append('outside_hemisphere_disk');roots=[br]+cuts;root_hashes=[ahash(a)for a in roots];buildseconds=time.monotonic()-buildstart;stack=[(roots,0,(0,0,0,0),'')];leaves=[];nodes=0;trace=[];maxdepth=0;clock=time.monotonic()
  while stack and processed_total<node_budget and time.monotonic()<deadline:
   arr,depth,loc,path=stack.pop();nodes+=1;processed_total+=1;maxdepth=max(maxdepth,depth);mins=[int(a.min())for a in arr]
   if mins[0]>=0:kind='phi_ge_tau';index=0
   elif max(mins[1:])>0:index=next(i for i in range(1,len(mins))if mins[i]>0);kind='excluded_'+labels[index]
   elif depth>=depth_limit:kind='depth_pending';index=None
   else:
    axis=depth%2;parts=[split(a,axis)for a in arr];x,dx,y,dy=loc;locs=[(2*x,dx+1,y,dy),(2*x+1,dx+1,y,dy)]if axis==0 else[(x,dx,2*y,dy+1),(x,dx,2*y+1,dy+1)];stack.append(([a[1]for a in parts],depth+1,locs[1],path+'1'));stack.append(([a[0]for a in parts],depth+1,locs[0],path+'0'));trace.append({'path':path,'location':loc,'axis':axis});continue
   leaves.append({'location':loc,'path':path,'depth':depth,'kind':kind,'lower_coefficients':mins,'decision_index':index})
  for arr,depth,loc,path in stack:leaves.append({'location':loc,'path':path,'depth':depth,'kind':'budget_pending','lower_coefficients':[int(a.min())for a in arr]})
  counts=Counter(l['kind']for l in leaves);areas=Counter()
  for l in leaves:areas[l['kind']]+=area(l['location'])
  assert sum(areas.values(),F(0))==4;row={'sign':sign,'root_built':True,'root_hashes':root_hashes,'labels':labels,'root_minimums':[int(a.min())for a in roots],'root_build_seconds':buildseconds,'processed_nodes':nodes,'split_nodes':len(trace),'max_depth':maxdepth,'counts':dict(counts),'areas':{k:str(v)for k,v in areas.items()},'coverage_seconds':time.monotonic()-clock,'leaves':leaves,'split_trace':trace};rows.append(row);print('CHART',json.dumps({k:row[k]for k in ['sign','processed_nodes','split_nodes','max_depth','counts','areas','root_build_seconds','coverage_seconds']}),flush=True)
 complete=len(rows)==2 and all(not any('pending'in l['kind']for l in row['leaves'])for row in rows);elapsed=time.monotonic()-start;deps=[modelpath,oldreport,upperpath,lowerpath,BASE/'dyadic_interval.py',BASE/'exact_tensor_bernstein.py',BASE/'verify_fixed_triangle_two_caps_widened_v1.py',Path(__file__)];result={'status':'certified_fixed_triangle_phi_lower'if complete else'budget_exhausted_or_depth_pending','claim_proved':complete,'root_only':True,'scope':'One fixed rational triangle, all sphere q whose three true anchor dots lie in[-9957/10000,14/25]. The lower dot bound is a necessary condition for global minimizers, not for arbitrary E<=U configurations. No neighborhood or global sharp Thomson certificate.','threshold':str(TAU),'triangle':list(map(str,(U,V,T))),'Gram_exact':str(g),'Gram_display':float(g),'anchor_dyadic_numerators':anchors,'anchor_denominator':str(Q),'anchor_coordinate_error_upper':str(F(1,Q)),'anchor_dot_error_upper':str(F(3,Q)),'phi_perturbation_bound':str(err),'phi_perturbation_allowance':str(EPS),'derivative_coefficient_sum':str(deriv),'bits':BITS,'interval_bits':IBITS,'degrees':[54,54],'allowed_lower':str(LOW),'allowed_upper':str(HIGH),'R_old_T_exact':str(rtri),'remaining_old_budget_exact':str(budget),'remaining_old_budget_display':float(budget),'six_phi_lower_exact':str(6*TAU),'strict_six_phi_budget_gap':str(6*TAU-budget),'strict_six_phi_budget_gap_display':float(6*TAU-budget),'elimination_conclusion':'If claim_proved, this fixed anchor triangle cannot occur in a global minimizer of energy<=U, since six external phi fields cost at least6/10000>remaining old residual budget. No six-point packing assumption is required.','chart_coverage':'Two stereographic hemisphere disks x*x+y*y<=1 inside squares[-1,1]^2; q=(2x,2y,sign*(1-x*x-y*y))/(1+x*x+y*y). All excluded cells are strict cap/lower-dot violations or strictly outside disk.','rounding_proof':'coordinate Q128 floor error<1/Q; dot error<3/Q; mean-value derivative bound for all3 residuals<=18/Q*sum|c|(j+k)<EPS. threshold polynomial subtracts(TAU+EPS)D^27 with upper Bernstein D^27 coefficients.','split_rule':'Exact floor integer midpoint de Casteljau, deterministic axis=depth%2; time stopping only changes pending frontier.','node_budget':node_budget,'seconds_budget':seconds,'depth_limit':depth_limit,'processed_nodes':processed_total,'elapsed_seconds':elapsed,'rows':rows,'dependencies':{str(p):sha(p)for p in deps},'no_old_global_verifier_rerun':True,'numerical_minimum_not_used_in_proof':True}
 out.write_text(json.dumps(result,indent=2)+'\n');print('RESULT',json.dumps({k:result[k]for k in ['status','claim_proved','processed_nodes','elapsed_seconds','strict_six_phi_budget_gap_display']}),flush=True);return result
if __name__=='__main__':run()
