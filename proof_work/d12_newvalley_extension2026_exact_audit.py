#!/usr/bin/env python3
"""Read-only saved-tree replay using shared exact Bernstein conversion, independent split loop."""
if not __debug__:raise RuntimeError('Assertions required')
from pathlib import Path
from fractions import Fraction as F
from math import lcm
from collections import Counter
import numpy as np,json,hashlib,time
from exact_tensor_bernstein import coefficients
from dyadic_interval import I,S
from verify_fixed_triangle_two_caps_widened_v1 import add,mul
B=Path(__file__).resolve().parent;P='d12_newvalley_extension2026_exact_'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ahash(a):return hashlib.sha256(json.dumps(a.tolist(),separators=(',',':')).encode()).hexdigest()
def bisect(a,axis):
 n=a.shape[axis]-1;w=np.moveaxis(a,axis,0);lo=np.empty_like(w);hi=np.empty_like(w)
 for j in range(n+1):
  lo[j]=w[0];hi[n-j]=w[-1]
  if j<n:w=np.array([(int(x)+int(y))//2 for x,y in zip(w[:-1].flat,w[1:].flat)],dtype=object).reshape((n-j,)+w.shape[1:])
 return np.moveaxis(lo,0,axis),np.moveaxis(hi,0,axis)
def peval(p,x,y):return sum(v*x**i*y**j for(i,j),v in p.items())
def run():
 start=time.monotonic();rp=B/(P+'result.json');r=json.loads(rp.read_text());assert r['claim_proved']and r['status']=='certified_fixed_triangle_phi_lower';assert all(sha(Path(p))==s for p,s in r['dependencies'].items());Q=int(r['anchor_denominator']);bits=r['bits'];tau=F(r['threshold']);eps=F(r['phi_perturbation_allowance']);U,V,T=map(F,r['triangle']);g=1+2*U*V*T-U*U-V*V-T*T;assert str(g)==r['Gram_exact']and g>0;ss=I(1-U*U).sqrt();actual=[[I(1),I(0),I(0)],[I(U),ss,I(0)],[I(V),I(T-U*V)/ss,I(g).sqrt()/ss]];anchors=r['anchor_dyadic_numerators']
 for aa,ar in zip(anchors,actual):
  for a,z in zip(aa,ar):assert F(a,Q)<=F(z.lo,S)<=F(z.hi,S)<F(a+1,Q)
 model=json.loads((B/'nonsharp_d10_root25_7599205_v10.json').read_text());terms=[(tuple(e),F(c))for e,c in model['residual_monomial']];assert all(sum(e)<=27 for e,c in terms);deriv=sum(abs(c)*(e[1]+e[2])for e,c in terms);err=F(18,Q)*deriv;assert str(err)==r['phi_perturbation_bound']and err<eps and(1+F(3,Q))**26<2;rtri=sum(c*U**i*V**j*T**k for(i,j,k),c in terms);upper=json.loads((B/'pair056_optimized_certificate.json').read_text());K=7*(F(upper['U'])-F(model['target']))-rtri;assert str(K)==r['remaining_old_budget_exact']and 6*tau-K==F(r['strict_six_phi_budget_gap'])>0
 cs=[];den=1
 for edge in(U,V,T):
  c={}
  for(i,j,k),v in terms:c[j,k]=c.get((j,k),F(0))+v*edge**i
  cs.append(c)
  for z in c.values():den=lcm(den,z.denominator)
 csi=[{e:z.numerator*(den//z.denominator)for e,z in c.items()}for c in cs];d={(0,0):Q,(2,0):Q,(0,2):Q};dp=[np.ones((1,1),dtype=object)]
 for _ in range(27):dp.append(mul(dp[-1],d))
 box=[(F(-1),F(1))]*2;D27={(i,j):F(int(z),Q**27)for(i,j),z in np.ndenumerate(dp[27])if z};du=coefficients(D27,box,degrees=(54,54),bits=bits,upper=True);summary=[];totalleaves=0;totalsplits=0;pointchecks=0
 for row in r['rows']:
  sign=row['sign'];assert row['root_built'];ns=[{(0,0):sign*c,(1,0):2*a,(0,1):2*b,(2,0):-sign*c,(0,2):-sign*c}for a,b,c in anchors];p=np.zeros((1,1),dtype=object)
  for(a,b),c in zip([(0,1),(0,2),(1,2)],csi):
   outer=np.zeros((1,1),dtype=object)
   for j in range(27,-1,-1):
    n=27-j;inner=np.zeros((1,1),dtype=object)
    for k in range(n,-1,-1):
     if k<n:inner=mul(inner,ns[b])
     if(j,k)in c:inner=add(inner,dp[n-k]*c[j,k])
    outer=add(mul(outer,ns[a]),inner)
   p=add(p,outer)
  poly={(i,j):F(int(z),den*Q**27)for(i,j),z in np.ndenumerate(p)if z};bp=coefficients(poly,box,degrees=(54,54),bits=bits);threshold=tau+eps;br=bp-np.array([-((-int(z)*threshold.numerator)//threshold.denominator)for z in du.flat],dtype=object).reshape(du.shape);cuts=[]
  for ni in ns:
   c={e:F(z,Q)for e,z in ni.items()}
   for e in d:c[e]=c.get(e,F(0))-(F(14,25)+F(3,Q))
   cuts.append(coefficients(c,box,degrees=(2,2),bits=bits))
  for ni in ns:
   c={e:-F(z,Q)for e,z in ni.items()}
   for e in d:c[e]=c.get(e,F(0))+(F(-9957,10000)-F(3,Q))
   cuts.append(coefficients(c,box,degrees=(2,2),bits=bits))
  cuts.append(coefficients({(2,0):F(1),(0,2):F(1),(0,0):F(-1)},box,degrees=(2,2),bits=bits));root=[br]+cuts;assert[ahash(a)for a in root]==row['root_hashes']
  for x,y in[(F(0),F(0)),(F(1,3),F(-2,5)),(F(-1,2),F(1,2))]:
   D=1+x*x+y*y;q=[2*x/D,2*y/D,sign*(1-x*x-y*y)/D];assert sum(z*z for z in q)==1;dot=[sum(F(a,Q)*z for a,z in zip(anchor,q))for anchor in anchors];field=sum(sum(c*dot[a]**j*dot[b]**k for(j,k),c in cc.items())for(a,b),cc in zip([(0,1),(0,2),(1,2)],cs));assert peval(poly,x,y)==field*D**27;pointchecks+=1
  leaves={z['path']:z for z in row['leaves']};splits={z['path']:z for z in row['split_trace']};assert len(leaves)==len(row['leaves'])and len(splits)==len(row['split_trace'])and not(set(leaves)&set(splits));stack=[('',root,(0,0,0,0))];seen=set();areas=Counter();kinds=Counter();rootnodes=0
  while stack:
   path,aa,loc=stack.pop();assert path not in seen;seen.add(path);rootnodes+=1;mins=[int(a.min())for a in aa]
   if path in leaves:
    z=leaves[path];assert list(loc)==z['location']and len(path)==z['depth']and mins==z['lower_coefficients'];kind=z['kind'];assert'pending'not in kind;idx=z['decision_index']
    if kind=='phi_ge_tau':assert idx==0 and mins[0]>=0
    else:assert kind.startswith('excluded_upper_anchor_')and idx in[1,2,3]and mins[idx]>0
    kinds[kind]+=1;areas[kind]+=F(4,1<<(loc[1]+loc[3]));continue
   assert path in splits;sp=splits[path];axis=len(path)%2;assert sp['axis']==axis and list(loc)==sp['location'];parts=[bisect(a,axis)for a in aa];x,dx,y,dy=loc;ll=[(2*x,dx+1,y,dy),(2*x+1,dx+1,y,dy)]if axis==0 else[(x,dx,2*y,dy+1),(x,dx,2*y+1,dy+1)];stack.extend([(path+'0',[z[0]for z in parts],ll[0]),(path+'1',[z[1]for z in parts],ll[1])])
  assert seen==set(leaves)|set(splits)and rootnodes==row['processed_nodes']and sum(areas.values(),F(0))==4 and dict(kinds)==row['counts']and{k:str(v)for k,v in areas.items()}==row['areas'];summary.append({'sign':sign,'checked_root_nodes':rootnodes,'leaves':len(leaves),'splits':len(splits),'counts':dict(kinds),'areas':{k:str(v)for k,v in areas.items()}});totalleaves+=len(leaves);totalsplits+=len(splits)
 assert len(summary)==2 and totalleaves==totalsplits+2
 out={'status':'passed_saved_complete_two_chart_replay','seconds':time.monotonic()-start,'coverage_and_coefficients_replayed':True,'independent_split_loop':True,'shared_implementation':'Homogenization reconstruction uses shared add/mul and exact_tensor_bernstein conversion; this is a shared-backend independent saved-tree replay, not a wholly independent proof implementation.','interval_anchor_floor_checked':True,'perturbation_bound_checked':True,'all_dependency_hashes_matched':True,'exact_rational_homogenization_point_checks':pointchecks,'terminal_leaves':totalleaves,'split_nodes':totalsplits,'rows':summary,'unused_lower_dot_and_disk_cuts':True,'stronger_scope':'All S2 q with each true anchor dot<=14/25, without using a lower dot bound; lower-dot certificate not needed in this successful tree.','phi_lower_exact':str(tau),'six_phi_cost_exact':str(6*tau),'remaining_budget_exact':str(K),'strict_six_phi_gap_exact':str(6*tau-K),'strict_six_phi_gap_display':float(6*tau-K),'conclusion':'This exact fixed rational anchor triangle cannot extend to any nine-point sphere configuration with energy<=U under the archived pair<=14/25 necessary bound. No neighborhood exclusion or global sharp proof.','source_result_sha256':sha(rp),'audit_sha256':sha(Path(__file__))};dest=B/(P+'audit.json');assert not dest.exists();dest.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2),flush=True);return out
if __name__=='__main__':run()
