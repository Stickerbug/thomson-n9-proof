"""Exact local budget gradient; no new sphere or parameter exclusion proof."""
from pathlib import Path
from fractions import Fraction as F
import json,hashlib,time
from exact_tensor_bernstein import coefficients
from dyadic_interval import I,S
if not __debug__:raise RuntimeError('Assertions required')
base=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run():
 start=time.monotonic();mp=base/'nonsharp_d10_root25_7599205_v10.json';rp=base/'nonsharp_d10_root25_7599205_v10_result.json';pp=base/'pair056_optimized_certificate.json'
 model=json.loads(mp.read_text());report=json.loads(rp.read_text());pair=json.loads(pp.read_text());assert report['status']=='certified'and report['pending']==0 and report['model_sha256']==sha(mp)
 center=list(map(F,['-.759220762336624','-.29211600772137486','.32931701954562287']));delta=F(1,1000000);box=[(t-delta,t+delta)for t in center];poly={tuple(e):F(v)for e,v in model['residual_monomial']};bits=96;scale=1<<bits;rows=[]
 for k in range(3):
  dp={tuple(n-(i==k)for i,n in enumerate(e)):v*e[k]for e,v in poly.items()if e[k]}
  tensor=coefficients(dp,box,bits=bits);lo=F(min(tensor.flat),scale);hi=F(max(tensor.flat)+1,scale);bound=max(abs(lo),abs(hi))
  rows.append(dict(axis=k,derivative_lower=str(lo),derivative_upper=str(hi),absolute_bound=str(bound),shape=list(tensor.shape),warning='Upper adds one fixed-point unit to maximum floor coefficient.'))
 G=sum((F(r['absolute_bound'])for r in rows),F(0));u,v,t=[I(*b)for b in box];gram=1+2*u*v*t-u*u-v*v-t*t;assert gram.lo>0
 value=sum(c*center[0]**e[0]*center[1]**e[1]*center[2]**e[2]for e,c in poly.items());U=F(pair['U']);B=F(model['target']);K=7*(U-B)-value;slack=F('0.00046')-K;remaining=(slack/delta-G)/6
 result=dict(status='exact_local_budget_gradient_bound',center=list(map(str,center)),delta=str(delta),box=[[str(a),str(b)]for a,b in box],bits=bits,derivatives=rows,gradient_l1_bound=str(G),gradient_l1_display=float(G),center_budget=str(K),conditional_sphere_derivative_sum_threshold=str(remaining),conditional_sphere_derivative_sum_threshold_display=float(remaining),gram_interval=gram.bounds(),scope='Budget K(T)=7(U-B)-R(T) has L1 gradient <= G throughout the stated parameter cube. If a NEW widened sphere certificate proves six-point cost>=0.00046 and sphere derivatives are certified on the entire parameter cube, the sufficient condition is sum(M_k)<saved conditional threshold. Neither hypothesis is proved here; no parameter neighborhood enlargement or new global energy bound.',dependencies={str(p):sha(p)for p in [mp,rp,pp,Path(__file__),base/'exact_tensor_bernstein.py',base/'dyadic_interval.py']},seconds=time.monotonic()-start)
 out=base/'t1_local_budget_gradient2026.json'
 if out.exists():
  old=json.loads(out.read_text());old.pop('seconds',None);check=dict(result);check.pop('seconds',None);assert old==check
 else:out.write_text(json.dumps(result,indent=2)+'\n')
 print('CERTIFIED budget gradient L1 <=',float(G),'conditional sphere derivative sum threshold',float(remaining),'seconds',result['seconds'],flush=True)
 return result
if __name__=='__main__':run()
