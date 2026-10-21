"""Bernstein derivative bounds on a full cube: no Gram pruning."""
if not __debug__:raise RuntimeError('Assertions must be enabled')
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,time,numpy as np
from exact_tensor_bernstein import coefficients
BASE=Path(__file__).parent
BITS=64;SCALE=1<<BITS

def split(C,axis,upper=False):
 W=np.moveaxis(C,axis,0);rows=[W];n=W.shape[0]-1
 for k in range(n):
  raw=rows[-1][:-1]+rows[-1][1:]
  rows.append(-((-raw)//2)if upper else raw//2)
 left=np.stack([rows[k][0]for k in range(n+1)])
 right=np.stack([rows[n-k][-1]for k in range(n+1)])
 return np.moveaxis(left,0,axis),np.moveaxis(right,0,axis)

def run():
 start=time.monotonic();mp=BASE/'nonsharp_d10_root25_7599205_v10.json';model=json.loads(mp.read_text());poly={tuple(e):F(c)for e,c in model['residual_monomial']};box=[(F(-1),F(56000001,10**8))]*3;axisreports=[]
 for axis in range(3):
  deriv={tuple(e[j]-(j==axis)for j in range(3)):c*e[axis]for e,c in poly.items()if e[axis]}
  lo=coefficients(deriv,box,bits=BITS);hi=coefficients(deriv,box,bits=BITS,upper=True);root=max(abs(int(lo.min())),abs(int(hi.max())));leaves=[(lo,hi,'root')]
  if F(root,SCALE)>100:
   for splitaxis in range(3):
    nxt=[]
    for low,high,label in leaves:
     lows=split(low,splitaxis);highs=split(high,splitaxis,True)
     for k in range(2):nxt.append((lows[k],highs[k],label+str(k)))
    leaves=nxt
  bound=max(max(abs(int(low.min())),abs(int(high.max())))for low,high,_ in leaves)
  rec={'axis':axis,'degrees':[x-1 for x in lo.shape],'root_maxabs':str(F(root,SCALE)),'leaf_maxabs':str(F(bound,SCALE)),'leaves':[{'label':label,'lower':str(F(int(low.min()),SCALE)),'upper':str(F(int(high.max()),SCALE))}for low,high,label in leaves]};axisreports.append(rec);print('AXIS',axis,'root',float(F(root,SCALE)),'leaf',float(F(bound,SCALE)),'leaves',len(leaves),flush=True)
 lip=sum(F(r['leaf_maxabs'])for r in axisreports)
 import t1_neighborhood_sensitivity2026_verify as old
 base=old.run();chart=json.loads((BASE/'fixed_triangle_two_caps_widened_certificate_v1.json').read_text());budget=json.loads((BASE/'fixed_triangle_two_cap_budget_exact_v1.json').read_text());T=list(map(F,chart['anchor_parameter']));K=F(budget['six_point_phi_budget']);six=F(chart['six_point_cost_lower']);candidates=[]
 for delta in [F(1,10**9),F(1,10**10),F(1,10**11),F(1,10**12),F(1,10**13)]:
  cube=[(x-delta,x+delta)for x in T];uv=[a*b for a in cube[0]for b in cube[1]];num=(cube[2][0]-max(uv),cube[2][1]-min(uv));coarse=max(map(abs,cube[0]))<F('.76')and max(map(abs,cube[1]))<F('.3')and max(map(abs,num))<F('.13')
  slack=F('.56')+8*delta<F(chart['allowed_anchor_dot_upper']);margin=six-K-145*lip*delta;candidates.append({'delta':str(delta),'coarse_bounds_pass':coarse,'anchor_slack_pass':slack,'margin':str(margin),'pass':coarse and slack and margin>0})
 chosen=next(r for r in candidates if r['pass']);delta=F(chosen['delta']);assert delta>=F(base['delta'])
 result={'status':'certified_fixed_triangle_neighborhood_v2_conditional_on_hashed_dependencies','method':'Full cube Bernstein derivative enclosures, 64-bit outward coefficient rounding and at most one midpoint split per axis. No Gram or geometric pruning.','derivative_cube':[[str(a),str(b)]for a,b in box],'axis_reports':axisreports,'Lipschitz_S':str(lip),'candidates':candidates,'delta':str(delta),'cube':[[str(x-delta),str(x+delta)]for x in T],'six_phi_lower':str(six-144*lip*delta),'budget_upper':str(K+lip*delta),'margin':chosen['margin'],'dependencies':base['dependencies'],'old_analytic_verifier_sha256':hashlib.sha256((BASE/'t1_neighborhood_sensitivity2026_verify.py').read_bytes()).hexdigest(),'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'seconds':time.monotonic()-start,'display_only':{'Lipschitz_S':float(lip),'delta':float(delta),'margin':float(F(chosen['margin']))}}
 return result
if __name__=='__main__':
 result=run();out=BASE/'t1_neighborhood_sensitivity2026_neighbor_v2_certificate.json';out.write_text(json.dumps(result,indent=2)+'\n');print(result['display_only']);print('SAVED',out)
