if not __debug__:
 raise RuntimeError('Run without -O')
import json,time,itertools,hashlib
from pathlib import Path
from fractions import Fraction as F
from math import comb
from dyadic_interval import I,S,BITS
from d10_sharpconvex_exact2026_export import raw
from d10_exact_contact_jets_v1 import ldl

def diff(p,axis):
 out={}
 for a,c in p.items():
  if a[axis]:b=list(a);b[axis]-=1;out[tuple(b)]=a[axis]*c
 return out

def horner(p,pt,axis=0):
 if axis==3:return p.get((),I(0))
 n=max((a[0]for a in p),default=0);v=I(0)
 for j in reversed(range(n+1)):
  q={a[1:]:c for a,c in p.items()if a[0]==j};v=v*pt[axis]+horner(q,pt,axis+1)
 return v

def shift(p,center):
 # Tensor binomial transform, one axis at a time, preserving I coefficient enclosures.
 for axis in range(3):
  out={};powers=[center[axis]**j for j in range(28)]
  for a,c in p.items():
   for j in range(a[axis]+1):
    b=list(a);b[axis]=j;b=tuple(b);out[b]=out.get(b,I(0))+c*comb(a[axis],j)*powers[a[axis]-j]
  p=out
 return p

def try_box(poly,center,width,kind,box_override=None):
 delta=I(width);box=[I(c.lo-delta.hi,c.hi+delta.hi,raw=True)for c in center]
 if box_override is not None:box=box_override
 dp=[diff(poly,i)for i in range(3)];ddp=[[diff(dp[i],j)for j in range(3)]for i in range(3)]
 midpoint=[I((c.lo+c.hi)//2,raw=True)for c in center]
 def evaluate(p,where):return horner(p,[x-c for x,c in zip(where,midpoint)])
 if kind!='identically_boundary':
  HH=[[evaluate(ddp[i][j],box)for j in range(3)]for i in range(3)]
  pivots=ldl(HH);return {'halfwidth':str(F(width)),'box':[v.bounds()for v in box],'Hessian_LDL':pivots,'kind':'interior_Hessian_PD_on_convex_cube'}
 v,t=box[1:];D=((1-v*v)*(1-t*t)).sqrt();b=v*t-D;ub=I(min(box[0].lo,b.lo),max(box[0].hi,b.hi),raw=True);evalbox=[ub,v,t]
 # Along the actual boundary, values of derivatives are enclosed by evalbox.
 ru=evaluate(dp[0],evalbox);assert ru.lo>0,('R_u',ru.pretty())
 bv=t+v*((1-t*t)/(1-v*v)).sqrt();bt=v+t*((1-v*v)/(1-t*t)).sqrt()
 bvv=(1-t*t).sqrt()/((1-v*v)**3).sqrt();btt=(1-v*v).sqrt()/((1-t*t)**3).sqrt();bvt=1-v*t/D
 H=[[evaluate(ddp[i][j],evalbox)for j in range(3)]for i in range(3)]
 BB=[[H[0][0]*bv*bv+2*H[0][1]*bv+H[1][1]+ru*bvv,H[0][0]*bv*bt+H[0][2]*bv+H[0][1]*bt+H[1][2]+ru*bvt],[I(0),H[0][0]*bt*bt+2*H[0][2]*bt+H[2][2]+ru*btt]];BB[1][0]=BB[0][1]
 pivots=ldl(BB)
 return {'halfwidth':str(F(width)),'box':[x.bounds()for x in box],'expanded_u':ub.bounds(),'R_u':ru.bounds(),'boundary_graph_Hessian_LDL':pivots,'kind':'lower_Gram_graph_monotonicity_and_boundary_Hessian_PD'}

def run(source_path,output_path,ctx=None):
 start=time.time();src=Path(source_path);source=ctx if ctx is not None else json.loads(src.read_text());assert source['bits']==BITS;poly={tuple(a):raw(c)for a,c in source['R_coefficients']};rows=[]
 for item in source['local_centers']:
  center=[raw(c)for c in item['center_intervals']];mid=[I((c.lo+c.hi)//2,raw=True)for c in center];q=shift(poly,mid);attempts=[]
  for width in ['.001','.0001','.00001','.000001','.0000001','.00000001','.000000001','.0000000001']:
   try:result=try_box(q,center,width,item['kind']);break
   except AssertionError as e:attempts.append({'halfwidth':width,'failure':str(e)})
  else:raise RuntimeError(('no positive-width local certificate',item['labels'],attempts))
  result.update({'labels':item['labels'],'center_intervals':item['center_intervals'],'failed_larger_widths':attempts});rows.append(result);print('PASS local',item['labels'],width,'seconds',time.time()-start,flush=True)
 out={'status':'CERTIFIED_POSITIVE_WIDTH_CONTACT_NEIGHBORHOODS','source':str(src),'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'implementation_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Rtrue nonnegative on each listed cube intersect actual Gram domain; exact R*=0/grad or boundarygrad=0 from true-root contact theorem; local only, not full domain','bits':BITS,'rows':rows,'seconds':time.time()-start}
 p=Path(output_path);assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');print(out['status'],flush=True)

 return out

if __name__=='__main__':
 import argparse
 p=argparse.ArgumentParser();p.add_argument('--source',default='proof_work/d10_sharpconvex_exact2026_coefficients.json');p.add_argument('--output',default='proof_work/d10_sharpconvex_exact2026_local.json');a=p.parse_args();run(a.source,a.output)
