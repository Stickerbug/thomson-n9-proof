if not __debug__:raise RuntimeError('Do not use -O')
import json,time,hashlib
from pathlib import Path
from fractions import Fraction as F
from dyadic_interval import I,S
BASE=Path(__file__).resolve().parent

def diff(p,axis):
 out={}
 for a,c in p.items():
  if a[axis]:b=list(a);b[axis]-=1;out[tuple(b)]=a[axis]*c
 return out

def horner(p,pt):
 if not pt:return p.get((),I(0))
 n=max((a[0]for a in p),default=0);v=I(0)
 for j in range(n,-1,-1):v=v*pt[0]+horner({a[1:]:c for a,c in p.items()if a[0]==j},pt[1:])
 return v

def raw(v):return I(int(v['lo_numerator']),int(v['hi_numerator']),raw=True)
def pack(v):return {**v.bounds(),'float_lo':float(F(v.lo,S)),'float_hi':float(F(v.hi,S))}
def gram(p):u,v,t=p;return 1-u*u-v*v-t*t+2*u*v*t

def exact_eval(p,pt):
 powers=[[t**i for i in range(28)]for t in pt];lo=hi=F(0)
 for a,c in p.items():
  m=powers[0][a[0]]*powers[1][a[1]]*powers[2][a[2]];x,y=F(c.lo,S)*m,F(c.hi,S)*m;lo+=min(x,y);hi+=max(x,y)
 return {'lo':str(lo),'hi':str(hi),'float_lo':float(lo),'float_hi':float(hi)},lo,hi

def main():
 start=time.time();source=BASE/'narrowroot2026_coefficients.json';pointsrc=BASE/'sharp_global_subsetdiag2026_exactpoint_run2.json';data=json.loads(source.read_text());p={tuple(a):raw(c)for a,c in data['R_coefficients']};point=[F(v)for v in json.loads(pointsrc.read_text())['point']];pt=[I(v)for v in point];dp=[diff(p,i)for i in range(3)];ddp=[[diff(dp[i],j)for j in range(3)]for i in range(3)];r=horner(p,pt);g=[horner(q,pt)for q in dp];H=[[horner(q,pt)for q in row]for row in ddp];n=3;LL=[[I(int(i==j))for j in range(n)]for i in range(n)];D=[];ldl_fail=None
 for i in range(n):
  d=H[i][i]-sum((LL[i][j]**2*D[j]for j in range(i)),I(0));D.append(d)
  if d.lo<=0<=d.hi:ldl_fail='pivot_contains_zero';break
  for j in range(i+1,n):LL[j][i]=(H[j][i]-sum((LL[j][k]*LL[i][k]*D[k]for k in range(i)),I(0)))/d
 axis=max(range(3),key=lambda i:abs(g[i].lo+g[i].hi));assert g[axis].lo>0 or g[axis].hi<0;direction=-1 if g[axis].lo>0 else 1;steps=[];witness=None
 print('point R',pack(r),'gradient',[pack(v)for v in g],'LDL',[pack(v)for v in D],flush=True)
 for exponent in range(12,5,-1):
  delta=F(direction,10**exponent);nextpt=point[:];nextpt[axis]+=delta;gg=gram(nextpt);assert gg>0 and all(F(-1)<v<F(14,25)for v in nextpt);v=horner(p,[I(t)for t in nextpt]);step={'axis':axis,'signed_step':str(delta),'point':[str(t)for t in nextpt],'Gram_exact':str(gg),'R':pack(v)};steps.append(step);print('step',step,flush=True)
  if v.hi<0:
   exact,elo,ehi=exact_eval(p,nextpt);assert ehi<0;assert F(v.lo,S)<=elo<=ehi<=F(v.hi,S);step['independent_exact_Fraction_monomial_evaluation']=exact;step['gradient']=[pack(horner(q,[I(t)for t in nextpt]))for q in dp];witness=step;break
 out={'status':'CERTIFIED_NEGATIVE_TRUE_SHARP_RESIDUAL_WITNESS'if witness else'FINITE_POINT_GRADIENT_DIAGNOSTIC_NO_NEGATIVE_FOUND','scope':'true algebraic residual from narrow root coefficient enclosures; a witness disproves this residual certificate, not the Thomson candidate configuration','source':str(source),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'point_source':str(pointsrc),'point_source_sha256':hashlib.sha256(pointsrc.read_bytes()).hexdigest(),'point':[str(v)for v in point],'Gram_exact':str(gram(point)),'R_at_initial_point':pack(r),'gradient_at_initial_point':[pack(v)for v in g],'gradient_max_abs_lower':float(F(max(min(abs(v.lo),abs(v.hi))if v.lo*v.hi>0 else 0 for v in g),S)),'Hessian_at_initial_point':[[pack(v)for v in row]for row in H],'Hessian_LDL_pivots':[pack(v)for v in D],'Hessian_LDL_failure':ldl_fail,'Hessian_PD_at_point':len(D)==3 and all(v.lo>0 for v in D),'descent_axis':axis,'descent_direction':direction,'steps':steps,'negative_witness':witness,'seconds':time.time()-start};target=BASE/'narrowroot2026_pointcheck.json';assert not target.exists();target.write_text(json.dumps(out,indent=2)+'\n');print(out['status'],'seconds',out['seconds'],flush=True)
if __name__=='__main__':main()
