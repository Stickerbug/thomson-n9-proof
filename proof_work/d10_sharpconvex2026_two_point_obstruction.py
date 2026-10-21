"""Finite exact interval obstruction to the THREE specified affine kernels only."""
import json,time,hashlib
from pathlib import Path
from fractions import Fraction as F
from dyadic_interval import I,S
from narrowroot2026_pointcheck import horner,raw,pack,gram
BASE=Path(__file__).parent;start=time.monotonic();out=BASE/'d10_sharpconvex2026_two_point_obstruction.json';assert not out.exists()
P=[F(14,25)]*3;Q=list(map(F,['-.7319927153030016','-.7319927162082746','.34931898965249153']));lam=F(1,10**7)
assert all(F(-1)<z<=F(14,25)for p in [P,Q]for z in p)and gram(P)>0 and gram(Q)>0
rows=[];sources={};commonH=None
for j in range(3):
 src=BASE/f'd10_affinefamily2026_endpoint{j}_coefficients.json';sources[str(src.resolve())]=hashlib.sha256(src.read_bytes()).hexdigest();d=json.loads(src.read_text());assert d['bits']==384 and d['status']=='TRUE_ALGEBRAIC_COEFFICIENT_ENCLOSURES_NOT_RATIONAL_SUBSTITUTE'
 if commonH is None:commonH=d['H_coefficients_ascending']
 else:assert commonH==d['H_coefficients_ascending']
 pr={tuple(e):raw(c)for e,c in d['R_coefficients']};hc=list(map(raw,commonH));vs=[]
 for point in [P,Q]:
  ipt=list(map(I,point));rh=horner(pr,ipt);loss=I(0)
  for x in ipt:
   h=I(0)
   for c in reversed(hc):h=h*x+c
   loss+=I(1)/(2-2*x).sqrt()-h
  vs.append({'R_H':pack(rh),'Hermite_loss':pack(loss),'R_f':pack(rh+loss)} )
 gh=raw(vs[1]['R_H'])+lam*raw(vs[0]['R_H']);gf=raw(vs[1]['R_f'])+lam*raw(vs[0]['R_f']);assert gh.hi<0 and gf.hi<0
 rows.append({'endpoint':j,'P':vs[0],'Q':vs[1],'G_H_Q_plus_lambda_P':pack(gh),'G_f_Q_plus_lambda_P':pack(gf),'strict_negative_upper_H':gh.hi<0,'strict_negative_upper_f':gf.hi<0})
result={'status':'STRICT_TWO_POINT_OBSTRUCTION_FOR_THESE_THREE_SPECIFIED_AFFINE_KERNELS','scope':'Conditional on the endpoint coefficient enclosure construction. For any nonnegative weights summing to1 over these exact three endpoints, G=R(Q)+lambda*R(P)<0, hence R cannot be nonnegative at both valid Gram points. This excludes this finite convex hull only, not the kernel family or Thomson candidate. Applies both true H residual and actual f residual.','P':list(map(str,P)),'Q':list(map(str,Q)),'Gram_P_exact':str(gram(P)),'Gram_Q_exact':str(gram(Q)),'lambda':str(lam),'source_sha256':sources,'endpoint_evaluations':rows,'seconds':time.monotonic()-start};out.open('x').write(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':result['status'],'G_f_upper':[r['G_f_Q_plus_lambda_P']['float_hi']for r in rows],'G_H_upper':[r['G_H_Q_plus_lambda_P']['float_hi']for r in rows],'seconds':result['seconds']}),flush=True)
