if not __debug__:
 raise RuntimeError('Run without -O')
"""Candidate membership in minimizer restricted domain, interval arithmetic."""
import json,hashlib
from pathlib import Path
from fractions import Fraction as F
from dyadic_interval import I,BITS
from certify_pair_moments import L,U
base=Path('proof_work');r=I(L,U);names='ABCDFG';nodes=[1-I('1.5')*r*r,2*r*r-1,r*r/2-1,I('-0.5'),r/2,-r]
E=sum((w/(2-2*x).sqrt()for w,x in zip([6,3,6,3,12,6],nodes)),I(0));energy_upper=F(E.hi,2**BITS)
cert=json.loads((base/'nonsharp_d10_root25_7599205_v10.json').read_text());poly={tuple(a):F(c)for a,c in cert['residual_monomial']};B=F(cert['target']);upper=F(json.loads((base/'pair056_optimized_certificate.json').read_text())['U']);assert upper==F('25.75998653126983156407570227376049402866');budget=7*(upper-B)
report=json.loads((base/'nonsharp_d10_root25_7599205_v10_result.json').read_text())
assert report['status']=='certified' and report['pending']==0 and report['degree']==10
assert F(report['target'])==B==F('25.7599205')
assert report['domain']==['-1','14/25']
assert report['model_sha256']==hashlib.sha256((base/'nonsharp_d10_root25_7599205_v10.json').read_bytes()).hexdigest()
assert len(poly)==807
assert all(F(v)>0 for row in report['psd_pivots'] for v in row)
assert report['minorant_nodes']>0
# Nested Horner, exact rational coefficients and outward arithmetic.
def horner(p,pt,axis=0):
 if axis==3:return I(p.get((),F(0)))
 n=max((a[0]for a in p),default=0);ans=I(0)
 for j in reversed(range(n+1)):
  q={a[1:]:c for a,c in p.items()if a[0]==j};ans=ans*pt[axis]+horner(q,pt,axis+1)
 return ans
geom=json.loads((base/'candidate_triple_types_v1.json').read_text())['triangle_types'];rows=[]
for item in geom:
 point=[nodes[names.index(a)]for a in item['labels']];dotmargin=min(x.lo-I('-0.9957').hi for x in point);uppermargin=min(I('.56').lo-x.hi for x in point);assert dotmargin>0 and uppermargin>0
 res=horner(poly,point);margin=I(budget)-res;assert res.lo>=0 and margin.lo>0
 rows.append({'labels':item['labels'],'multiplicity':item['multiplicity'],'old_R':res.bounds(),'old_R_display':res.pretty(),'budget_margin':margin.bounds(),'margin_display':margin.pretty(),'strict_dot_lower_margin_raw':str(dotmargin),'strict_dot_upper_margin_raw':str(uppermargin)})
E=sum((w/(2-2*x).sqrt()for w,x in zip([6,3,6,3,12,6],nodes)),I(0));assert E.hi<I(upper).lo;assert E.hi<I('25.759986531269832').lo
ans={'status':'CERTIFIED_ALL12_CANDIDATE_TYPES_STRICTLY_INSIDE_RESTRICTED_DOMAIN','root_interval':[L,U],'bits':BITS,'minimizer_dot_interval':'(-9957/10000,14/25)','old_lower_bound':str(B),'candidate_energy_upper':str(upper),'old_R_budget':str(budget),'old_R_budget_display':I(budget).pretty(),'rows':rows,'source_sha256':{n:hashlib.sha256((base/n).read_bytes()).hexdigest()for n in ['nonsharp_d10_root25_7599205_v10.json','nonsharp_d10_root25_7599205_v10_result.json','candidate_triple_types_v1.json','pair056_optimized_certificate.json']},'source_report_checks':{'status':report['status'],'pending':report['pending'],'target':report['target'],'model_sha256':report['model_sha256'],'domain':report['domain'],'residual_terms':len(poly)},'candidate_energy_interval':E.bounds(),'scope':'candidate membership only; no new sharp residual certification'}
p=base/'restricted_sharp_theorem2026_v2_source_corrected_candidate_check.json';p.write_text(json.dumps(ans,indent=2)+'\n');print('PASS all12 candidate types, budget',I(budget).pretty());print('smallest budget slack',min(float(F(int(v['budget_margin']['lo_numerator']),2**BITS))for v in rows));print('oldR range',min(float(F(int(v['old_R']['lo_numerator']),2**BITS))for v in rows),max(float(F(int(v['old_R']['hi_numerator']),2**BITS))for v in rows))
