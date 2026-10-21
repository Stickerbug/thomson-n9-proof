#!/usr/bin/env python3
"""Read-only fixed-point exact budget signs and independent 80-digit actualf.
No optimization or new sampled point. Charged to the <=90-second diagnostic.
"""
from pathlib import Path
from fractions import Fraction as F
import ast,itertools,json,time,hashlib
import mpmath as mp
BASE=Path(__file__).resolve().parent;P='d12_competitive_probe2026_'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run():
 start=time.monotonic();inp=BASE/(P+'results.json');data=json.loads(inp.read_text());outpath=BASE/(P+'verified_points.json');assert not outpath.exists();remaining=90-data['elapsed_seconds'];assert remaining>5
 oldpath=BASE/'nonsharp_d10_root25_7599205_v10.json';old=json.loads(oldpath.read_text());reportpath=BASE/'nonsharp_d10_root25_7599205_v10_result.json';report=json.loads(reportpath.read_text());assert report['model_sha256']==sha(oldpath)and report['status']=='certified'and report['pending']==0
 terms=[(tuple(e),F(c))for e,c in old['residual_monomial']];budget=F(data['budget_exact']);upper=json.loads((BASE/'pair056_optimized_certificate.json').read_text());assert budget==7*(F(upper['U'])-F(old['target']))
 evaluator=BASE/'sharp_contact_refinement2026_export.py';text=evaluator.read_text();node=next(n for n in ast.parse(text).body if isinstance(n,ast.FunctionDef)and n.name=='mpR');ns={'mp':mp,'itertools':itertools};exec(compile(ast.Module(body=[node],type_ignores=[]),str(evaluator),'exec'),ns);mp.mp.dps=80
 sol=data['new_model'];rows=[]
 points=[('random_minimum',data['search']['random']['worst_point']),('DE_best',data['best_strict_numeric_eligible']['point'])]
 for name,p in points:
  assert time.monotonic()-start<remaining-2
  z=[F(str(x))for x in p];pw=[[x**k for k in range(28)]for x in z];r=sum(c*pw[0][e[0]]*pw[1][e[1]]*pw[2][e[2]]for e,c in terms);g=1+2*z[0]*z[1]*z[2]-sum(x*x for x in z);k=budget-r
  high=ns['mpR'](sol['A'],sol['c'],p)
  row={'name':name,'point':p,'R_old_exact':str(r),'R_old_decimal':str(mp.mpf(r.numerator)/r.denominator),'Gram_exact':str(g),'Gram_float':float(g),'budget_minus_Rold_exact':str(k),'budget_minus_Rold_float':float(k),'all_dot_bounds_exact':all(F(-1)<=x<=F(14,25)for x in z),'exact_Gram_positive':g>0,'exact_budget_margin_positive':k>0,'actualf_high_precision':high};rows.append(row)
 elapsed=time.monotonic()-start;out={'warning':'Exact signs concern only old rational polynomial/domain at specified finite-decimal triples. New actualf evaluated at 80 digits is numerical discovery, not interval proof or a Thomson counterexample.','model_sha256':data['snapshot']['sha256'],'iteration':data['selected_iteration'],'budget_exact':str(budget),'rows':rows,'primary_probe_seconds':data['elapsed_seconds'],'fixed_point_verification_seconds':elapsed,'total_numerical_seconds':data['elapsed_seconds']+elapsed,'numerical_seconds_budget':90,'dependencies':{str(p):sha(p)for p in [inp,oldpath,reportpath,evaluator,Path(__file__)]}}
 assert out['total_numerical_seconds']<90
 outpath.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2));return out
if __name__=='__main__':run()
