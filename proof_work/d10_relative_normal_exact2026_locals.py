if not __debug__:raise RuntimeError('No -O')
import json,time,signal,hashlib
from pathlib import Path
from fractions import Fraction as F
from dyadic_interval import I,S
from narrowroot2026_export import raw
import narrowroot2026_local_formulas as loc
import narrowroot2026_precondition as pre
from narrowroot2026_kernel import run
BASE=Path(__file__).resolve().parent
PREFIX='d10_relative_normal_exact2026'
def save(suffix,obj):
 p=BASE/(PREFIX+suffix);assert not p.exists();p.write_text(json.dumps(obj,indent=2)+'\n');return p
def main():
 start=time.time();signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('locals and originalA comparison hard240second budget')));signal.alarm(240)
 cp=BASE/(PREFIX+'_certificate.json');source=BASE/(PREFIX+'_coefficients.json');co=json.loads(source.read_text());datafile=BASE/'d10_relative_normal2026_results.json';d=json.loads(datafile.read_text());sol=d['solution'];ctx=run(None,str(cp),True);lookup={tuple(a):j for j,a in enumerate(ctx['indices'])};NN=ctx['N'];xx=ctx['x'];As=[];Nerr=F(0);Aerr=F(0)
 for k,N in enumerate(NN):
  n=len(N);m=11-k;B=[[xx[lookup[k,min(a,b),max(a,b)]]for b in range(n)]for a in range(n)];A=[[sum((N[a][i]*sum((B[a][b]*N[b][j]for b in range(n)),I(0))for a in range(n)),I(0))for j in range(m)]for i in range(m)];As.append(A)
  for a in range(n):
   for i in range(m):
    z=N[a][i]-I(F(str(sol['N'][k][i][a])));Nerr=max(Nerr,F(max(abs(z.lo),abs(z.hi)),S))
  numericA=sol['A'][str(k)] if isinstance(sol['A'],dict)else sol['A'][k]
  for i in range(m):
   for j in range(m):
    z=A[i][j]-I(F(str(numericA[i][j])));Aerr=max(Aerr,F(max(abs(z.lo),abs(z.hi)),S))
 comparison={'status':'TRUE_ROOT_REDUCED_TO_ORIGINAL_A_ENCLOSURES_AND_SAVED_MODEL_COMPARISON','source_sha256':hashlib.sha256(datafile.read_bytes()).hexdigest(),'certificate_sha256':hashlib.sha256(cp.read_bytes()).hexdigest(),'N_coordinate_rule':'stored original N has columns; exact ctx N has rows; compare ctxN[k][a][i] with savedN[k][i][a]','max_N_entry_difference_upper':str(Nerr),'max_N_entry_difference_display':float(Nerr),'max_originalA_entry_difference_upper':str(Aerr),'max_originalA_entry_difference_display':float(Aerr),'A_true_enclosures':[[[v.bounds()for v in row]for row in A]for A in As],'N_true_enclosures':[[[v.bounds()for v in row]for row in N]for N in NN],'basis_transforms':json.loads(cp.read_text())['rational_basis_transforms'],'comparison_is_not_an_equality_claim_for_floating_model':True};save('_originalA_comparison.json',comparison);print('PASS originalA comparison',float(Aerr),'N difference',float(Nerr),'seconds',time.time()-start,flush=True)
 poly={tuple(a):raw(v)for a,v in co['R_coefficients']};rows=[];complete=False
 try:
  for item in co['local_centers']:
   center=[raw(v)for v in item['center_intervals']];mid=[I((v.lo+v.hi)//2,raw=True)for v in center];q=loc.shift(poly,mid);attempts=[]
   try:
    _,Hc=pre.evaluate_box(q,center,'0',item['kind']);W=pre.center_transform(Hc)
    for power in range(3,19):
     width=F(1,10**power)
     try:row,H=pre.evaluate_box(q,center,width,item['kind'],W);break
     except AssertionError as e:attempts.append({'halfwidth':str(width),'failure':str(e)})
    else:raise AssertionError('no positivewidth passed down to1e-18')
    row.update({'labels':item['labels'],'center_intervals':item['center_intervals'],'congruence_W':[[str(v)for v in rr]for rr in W],'W_invertibility_proof':'exact Fraction unit lower triangular and W L=I checked','preconditioned_Hessian':[[v.bounds()for v in rr]for rr in pre.transform(H,W)],'failed_larger_widths':attempts,'status':'CERTIFIED_LOCAL_POSITIVE_WIDTH'})
   except AssertionError as e:row={'labels':item['labels'],'status':'LOCAL_CHECK_FAILED','failure':str(e),'attempts':attempts}
   rows.append(row);print(row['status'],item['labels'],row.get('halfwidth'),time.time()-start,flush=True)
  complete=True
 finally:
  out={'status':'CERTIFIED_TWELVE_LOCAL_BOXES_NOT_GLOBAL'if complete and len(rows)==12 and all(r['status']=='CERTIFIED_LOCAL_POSITIVE_WIDTH'for r in rows)else'LOCAL_PROOF_INCOMPLETE','source':str(source),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'scope':'RH>=0 on Gram domain in each certified cube using exact45-contact compatibility theorem plus interval Hessian/graph proof; no global nonnegativity','bits':co['bits'],'rows':rows,'seconds':time.time()-start,'sources_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest()for p in [Path(__file__),BASE/'narrowroot2026_local_formulas.py',BASE/'narrowroot2026_precondition.py',BASE/'d10_exact_contact_jets_v1.py',cp]}};save('_locals.json',out)
 signal.alarm(0);print(out['status'],'seconds',out['seconds'],flush=True)
if __name__=='__main__':main()
