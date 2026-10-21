if not __debug__:raise RuntimeError('Do not use -O')
import json,time,hashlib,signal
from pathlib import Path
from fractions import Fraction as F
from dyadic_interval import I,S,BITS
BASE=Path(__file__).resolve().parent

def save(name,obj):
 p=BASE/name;assert not p.exists();p.write_text(json.dumps(obj,indent=2)+'\n');return p

def solve(rhs,ctx):
 v=[rhs[i]for i in ctx['sel']]
 for k,q,factors in ctx['LU_ops']:
  v[k],v[q]=v[q],v[k]
  for i,fac in factors.items():v[i]-=fac*v[k]
 U=ctx['LU_upper'];delta=[I(0)]*33
 for i in range(32,-1,-1):delta[i]=(v[i]-sum((U[i][j]*delta[j]for j in range(i+1,33)),I(0)))/U[i][i]
 return delta

def psd(xx,ctx):
 lookup={tuple(a):j for j,a in enumerate(ctx['indices'])};out=[]
 for k,N in enumerate(ctx['N']):
  n=len(N)
  if not n:continue
  B=[[xx[lookup[k,min(i,j),max(i,j)]]for j in range(n)]for i in range(n)];L=[[I(int(i==j))for j in range(n)]for i in range(n)];D=[]
  for i in range(n):
   d=B[i][i]-sum((L[i][j]**2*D[j]for j in range(i)),I(0));assert d.lo>0,('endpointPSD',k,i,d.bounds());D.append(d)
   for j in range(i+1,n):L[j][i]=(B[j][i]-sum((L[j][a]*L[i][a]*D[a]for a in range(i)),I(0)))/d
  out.append({'k':k,'positive_pivots':[d.bounds()for d in D],'B_enclosures':[[d.bounds()for d in row]for row in B],'smallest_lower_display':min(float(F(d.lo,S))for d in D)})
 return out

def main():
 start=time.time();signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('affine family hard120second budget')));signal.alarm(120)
 import numpy as np
 from d10_affinefamily2026_kernel import run
 from narrowroot2026_export import export,raw
 from narrowroot2026_pointcheck import horner,pack
 pc=json.loads((BASE/'narrowroot2026_pointcheck.json').read_text());mid=lambda a:float(F(int(a['lo_numerator'])+int(a['hi_numerator']),2*S));H=np.array([[mid(a)for a in row]for row in pc['Hessian_at_initial_point']]);g=np.array([mid(a)for a in pc['gradient_at_initial_point']]);newton=-np.linalg.solve(H,g);print('NUMERICAL_DIAGNOSTIC Newtonstep',newton.tolist(),'predicted_drop',float(g@newton/2),flush=True)
 src=BASE/'sharp_contact_refinement2026_batch3_best_original_data.json';data=json.loads(src.read_text());models=[data['first_batch_original_PSD_seed'],*data['third_batch_original_models']];assert len(models)==3;common=data['third_batch_common_N'];assert models[0]['N']==common;assert all(m.get('N',common)==common for m in models)
 archived=BASE/'narrowroot2026_certificate.json';ctx=run(None,str(archived),True);assert ctx['indices']==[tuple(a)for a in data['indices']];M=ctx['M'];rhs=ctx['rhs'];root=json.loads((BASE/'narrowroot2026_root.json').read_text());point=[F(a)for a in pc['negative_witness']['point']];endpointrows=[]
 for ei,model in enumerate(models):
  seed=[F(str(a))for a in model['x']];assert len(seed)==190
  for j,(k,a,b)in enumerate(ctx['indices']):assert F(str(model['B'][str(k)][a][b]))==seed[j]
  res=[rhs[i]-sum((v*s for v,s in zip(M[i],seed)),I(0))for i in range(45)];delta=solve(res,ctx);xx=[I(v)for v in seed]
  for i,j in enumerate(ctx['cols']):xx[j]+=delta[i]
  errors=[rhs[i]-sum((v*s for v,s in zip(M[i],xx)),I(0))for i in range(45)];assert all(e.lo<=0<=e.hi for e in errors);ldls=psd(xx,ctx)
  cert=save(f'd10_affinefamily2026_endpoint{ei}_certificate.json',{'status':'CERTIFIED_EXACT_CONTACT_AND_PSD_AFFINE_ENDPOINT','root_interval':root['root_refined'],'seed':[str(a)for a in seed],'seed_model_index':ei,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'selected_columns':ctx['cols'],'selected_rows':ctx['sel'],'delta_enclosures':[d.bounds()for d in delta],'reduced_solution_enclosures':[a.bounds()for a in xx],'all45_contact_error_enclosures':[a.bounds()for a in errors],'PSD_LDL':ldls,'exactness':'33 selected equations solved with same invertible LU;45 equations follow same rank33/W/Eprime compatibility theorem, not mere interval zero containment'})
  newctx={**ctx,'x':xx};coef=BASE/f'd10_affinefamily2026_endpoint{ei}_coefficients.json';co=export(str(cert),str(coef),newctx);p={tuple(a):raw(v)for a,v in co['R_coefficients']};value=horner(p,[I(a)for a in point]);endpointrows.append({'index':ei,'certificate':str(cert),'certificate_sha256':hashlib.sha256(cert.read_bytes()).hexdigest(),'coefficients':str(coef),'coefficients_sha256':hashlib.sha256(coef.read_bytes()).hexdigest(),'R_terms':len(p),'R_at_old_negative_witness':pack(value),'R_coefficient_sumwidth':str(sum((F(v.hi-v.lo,S)for v in p.values()),F(0))),'smallest_PSD_pivot_lower_display':min(row['smallest_lower_display']for row in ldls)});print('PASS affine endpoint',ei,'R_at_witness',pack(value),'seconds',time.time()-start,flush=True)
 shared=save('d10_affinefamily2026_shared.json',{'root_interval':root['root_refined'],'indices':[list(a)for a in ctx['indices']],'selected_columns':ctx['cols'],'selected_rows':ctx['sel'],'N_enclosures':[[[a.bounds()for a in row]for row in N]for N in ctx['N']],'rational_basis_transforms':json.loads(archived.read_text())['rational_basis_transforms'],'contact_M_enclosures':[[a.bounds()for a in row]for row in M],'rhs_enclosures':[a.bounds()for a in rhs],'LU_upper_enclosures':[[a.bounds()for a in row]for row in ctx['LU_upper']],'LU_ops':[[k,q,{str(i):a.bounds()for i,a in factors.items()}]for k,q,factors in ctx['LU_ops']],'LU_pivots':ctx['LU_pivots'],'Hermite_source':str(BASE/'narrowroot2026_hermite.json'),'Hermite_source_sha256':hashlib.sha256((BASE/'narrowroot2026_hermite.json').read_bytes()).hexdigest(),'Hermite_total_nodes_with_multiplicity':28})
 result={'status':'CERTIFIED_THREE_EXACT_CONTACT_PSD_ENDPOINTS_AND_AFFINE_FAMILY_NOT_GLOBAL','source':str(src),'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'model_keys':['first_batch_original_PSD_seed','third_batch_original_models[0]','third_batch_original_models[1]'],'endpoints':endpointrows,'shared':str(shared),'shared_sha256':hashlib.sha256(shared.read_bytes()).hexdigest(),'affine_theorem':'For rational weights w_j with sum w_j=1, nonselected157 coordinates x(w)=sum w_j seed_j; selected33 solve same fixed invertible M_selected and fixed rhs. Since M(sum w_j x_j)=sum w_j rhs=rhs, uniqueness gives x(w)=sum w_j x_j. Thus B,A,F and c are affine; shared H and sum w_j=1 give R_H(w)=sum w_j R_H_j. If all w_j>=0, all B(w) positive definite by convexity. Arbitrary signed affine weights require new PSD verification.','combination_rule':'For rational nonnegative weights summing to1, combine interval coefficients using outward I384 rational multiplication/addition. Monomial supports may be unioned; absent coefficients are exact0. No new33LU or polynomial export is required. New local or global residual assertions still require their own proof.','Newton_direction_numerical_diagnostic':newton.tolist(),'Newton_quadratic_predicted_drop':float(g@newton/2),'seconds':time.time()-start};save('d10_affinefamily2026_result.json',result);signal.alarm(0);print(result['status'],'seconds',result['seconds'],flush=True)
if __name__=='__main__':main()
