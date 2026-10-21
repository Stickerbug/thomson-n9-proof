if not __debug__:
 raise RuntimeError('Run verifier without -O or PYTHONOPTIMIZE')
"""Independent exact-only replay of sharp prerequisites; never runs away search."""
import argparse,json,hashlib,time,runpy
from pathlib import Path
from fractions import Fraction as F
from dyadic_interval import I,S,BITS
from certify_pair_moments import L,U,derivative
from contact_minorant_factor_v1 import run as hermite
from d10_sharpconvex_exact2026_kernel import run as kernel
from d10_sharpconvex_exact2026_export import export
from d10_sharpconvex_exact2026_local import run as local
BASE=Path(__file__).resolve().parent

def refine_root():
 left,right=F(L),F(U);assert 0<left<right<1
 assert derivative(I(left)).hi<0<derivative(I(right)).lo
 initial=[str(left),str(right)];steps=0;fallbacks=0
 while right-left>F(1,2**300):
  steps+=1;assert steps<1000
  mid=(left+right)/2;d=derivative(I(mid))
  if d.hi<0:left=mid
  elif d.lo>0:right=mid
  else:
   # On(0,1), Esecond>4sqrt3/r^3>1. Mean-value theorem bounds root distance.
   rad=F(max(abs(d.lo),abs(d.hi)),S);assert rad>0
   old=right-left;left=max(left,mid-rad);right=min(right,mid+rad);assert right-left<old;fallbacks+=1
 rr=I(left,right);E=I(3).sqrt()+2*I(3).sqrt()/rr+I('1.5')/(1-rr*rr).sqrt()+6/(4-rr*rr).sqrt()+12/(2-rr).sqrt()+6/(2+2*rr).sqrt()
 pair=json.loads((BASE/'pair056_optimized_certificate.json').read_text());upper=F(pair['U']);assert upper==F('25.75998653126983156407570227376049402866')
 assert E.hi<I(upper).lo
 return {'root_initial':initial,'root_refined':[str(left),str(right)],'root_width':str(right-left),'target_width':'1/2^300','bisections':steps,'mean_value_fallbacks':fallbacks,'E_star':E.bounds(),'E_display':E.pretty(),'U':str(upper),'U_minus_E_lower':str(upper-F(E.hi,S)),'convexity_proof':'Esecond=4sqrt3/r^3+(3/2)(1+2r²)/(1−r²)^(5/2)+6(4+2r²)/(4−r²)^(5/2)+9/(2−r)^(5/2)+18/(2+2r)^(5/2)>1 for0<r<1'}

def verify_geometry():
 import sympy as sp
 geo=json.loads((BASE/'d10_contact_left_geometry_v1.json').read_text());r=sp.symbols('r');rows=[[sp.sympify(v,locals={'r':r})for v in row]for row in geo['rows']];W=sp.Matrix(rows);assert W.shape==(12,45)
 determinant=sp.factor(W[:,geo['minor_columns']].det());assert sp.cancel(determinant+36*r)==0
 return {'rows':12,'columns':45,'exact_minor_determinant':str(determinant),'rank_at_true_root':12,'allcolumn_WM_zero':'mathematical dependency: coordinate symmetry + GkNk=0 and differentiated complete kernel sum; not inferred from saved status','rhs_compatibility':'first11 zero, last7Eprime; follows exact geometric row theorem and true stationary root'}

def run(outdir):
 start=time.time();outdir=Path(outdir).resolve();assert not outdir.exists(),'Output directory must be new';outdir.mkdir(parents=True)
 print('replaying rational pair056 verifier',flush=True);runpy.run_path(str(BASE/'verify_pair056_saved.py'),run_name='__main__')
 root=refine_root();print('PASS refined root and strict candidate energy<U',root['E_display'],flush=True)
 extras=[F(-1),F(-9,10),F(-2,5),F(-1,5),F(1,10),F(9,20),F(13,25),F(14,25)];actual=hermite(extras);savedH=json.loads((BASE/'contact_minorant_factor_v1.json').read_text())['cases'][1];assert actual==savedH
 (outdir/'hermite.json').write_text(json.dumps(actual,indent=2)+'\n');geometry=verify_geometry();print('PASS exact Hermite reconstruction and geometric W minor',flush=True)
 cert=BASE/'d10_sharpconvex_exact2026_certificate.json';freshcert=outdir/'kernel.json';kernel(str(freshcert),str(cert))
 # Context reconstruction computes LU/LDL again; no floating discovery models or solver are read.
 ctx=kernel(None,str(freshcert),True);newcoef=outdir/'coefficients.json';co=export(str(freshcert),str(newcoef),ctx)
 oldco=json.loads((BASE/'d10_sharpconvex_exact2026_coefficients.json').read_text());keys=['R_coefficients','F_coefficients','H_coefficients_ascending','E_star','c','F111','local_centers'];assert all(co[k]==oldco[k]for k in keys)
 freshlocal=outdir/'local.json';lo=local(str(newcoef),str(freshlocal),co);oldlocal=json.loads((BASE/'d10_sharpconvex_exact2026_local.json').read_text());assert lo['rows']==oldlocal['rows'];assert len(lo['rows'])==12
 names=['dyadic_interval.py','certify_pair_moments.py','certify_all_degree.py','verify_pair056_saved.py','pair056_optimized_certificate.json','candidate_low_rank.py','candidate_low_rank_notes.md','candidate_triple_types_v1.json','contact_minorant_factor_v1.py','contact_minorant_factor_v1.json','d10_contact_left_geometry_v1.py','d10_contact_left_geometry_v1.json','d10_exact_contact_psd_seed1_v1.json','d10_sharpconvex_exact2026_kernel.py','d10_sharpconvex_exact2026_certificate.json','d10_sharpconvex_exact2026_export.py','d10_sharpconvex_exact2026_coefficients.json','d10_sharpconvex_exact2026_local.py','d10_sharpconvex_exact2026_local.json','d10_exact_contact_jets_v1.py','d10_sharpconvex_exact2026_closure_checklist_zh.md',Path(__file__).name]
 sourcehash={n:hashlib.sha256((BASE/n).read_bytes()).hexdigest()for n in names}
 result={'status':'CERTIFIED_SHARP_PREREQUISITES_NOT_GLOBAL','scope':'pair reduction, stationary root and energy upper, true Hermite minorant reconstruction, exact contact and PSD, coefficient identity and12 full positivewidth local domains; no away search or global coverage','root_and_energy':root,'geometry':geometry,'Hermite_case_identical':True,'Hermite_minorant_proof':'f28>0 and product of14 squared factors in Hermite remainder; numerical K not needed','exact_kernel_status':json.loads(freshcert.read_text())['status'],'math_array_identity':{k:True for k in keys},'PSD_replayed_from_rational_seed_T1':True,'local_rows_identical':True,'local_rows':len(lo['rows']),'E_enclosure_original_root':co['E_star'],'c':co['c'],'F111':co['F111'],'source_sha256':sourcehash,'artifacts_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in [freshcert,newcoef,freshlocal,outdir/'hermite.json']},'seconds':time.time()-start}
 assert result['exact_kernel_status']=='CERTIFIED_CONTACT_AND_POSITIVE_DEFINITE'
 (outdir/'prerequisites.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'],'seconds',result['seconds'],flush=True);return result
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--outdir',required=True);a=p.parse_args();run(a.outdir)
