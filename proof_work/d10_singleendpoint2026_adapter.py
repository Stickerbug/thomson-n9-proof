if not __debug__:raise RuntimeError('Do not use -O')
import argparse,json,hashlib
from pathlib import Path
from fractions import Fraction as F
BASE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def prepare(source,prefix,execute=False):
 source=Path(source).resolve();prefix=Path(prefix).resolve();d=json.loads(source.read_text());sol=d['solution'];rp=BASE/'sharp_contact_refinement2026_batch3_best_original_data.json';ref=json.loads(rp.read_text());N=sol['N'];assert len(N)==11 and N==ref['third_batch_common_N']==ref['first_batch_original_PSD_seed']['N'];assert all(m.get('N',N)==N for m in ref['third_batch_original_models']);assert d.get('N',N)==N
 ix=d['indices'];assert ix==ref['indices'] and len(ix)==190;seed=[str(F(str(v)))for v in sol['x']];assert len(seed)==190
 for j,(k,a,b)in enumerate(ix):assert F(str(sol['B'][str(k)][a][b]))==F(seed[j])
 ap=BASE/'narrowroot2026_certificate.json';arc=json.loads(ap.read_text());assert arc['indices']==ix and len(arc['rational_basis_transforms'])==11 and len(set(arc['selected_columns']))==len(set(arc['selected_rows']))==33
 paths={k:Path(str(prefix)+'_'+k+'.json')for k in ['seed','basischeck','certificate','coefficients','result']};assert all(not p.exists()for p in paths.values())
 obj={'status':'RATIONAL_SINGLE_ENDPOINT_SEED_ONLY_NOT_A_PROOF','seed':seed,'source':str(source),'source_sha256':sha(source),'indices':ix,'basis':'exact JSON equality to first/third/common N; use archived rationalT1 and pivots','source_dependencies_sha256':{str(p):sha(p)for p in [source,rp,ap,BASE/'d10_sharpconvex_exact2026_seed.json',BASE/'narrowroot2026_root.json',BASE/'narrowroot2026_hermite.json',BASE/'d10_singleendpoint2026_kernel.py',BASE/'narrowroot2026_export.py',Path(__file__).resolve()]}}
 paths['seed'].write_text(json.dumps(obj,indent=2)+'\n');check={'status':'BASIS_AND_INDICES_IDENTICAL_PREPARED_NOT_EXACTIFIED','numerical_model_is_not_strict_PSD':True,'source_sha256':sha(source),'seed_sha256':sha(paths['seed']),'no_exactification_performed_in_prepare_mode':True};paths['basischeck'].write_text(json.dumps(check,indent=2)+'\n');print(check['status'],flush=True)
 if not execute:return
 from d10_singleendpoint2026_kernel import run
 from narrowroot2026_export import export
 ctx=run(str(paths['certificate']),str(ap),True,str(paths['seed']));cert=json.loads(paths['certificate'].read_text());assert cert['status']=='CERTIFIED_CONTACT_AND_POSITIVE_DEFINITE';co=export(str(paths['certificate']),str(paths['coefficients']),ctx)
 result={'status':'CERTIFIED_CONTACT_AND_PSD_AND_TRUE_COEFFICIENTS_NOT_GLOBAL','outputs_sha256':{str(p):sha(p)for k,p in paths.items()if k!='result'},'F_terms':len(co['F_coefficients']),'R_terms':len(co['R_coefficients']),'local_or_global_nonnegativity_claimed':False};paths['result'].write_text(json.dumps(result,indent=2)+'\n');print(result['status'],flush=True)
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--source',required=True);p.add_argument('--prefix',required=True);p.add_argument('--run-exact',action='store_true');a=p.parse_args();prepare(a.source,a.prefix,a.run_exact)
