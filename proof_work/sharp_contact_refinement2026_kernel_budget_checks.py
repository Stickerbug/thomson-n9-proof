"""Exact point checks of a new necessary budget, conditional on existing certificates.
No global positivity verification is re-run here. Existing reports are hash-bound.
"""
import json,hashlib
from pathlib import Path
from fractions import Fraction as F
import mpmath as mp
ROOT=Path(__file__).parent
PREFIX='sharp_contact_refinement2026_'


def evaluate(point,terms):
    p=list(map(lambda x:F(str(x)),point));return sum(F(s)*p[0]**e[0]*p[1]**e[1]*p[2]**e[2] for e,s in terms)


def main():
    mp.mp.dps=80
    names=['nonsharp_d10_root25_7599205_v10.json','nonsharp_d10_root25_7599205_v10_result.json','conditional_h27_certificate.json','pair056_optimized_certificate.json']
    raw={n:(ROOT/n).read_bytes() for n in names};data={n:json.loads(v) for n,v in raw.items()};hashes={n:hashlib.sha256(v).hexdigest() for n,v in raw.items()}
    model=data[names[0]];report=data[names[1]];assert report['status']=='certified' and report['pending']==0
    assert report['model_sha256']==hashes[names[0]] and model['target']==report['target']
    U=F(data[names[3]]['U']);B=F(model['target']);budget=7*(U-B)
    old=json.loads((ROOT/(PREFIX+'competitive_validation.json')).read_text());second=json.loads((ROOT/(PREFIX+'batch2_results.json')).read_text());rows=[]
    points=[('first_PSD_worst',old['best_strict_feasible']['point'])]+[('batch2_round'+str(r['iteration']),r['validation']['best_strict_feasible']['point']) for r in second['history']]
    def dec(q):return mp.nstr(mp.mpf(q.numerator)/q.denominator,80)
    for name,p in points:
        residual=evaluate(p,model['residual_monomial']);value=budget-residual;rows.append({'case':name,'point_decimal':list(map(str,p)),'R_old_exact_fraction':str(residual),'R_old_decimal_80digit':dec(residual),'C_kernel_exact_fraction':str(value),'C_kernel_decimal_80digit':dec(value),'C_kernel_sign_exact':1 if value>0 else -1 if value<0 else 0,'survives_new_necessary_condition':value>=0})
    result={'status':'new_necessary_condition_derived_from_existing_certificates_with_exact_point_evaluation','global_verifier_re_run':False,'warning':'Existing global positivity, minorant and PSD reports are dependencies, not re-proved by this script. Sharp models remain numerical discovery; a failed residual model is not a Thomson counterexample.','lemma':{'assumptions':['n=9, competitive E<=U','all pair dot products lie in [-1,14/25] by existing pair exclusion','existing model: h<=f, A_k PSD, R_old>=0 on Gram domain; B=12c-1.5F111'],'identity':'E-B = sum_{i<j}(f(sij)-h(sij)) + (1/7)sum_{i<j<k} R_old(sij,sik,sjk) + (1/6)sum_{i,j,k=1}^9 F_old(sij,sik,sjk)','nonnegative_terms':'Each pair defect and each distinct-triple R_old is nonnegative. The full ordered sum of F_old is nonnegative by the three-point PSD addition theorem; individual F values need not be nonnegative.','conclusion':'For every distinct triple, R_old<=7(E-B)<=7(U-B); hence C_kernel=7(U-B)-R_old>=0.','budget_factor_7':'9-2=7','U_exact':str(U),'B_exact':str(B),'seven_U_minus_B_exact':str(budget),'seven_U_minus_B_decimal':dec(budget)},'dependencies':{'sha256':hashes,'report_model_hash_match':True,'existing_global_report':{'status':report['status'],'nodes':report['nodes'],'pending':report['pending'],'bits':report['bits'],'maxdepth':report['maxdepth']},'residual_terms':len(model['residual_monomial'])},'exact_point_checks':rows}
    out=ROOT/(PREFIX+'kernel_budget_certificate.json');assert not out.exists();out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='exact_point_checks'},indent=2));print('EXACT_POINT_SIGNS',[(r['case'],r['C_kernel_sign_exact']) for r in rows])

if __name__=='__main__':main()
