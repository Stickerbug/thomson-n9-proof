"""Rational interval negative witnesses for finite saved decimal kernels only.
This can disprove nonnegativity of those fixed kernels; it is not a Thomson
counterexample or a theorem about the full sharp-kernel family or true root.
"""
import json,itertools,math,hashlib
from fractions import Fraction as F
from sharp_contact_refinement2026_core import ROOT
from sharp_contact_refinement2026_kernel_domain import KernelBudget
PREFIX='sharp_contact_refinement2026_'


def exact_F(AA,p):
    total=F(0)
    for u,v,t in itertools.permutations(p):
        a=t-u*v;b=(1-u*u)*(1-v*v);Q=[F(1),a]
        for k in range(1,len(AA)-1):Q.append(2*a*Q[-1]-b*Q[-2])
        up=[F(1)];vp=[F(1)]
        for i in range(1,len(AA[0])):up.append(up[-1]*u);vp.append(vp[-1]*v)
        for k,M in enumerate(AA):total+=Q[k]*sum(M[i][j]*up[i]*vp[j] for i in range(len(M)) for j in range(len(M)))/6
    return total


def witness(solution,point,bits=160):
    AA=[[[F(str(v)) for v in row] for row in a] for a in solution['A']];cc=F(str(solution['c']));p=[F(str(v)) for v in point];poly=7*exact_F(AA,p)+sum(exact_F(AA,[F(1),s,s]) for s in p)+cc;scale=1<<bits;lower=F(0);upper=F(0)
    for s in p:
        q=2-2*s;assert q>0
        m=math.isqrt((q.denominator*scale*scale)//q.numerator)
        assert F(m*m,scale*scale)<=1/q<F((m+1)*(m+1),scale*scale)
        lower+=F(m,scale);upper+=F(m+1,scale)
    lo=lower-poly;hi=upper-poly;assert hi<0
    gram=1+2*p[0]*p[1]*p[2]-sum(v*v for v in p);assert gram>0
    Cterms=json.loads((ROOT/'competitive_triple_constraint_certificate.json').read_text())['C_monomial'];C=sum(F(s)*p[0]**e[0]*p[1]**e[1]*p[2]**e[2] for e,s in Cterms);K=KernelBudget().exact_fraction(point);assert C>0 and K>0
    return {'point_decimal':list(map(str,point)),'interval_bits':bits,'R_lower_exact':str(lo),'R_upper_exact':str(hi),'R_lower_float_for_display':float(lo),'R_upper_float_for_display':float(hi),'R_upper_strictly_negative_exact':hi<0,'Gram_exact':str(gram),'Gram_positive_exact':gram>0,'C_exact':str(C),'C_positive_exact':C>0,'Ckernel_exact':str(K),'Ckernel_positive_exact':K>0,'interpretation':'Every saved float is converted through its JSON decimal string into an exact rational; square-root terms enclosed by integer isqrt. This certifies failure only of the fixed saved finite-decimal kernel.'}


def main():
    names=['sharp_contact_refinement2026_results.json','sharp_contact_refinement2026_competitive_validation.json','sharp_contact_refinement2026_batch2_results.json'];data={n:json.loads((ROOT/n).read_text()) for n in names};rows=[]
    old=data[names[0]]['best_solution'];point=data[names[1]]['best_strict_feasible']['point'];rows.append({'case':'first_batch_PSD_model','model_json':str(ROOT/names[0]),'iteration':old['iteration'],'witness':witness(old,point)})
    second=data[names[2]];row=second['history'][-1];rows.append({'case':'second_batch_final_NOT_PSD','model_json':str(ROOT/names[2]),'iteration':row['iteration'],'witness':witness(row['solution'],row['validation']['best_strict_feasible']['point'])})
    result={'status':'fixed_saved_decimal_kernel_nonnegativity_refuted_by_exact_rational_intervals','warning':'SHARP CERTIFICATE DISCOVERY STILL OPEN. No Thomson counterexample, no SDP family infeasibility, no exact-root certificate. Existing necessary-domain lemmas are dependency certificates.','algorithm':'For q=2-2s and scale=2^160, m=isqrt(floor(scale^2/q)) gives m/scale<=q^-1/2<(m+1)/scale. All F and c values and C/Gram/Ckernel use exact Fraction arithmetic.','global_verifier_re_run':False,'source_model_sha256':{n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in names},'witnesses':rows};out=ROOT/(PREFIX+'fixed_model_obstructions.json');assert not out.exists();out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps([{'case':row['case'],'R_upper_float':row['witness']['R_upper_float_for_display'],'positive_Gram_C_Ckernel':True} for row in rows],indent=2))

if __name__=='__main__':main()
