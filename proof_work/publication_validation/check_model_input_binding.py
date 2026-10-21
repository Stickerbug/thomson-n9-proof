"""Independent exact binding of exported inputs to frozen interval and local-box data."""
from pathlib import Path
from fractions import Fraction as Q
from itertools import permutations
from hashlib import sha256
import json
D=Path(__file__).resolve().parent
CO='860f37384e2b1d704956269b63acbf0b8ee6faad84e30f5857c8b2e3acb715a2'
LOC='c97df856e866f0ec464c16948e506162e48697950e653984198a7558b8e3beec'
def interval(z):
    bits=z['denominator_power_of_two']
    if type(bits) is not int or not 0<=bits<=4096:raise ValueError('invalid interval denominator')
    lo,hi=Q(int(z['lo_numerator']),1<<bits),Q(int(z['hi_numerator']),1<<bits)
    if lo>hi:raise ValueError('reversed source interval')
    return lo,hi

def main():
    cr=(D.parent/'d10_relative_normal_exact2026_coefficients.json').read_bytes();lr=(D.parent/'d10_relative_normal_exact2026_locals.json').read_bytes();ir=(D/'sharp_root_inputs.json').read_bytes();co=json.loads(cr);loc=json.loads(lr);v=json.loads(ir)
    f={tuple(p):interval(z) for p,z in co['F_coefficients']};fm={tuple(p):Q(z) for p,z in v['F_mid_sym']};support=set(f)|set(fm)
    for p in tuple(support):support.update(permutations(p))
    rawerror=sum(max(abs(f.get(p,(Q(0),Q(0)))[0]-fm.get(p,Q(0))),abs(f.get(p,(Q(0),Q(0)))[1]-fm.get(p,Q(0)))) for p in support)
    symeps=Q(0);midok=True
    for p in support:
        orbit=list(permutations(p));lo=sum(f.get(q,(Q(0),Q(0)))[0] for q in orbit)/6;hi=sum(f.get(q,(Q(0),Q(0)))[1] for q in orbit)/6;mid=fm.get(p,Q(0));symeps+=max(abs(mid-lo),abs(hi-mid));midok&=mid==(lo+hi)/2
    localsok=[]
    for i,(row,reg) in enumerate(zip(loc['rows'],v['local_regions'])):
        center=tuple(tuple(map(Q,z)) for z in reg['center']);w=Q(reg['halfwidth']);core=tuple((hi-w,lo+w) for lo,hi in center);supplied=tuple(tuple(map(Q,z)) for z in reg['core']);oldbox=tuple(map(interval,row['box']))
        localsok.append({'id':reg['id'],'expected_row_id':reg['id']=='new-local-'+str(i)+'-012','core_matches_center_width':core==supplied,'core_inside_original_certified_box':len(core)==len(oldbox)==3 and all(a<=l<=r<=b for (l,r),(a,b) in zip(core,oldbox))})
    checks={'co_digest':sha256(cr).hexdigest()==CO,'locals_digest':sha256(lr).hexdigest()==LOC,'locals_same_model_digest':loc['source_sha256']==CO,'exact_symmetric_midpoints':midok,'sym_error_equals_exported_eps':symeps==Q(v['epsF']),'direct_raw_coefficient_L1_error_bounded':rawerror<=Q(v['epsF']),'constant_interval_exact':interval(co['c'])==tuple(map(Q,v['c_interval'])),'all_twelve_local_boxes':len(loc['rows'])==len(v['local_regions'])==len(localsok)==12,'every_local_binding':all(all(z[k] for k in ('expected_row_id','core_matches_center_width','core_inside_original_certified_box')) for z in localsok)}
    result={'status':'PASS_EXPORTED_MODEL_INPUT_BINDING' if all(checks.values()) else 'FAIL','checks':checks,'raw_coefficient_L1_error':str(rawerror),'symmetrized_L1_error':str(symeps),'exported_epsF':v['epsF'],'F_support':len(support),'local_bindings':localsok,'root_input_sha256':sha256(ir).hexdigest(),'source_hashes':{'co':sha256(cr).hexdigest(),'locals':sha256(lr).hexdigest()},'scope':'Verifies midpoint, error, constant and local-core derivation from the frozen source data. Validity of the original algebraic coefficient enclosures and local nonnegativity proofs remains assumed, not independently generated or proved.'}
    with (D/'independent_model_input_binding.json').open('x') as stream:json.dump(result,stream,indent=2);stream.write(chr(10))
    print(json.dumps(result));return 0 if all(checks.values()) else 1
if __name__=='__main__':raise SystemExit(main())
