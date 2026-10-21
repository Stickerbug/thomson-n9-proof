"""Exact single guarded midpoint diagnostics; never a global statement."""
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
from itertools import permutations
import json
BASE=Path(__file__).parent

def add(a,b):return a[0]+b[0],a[1]+b[1]
def mul(a,x):return (a[0]*x,a[1]*x)if x>=0 else(a[1]*x,a[0]*x)
def horner(values,x):
 out=(F(0),F(0))
 for k in range(max(values,default=0),-1,-1):out=add(mul(out,x),values.get(k,(F(0),F(0))))
 return out
def evaluate(poly,point):
 rows={}
 for (i,j,k),v in poly.items():rows.setdefault(i,{}).setdefault(j,{})[k]=v
 a={i:horner({j:horner(v,point[2])for j,v in row.items()},point[1])for i,row in rows.items()}
 return horner(a,point[0])
def interval(d):
 n=1<<int(d['denominator_power_of_two']);return F(int(d['lo_numerator']),n),F(int(d['hi_numerator']),n)
def pack(a):
 return {'lo':str(a[0]),'hi':str(a[1]),'float_lo':float(a[0]),'float_hi':float(a[1]),'sign':'positive'if a[0]>0 else'negative'if a[1]<0 else'contains_zero'}
result=json.loads((BASE/'sharp_global_subsetdiag2026_run2.json').read_text());guard=result['diagnostic_guard'];assert guard
point=tuple(F(z)for z in guard['midpoint']);source=BASE/'sharp_prerequisites2026_parent_replay2/coefficients.json';co=json.loads(source.read_text());poly={tuple(p):interval(c)for p,c in co['R_coefficients']}
scale=1<<200;midpoint={};eps=F(0)
for powers,(lo,hi)in poly.items():
 mid=F(round((lo+hi)*scale/2),scale)
 if mid:midpoint[powers]=mid
 eps+=max(mid-lo,hi-mid)
p={}
for pm in permutations(range(3)):
 for powers,value in midpoint.items():
  k=tuple(powers[j]for j in pm);p[k]=p.get(k,F(0))+value/6
pv=evaluate({k:(v,v)for k,v in p.items()},point);assert pv[0]==pv[1]
R=evaluate(poly,point);L=pv[0]-eps;u,v,t=point;g=1+2*u*v*t-u*u-v*v-t*t
local=guard['local_core_comparisons'];ranked=[]
for r in local:
 deficits=[F(z)for pair in r['signed_containment_deficits']for z in pair];ranked.append({'id':r['id'],'contained':r['contained'],'intersects':r['intersects'],'max_signed_box_core_deficit':str(max(deficits)),'float_max_deficit':float(max(deficits))})
ranked.sort(key=lambda r:F(r['max_signed_box_core_deficit']))
narrow_source=BASE/'narrowroot2026_coefficients.json';narrow=json.loads(narrow_source.read_text());npoly={tuple(k):interval(c)for k,c in narrow['R_coefficients']};NR=evaluate(npoly,point)
contacts=[]
for row in narrow['local_centers']:
 center=tuple(sorted((interval(z)for z in row['center_intervals']),key=lambda z:sum(z)))
 ds=[]
 for z,(a,b)in zip(point,center):
  dl=F(0)if a<=z<=b else min(abs(z-a),abs(z-b));dh=max(abs(z-a),abs(z-b));ds.append((dl,dh))
 dl=max(z[0]for z in ds);dh=max(z[1]for z in ds)
 contacts.append({'labels':row['labels'],'distance_inf_interval':[str(dl),str(dh)],'distance_inf_float':[float(dl),float(dh)],'sorted_center_float':[float(sum(z)/2)for z in center]})
contacts.sort(key=lambda r:F(r['distance_inf_interval'][0]))
classify='unresolved_from_midpoint_alone'
if g>=0 and R[1]<0:classify='EXACT_NEGATIVE_ORIGINAL_R_INTERVAL_AT_GRAM_FEASIBLE_RATIONAL_POINT'
elif g>=0 and L<0 and R[0]>0:classify='TRUE_R_INTERVAL_POSITIVE_BUT_QUANTIZED_SYMMETRIC_p_MINUS_eps_NEGATIVE'
elif g>=0 and L<0 and R[0]<=0<=R[1]:classify='LOWER_POLYNOMIAL_NEGATIVE_WITH_ORIGINAL_COEFFICIENT_INTERVAL_INCONCLUSIVE'
elif g<0:classify='GUARD_MIDPOINT_GRAM_INFEASIBLE_NEEDS_FEASIBLE_POINT_OR_BOX_ANALYSIS'
elif L>=0:classify='POINT_LOWER_NONNEGATIVE_BUT_REPLAY_BERNSTEIN_ROUNDING_OR_BOX_WIDTH_UNRESOLVED'
if g>=0 and NR[1]<0:classify='EXACT_NEGATIVE_NARROWROOT_R_AT_GRAM_FEASIBLE_RATIONAL_POINT'
elif g>=0 and NR[0]>0 and L<0:classify='NARROW_TRUE_R_POSITIVE_BUT_OLD_p_MINUS_eps_NEGATIVE'
elif g>=0 and NR[0]>0 and L>=0:classify='TRUE_R_AND_LOWER_POSITIVE_AT_MIDPOINT_NATIVE_BOUND_INCONCLUSIVE'
report={'status':'EXACT_POINT_DIAGNOSTIC_ONLY','classification':classify,'no_global_conclusion':True,'point':[str(z)for z in point],'point_float':[float(z)for z in point],'Gram_exact':str(g),'Gram_float':float(g),'Gram_feasible':g>=0,'R_original_I384_interval_Horner':pack(R),'symmetric_quantized_p_exact':str(pv[0]),'symmetric_quantized_p_float':float(pv[0]),'eps_exact':str(eps),'eps_float':float(eps),'p_minus_eps_exact':str(L),'p_minus_eps_float':float(L),'native_B_extrema_scaled':{'min':guard['B_min'],'max':guard['B_max']},'native_B_extrema_float':[float(F(int(guard['B_min']),1<<80)),float(F(int(guard['B_max']),1<<80))],'native_G_extrema_float':[float(F(int(guard['G_min']),1<<80)),float(F(int(guard['G_max']),1<<80))],'closest_local_cores':ranked,'boundary_activations':guard['boundary_activation_comparisons'],'guard_path':guard['path'],'guard_levels':guard['levels'],'coefficient_source_sha256':sha256(source.read_bytes()).hexdigest(),'diagnostic_source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'guard_result_sha256':sha256((BASE/'sharp_global_subsetdiag2026_run2.json').read_bytes()).hexdigest()}
report['R_narrowroot_I384_interval_Horner']=pack(NR);report['narrowroot_source_sha256']=sha256(narrow_source.read_bytes()).hexdigest();report['contact_distances_inf']=contacts
out=BASE/'sharp_global_subsetdiag2026_exactpoint_run2.json';assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'classification':classify,'point_float':report['point_float'],'Gram_float':float(g),'R_old_float':[float(z)for z in R],'R_narrow_float':[float(z)for z in NR],'p_minus_eps_float':float(L),'eps_float':float(eps),'nearest_contact':contacts[0],'native_B_float':report['native_B_extrema_float']}))
