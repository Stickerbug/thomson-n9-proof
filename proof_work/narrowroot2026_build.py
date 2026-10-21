if not __debug__:
 raise RuntimeError('Run without -O')
import json,time,hashlib
from pathlib import Path
from fractions import Fraction as F
from dyadic_interval import I,S,BITS
from certify_pair_moments import L,U,derivative
BASE=Path(__file__).resolve().parent

def widthsum(co,key):return sum((F(int(v['hi_numerator'])-int(v['lo_numerator']),S)for _,v in co[key]),F(0))
def save(name,obj):
 p=BASE/name;assert not p.exists();p.write_text(json.dumps(obj,indent=2)+'\n');return p

def build():
 start=time.time();frozen=['d10_sharpconvex_exact2026_kernel.py','d10_sharpconvex_exact2026_export.py','contact_minorant_factor_v1.py','contact_minorant_factor_v1.json','d10_sharpconvex_exact2026_certificate.json','d10_sharpconvex_exact2026_coefficients.json','d10_sharpconvex_exact2026_local.json','local_precondition2026_boxes.json'];oldhash={n:hashlib.sha256((BASE/n).read_bytes()).hexdigest()for n in frozen}
 left,right=F(L),F(U);assert derivative(I(left)).hi<0<derivative(I(right)).lo;steps=0;fallback=0
 while right-left>F(1,2**350):
  steps+=1;assert steps<1000;mid=(left+right)/2;d=derivative(I(mid))
  if d.hi<0:left=mid
  elif d.lo>0:right=mid
  else:
   rad=F(max(abs(d.lo),abs(d.hi)),S);assert rad>0;old=right-left;left=max(left,mid-rad);right=min(right,mid+rad);assert right-left<old;fallback+=1
 dl,du=derivative(I(left)),derivative(I(right));assert dl.hi<0<du.lo
 root={'status':'STRICT_STATIONARY_ROOT_REFINED','root_refined':[str(left),str(right)],'root_initial':[L,U],'width':str(right-left),'width_target':'2^-350','steps':steps,'mean_value_fallbacks':fallback,'derivative_left':dl.bounds(),'derivative_right':du.bounds(),'uniqueness':'Esecond>4sqrt3/r^3>1 on(0,1)'};save('narrowroot2026_root.json',root);print('PASS narrow root350',steps,flush=True)
 import narrowroot2026_kernel as nk
 import narrowroot2026_hermite as nh
 from narrowroot2026_export import export,raw
 import narrowroot2026_local_formulas as loc
 import narrowroot2026_precondition as pre
 extras=[F(-1),F(-9,10),F(-2,5),F(-1,5),F(1,10),F(9,20),F(13,25),F(14,25)];cases=[nh.run(),nh.run(extras)];save('narrowroot2026_hermite.json',{'status':'certified_contact_minorant_and_error_bound','root_interval':root['root_refined'],'domain':['-1','14/25'],'cases':cases,'minorant_proof':'Hermite remainder f28>0 times product14 squared factors; true shared stationary root'})
 cert=BASE/'narrowroot2026_certificate.json';nk.run(str(cert),str(BASE/'d10_sharpconvex_exact2026_certificate.json'),seed_input=str(BASE/'d10_sharpconvex_exact2026_seed.json'));certdata=json.loads(cert.read_text());assert certdata['status']=='CERTIFIED_CONTACT_AND_POSITIVE_DEFINITE'
 ctx=nk.run(None,str(cert),True);coefpath=BASE/'narrowroot2026_coefficients.json';co=export(str(cert),str(coefpath),ctx);poly={tuple(a):raw(v)for a,v in co['R_coefficients']}
 # Re-certify the SAME physical outer boxes, not narrowed center +/- same width.
 reports={}
 for mode,name in [('original','d10_sharpconvex_exact2026_local.json'),('preconditioned','local_precondition2026_boxes.json')]:
  targets=json.loads((BASE/name).read_text());bylabel={tuple(v['labels']):v for v in targets['rows']};rows=[]
  for item in co['local_centers']:
   target=bylabel[tuple(item['labels'])];center=[raw(v)for v in item['center_intervals']];midpoint=[I((v.lo+v.hi)//2,raw=True)for v in center];q=loc.shift(poly,midpoint);box=[raw(v)for v in target['box']];assert all(b.lo<=v.lo<=v.hi<=b.hi for b,v in zip(box,center))
   if mode=='original':row=loc.try_box(q,center,target['halfwidth'],item['kind'],box_override=box)
   else:
    _,Hc=pre.evaluate_box(q,center,'0',item['kind']);W=pre.center_transform(Hc);row,H=pre.evaluate_box(q,center,target['halfwidth'],item['kind'],W,box_override=box);row.update({'congruence_W':[[str(v)for v in rr]for rr in W],'W_determinant':'1','preconditioned_Hessian':[[v.bounds()for v in rr]for rr in pre.transform(H,W)]})
   assert row['box']==target['box'];row.update({'labels':item['labels'],'center_intervals':item['center_intervals'],'exact_same_physical_box':True});rows.append(row);print('PASS narrow',mode,item['labels'],flush=True)
  report={'status':'CERTIFIED_SAME_PHYSICAL_LOCAL_BOXES_NARROW_ROOT','source':str(coefpath),'source_sha256':hashlib.sha256(coefpath.read_bytes()).hexdigest(),'prior_source':name,'prior_sha256':oldhash[name],'mode':mode,'rows':rows,'scope':'same full physical12 local boxes re-proved for same true algebraic polynomial, narrower coefficient enclosures; not global'};outname='narrowroot2026_local.json'if mode=='original'else'narrowroot2026_precondition_boxes.json';save(outname,report);reports[mode]=outname
 oldco=json.loads((BASE/'d10_sharpconvex_exact2026_coefficients.json').read_text());oldw=widthsum(oldco,'R_coefficients');neww=widthsum(co,'R_coefficients');assert neww<oldw;assert neww<F(1,10**60)
 assert oldhash=={n:hashlib.sha256((BASE/n).read_bytes()).hexdigest()for n in frozen}
 upper=F(json.loads((BASE/'pair056_optimized_certificate.json').read_text())['U']);rr=I(left,right);E=I(3).sqrt()+2*I(3).sqrt()/rr+I('1.5')/(1-rr*rr).sqrt()+6/(4-rr*rr).sqrt()+12/(2-rr).sqrt()+6/(2+2*rr).sqrt();assert E.hi<I(upper).lo
 own=['narrowroot2026_root.json','narrowroot2026_hermite.py','narrowroot2026_hermite.json','narrowroot2026_kernel.py','narrowroot2026_certificate.json','narrowroot2026_export.py','narrowroot2026_coefficients.json','narrowroot2026_local_formulas.py','narrowroot2026_precondition.py','narrowroot2026_local.json','narrowroot2026_precondition_boxes.json',Path(__file__).name]
 out={'status':'CERTIFIED_NARROW_ROOT_PSD_HERMITE_COEFFICIENTS_AND_SAME_LOCAL_BOXES_NOT_GLOBAL','root':root,'old_R_coefficient_sumwidth':str(oldw),'new_R_coefficient_sumwidth':str(neww),'old_width_display':float(oldw),'new_width_display':float(neww),'uniform_midpoint_error':str(neww/2),'error_improvement_ratio_display':float(oldw/neww),'E_star_refined':E.bounds(),'c':co['c'],'F111':co['F111'],'local_reports':reports,'same_physical_boxes_original_and_preconditioned':True,'frozen_original_sources_sha256':oldhash,'new_sources_sha256':{n:hashlib.sha256((BASE/n).read_bytes()).hexdigest()for n in own},'seconds':time.time()-start};save('narrowroot2026_result.json',out);print(out['status'],'oldwidth',float(oldw),'newwidth',float(neww),'seconds',out['seconds'],flush=True)
if __name__=='__main__':build()
