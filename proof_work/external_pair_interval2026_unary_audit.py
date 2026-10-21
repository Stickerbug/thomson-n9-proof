#!/usr/bin/env python3
"""Independent static-input/rectangle audit of the parent's finished unary screen.
Does not call the parent's run(), rebuild degree-54 polynomials, or certify low cells.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import hashlib,json
import numpy as np
from dyadic_interval import I,S
if not __debug__:raise RuntimeError('Assertions must remain enabled')
BASE=Path(__file__).resolve().parent;P='external_pair_interval2026_'
def run():
 source=BASE/'t2_unary_screen2026.py';path=BASE/'t2_unary_screen2026_result.json';result=json.loads(path.read_text())
 for name,h in result['dependencies'].items():assert hashlib.sha256((BASE/name).read_bytes()).hexdigest()==h,name
 modelpath=BASE/'nonsharp_d10_root25_7599205_v10.json';closed=json.loads((BASE/'nonsharp_d10_root25_7599205_v10_result.json').read_text())
 assert closed['status']=='certified'and closed['pending']==0 and hashlib.sha256(modelpath.read_bytes()).hexdigest()==closed['model_sha256']
 assert result['status']=='partial_unary_screen_not_pair_certificate' and F(result['threshold'])==F(1,5000)
 Q=int(result['anchor_denominator']);assert Q==1<<128
 U,V,T=map(F,result['triangle']);g=1+2*U*V*T-U*U-V*V-T*T;assert g>0
 b=(1-I(U)**2).sqrt();actual=[[I(1),I(0),I(0)],[I(U),b,I(0)],[I(V),(T-I(U)*V)/b,I(g).sqrt()/b]]
 for row,intervals in zip(result['anchors_dyadic'],actual):
  for k,x in zip(row,intervals):assert F(k,Q)<=F(x.lo,S)<=F(x.hi,S)<F(k+1,Q)
 terms=[(tuple(e),F(c))for e,c in json.loads(modelpath.read_text())['residual_monomial']]
 assert all(sum(e)<=27 for e,c in terms)
 derivative=sum(abs(c)*(e[1]+e[2])for e,c in terms);err=F(18,Q)*derivative
 assert (1+F(3,Q))**26<2 and err==F(result['rounding_error_upper']) and err<F(1,10**25)
 charts=[];total_low=F(0);total_low_boxes=0
 assert [r['sign']for r in result['results']]==[1,-1]
 for chart in result['results']:
  grid=np.zeros((128,128),dtype=np.int16);kindgrid=np.zeros_like(grid);counts=Counter();area=Counter();low=[];maxd=0
  for leaf in chart['leaves']:
   x,dx,y,dy=leaf['location'];assert 0<=dx<=7 and 0<=dy<=7 and 0<=x<1<<dx and 0<=y<1<<dy
   assert dx+dy<=result['max_depth'];maxd=max(maxd,dx+dy)
   ix=x<<(7-dx);ex=(x+1)<<(7-dx);iy=y<<(7-dy);ey=(y+1)<<(7-dy)
   grid[ix:ex,iy:ey]+=1;kind=leaf['kind'];counts[kind]+=1;area[kind]+=F(4,1<<(dx+dy))
   if kind=='phi_high':assert leaf['lower_coefficients'][0]>=0;kindgrid[ix:ex,iy:ey]=1
   elif kind=='excluded_anchor_or_disk':assert max(leaf['lower_coefficients'][1:])>0;kindgrid[ix:ex,iy:ey]=2
   elif kind=='low_pending':assert dx+dy>=result['max_depth'];low.append(leaf['location']);kindgrid[ix:ex,iy:ey]=3
   else:assert kind=='budget_pending';low.append(leaf['location']);kindgrid[ix:ex,iy:ey]=4
  assert np.all(grid==1)and int(grid.sum())==128**2
  assert dict(counts)==chart['counts'] and {k:str(v)for k,v in area.items()}==chart['area'] and sum(area.values(),F(0))==4
  assert chart['nodes']==2*len(chart['leaves'])-1 and counts.get('budget_pending',0)==0
  lowarea=area['low_pending']+area['budget_pending'];total_low+=lowarea;total_low_boxes+=len(low)
  charts.append({'sign':chart['sign'],'grid_shape':[128,128],'grid_min':int(grid.min()),'grid_max':int(grid.max()),'grid_sum':int(grid.sum()),
   'nodes':chart['nodes'],'leaves':len(chart['leaves']),'counts':dict(counts),'exact_areas':{k:str(v)for k,v in area.items()},'max_depth':maxd,
   'low_rectangles':low,'classification_grid_sha256':hashlib.sha256(kindgrid.tobytes()).hexdigest()})
 fraction=total_low/8;pairfraction=fraction*fraction
 out={'status':'static_input_and_terminal_rectangular_cover_verified','global_pair_certificate':False,'independent_degree54_reconstruction':False,
  'input_hashes_match_result':True,'old_residual_report_model_hash_matches':True,'anchor_rounding_rechecked':True,'perturbation_rechecked':True,
  'rounding_error_upper':str(err),'error_allowance':'1/10000000000000000000000000','charts':charts,
  'low_rectangles_total':total_low_boxes,'low_chart_area_exact':str(total_low),'low_fraction_of_two_square_charts':str(fraction),
  'ordered_pair_rectangles':total_low_boxes**2,'pair_parameter_area_fraction':str(pairfraction),'pair_parameter_area_fraction_display':float(pairfraction),
  'parameter_area_reduction_factor':float(1/pairfraction),
  'static_review':[
   'Q128 floor anchors enclose exact unit-anchor coordinates with error <1/Q each. Therefore each anchor-dot error is <=3/Q.',
   'Total polynomial degree<=27 and (1+3/Q)^26<2 imply phi error <=18/Q times sum|c|(j+k), strictly below EPS=1e-25.',
   'The nested loop builds sum c_jk*N_i^j*N_j^k*D^(27-j-k), summed over three fixed-edge residuals. D=(1+a^2+b^2)>0.',
   'Lower Bernstein numerator minus ceil((TAU+EPS)*upper Bernstein D^27) coefficientwise is a valid lower polynomial. Nonnegative coefficients imply true phi>=TAU after anchor perturbation.',
   'Cap polynomial uses cap+3/Q; positivity excludes actual anchor-dot<=cap points. Disk r^2>1 exclusion is valid because two hemisphere disks already cover S2.',
   'Each current split uses Python object integers and floor half-sums, so all lower coefficient directions remain valid.',
   'If either phi(q) or phi(r)>=1/5000, then W>=(1/5000)/5=1/25000 using the old certificate phi>=0 and psi>=0 on feasible actual triples.'
  ],
  'limitations':[
   'This audit checks source algebra, exact inputs, hashes and a complete nonoverlapping terminal rectangle cover. It does not independently rebuild or reevaluate every degree-54 Bernstein acceptance.',
   'The 894 low rectangles and 799236 ordered pairs are unresolved. Parameter area fractions are not sphere-area fractions or proof completeness measures.',
   'The result is for the fixed rational T2 only, without a surrounding triangle interval. It does not prove the Thomson global optimum.',
   'For standalone future replay, add certify_all_degree.py and the closed old-residual report hashes as explicit dependencies; the present audit verifies that report/model link separately.'
  ],
  'dependencies':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in [source,path,modelpath,BASE/'nonsharp_d10_root25_7599205_v10_result.json',BASE/'certify_all_degree.py',Path(__file__)]}}
 (BASE/(P+'unary_audit.json')).write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({k:out[k]for k in ['status','low_rectangles_total','low_chart_area_exact','low_fraction_of_two_square_charts','ordered_pair_rectangles','pair_parameter_area_fraction','parameter_area_reduction_factor']},indent=2))
 print('chart_cover',[(r['sign'],r['grid_min'],r['grid_max'],r['grid_sum'],r['counts'])for r in charts])
 return out
if __name__=='__main__':run()
