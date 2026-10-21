if not __debug__:raise RuntimeError('Do not use -O')
import json,hashlib,argparse
from pathlib import Path
from fractions import Fraction as F
from dyadic_interval import I,S
BASE=Path(__file__).resolve().parent

def raw(v):return I(int(v['lo_numerator']),int(v['hi_numerator']),raw=True)
def combine(weights,output):
 weights=[F(w)for w in weights];assert len(weights)==3 and sum(weights)==1 and min(weights)>=0
 resultpath=BASE/'d10_affinefamily2026_result.json';result=json.loads(resultpath.read_text());coeff=[];cert=[]
 for row in result['endpoints']:
  cp=Path(row['coefficients']);bp=Path(row['certificate']);assert hashlib.sha256(cp.read_bytes()).hexdigest()==row['coefficients_sha256'];assert hashlib.sha256(bp.read_bytes()).hexdigest()==row['certificate_sha256'];coeff.append(json.loads(cp.read_text()));cert.append(json.loads(bp.read_text()))
 def weighted(vals):return sum((w*raw(v)for w,v in zip(weights,vals)),I(0)).bounds()
 out=coeff[0].copy()
 for key in ['R_coefficients','F_coefficients']:
  ps=[{tuple(a):v for a,v in co[key]}for co in coeff];support=sorted(set().union(*(p.keys()for p in ps)));zero=I(0).bounds();out[key]=[[list(a),weighted([p.get(a,zero)for p in ps])]for a in support]
 for key in ['c','F111']:out[key]=weighted([co[key]for co in coeff])
 out['reduced_solution_enclosures']=[weighted([ce['reduced_solution_enclosures'][i]for ce in cert])for i in range(190)]
 out['source_sha256']={str(resultpath):hashlib.sha256(resultpath.read_bytes()).hexdigest(),**{row['coefficients']:row['coefficients_sha256']for row in result['endpoints']},**{row['certificate']:row['certificate_sha256']for row in result['endpoints']}}
 out['affine_family']={'weights':[str(w)for w in weights],'exact_contacts':'inherited from fixed33LU affine uniqueness theorem','PSD':'convex combination of individually strictly PD reduced blocks; no new LDL needed','residual_nonnegativity':'NOT CLAIMED','construction':'exact rational weights; outward I384 interval combination; shared true root and H27'}
 target=Path(output);assert not target.exists();target.write_text(json.dumps(out,indent=2)+'\n');return out
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--weights',nargs=3,required=True);p.add_argument('--output',required=True);a=p.parse_args();combine(a.weights,a.output);print('PASS affine coefficient combination; no global nonnegativity assertion')
