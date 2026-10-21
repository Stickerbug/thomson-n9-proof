"""Uniform gap for standard two-point LP bounds; not a bound on Emin itself."""
if not __debug__: raise RuntimeError('Assertions are required')
from fractions import Fraction as F
from pathlib import Path
import json
from certify_all_degree import I,S,run

def main():
 data=run();m=F(1,1000)
 for row in data['positive_moments']:
  assert F(int(row['bounds']['lo_numerator']),S)>m
 assert F(72**2*176,49*230)<(9-m)**2
 r=I(F(data['root_lower']),F(data['root_upper']))
 a,b=r*r/2-1,r/2
 f=lambda t:1/(2-2*t).sqrt()
 D=(f(a)+f(b))/2-f((a+b)/2)
 gap=D/(F(1,12)+4/m)
 assert gap.lo>I(F(1,100000)).hi
 result={'status':'certified_method_obstruction','uniform_moment_lower':str(m),'tail_check':'72^2*176/(49*230)<(9-1/1000)^2','node_multiplicities':[6,12],'midpoint_convexity_defect':D.bounds(),'gap_lower_interval':gap.bounds(),'conclusion':'Every standard finite-degree Legendre LP minorant has B < E_star - 1/100000. Its supremum cannot approach E_star.','scope':'p=sum a_l P_l <= f on [-1,1), a_l>=0 for l>=1; N=9; B=(81a0-9p(1))/2. Also applies to uniformly absolutely convergent Legendre expansions with finite sum a_l and the same defect identity.'}
 out=Path(__file__).with_name('uniform_pair_lp_gap_v1_certificate.json')
 if out.exists():assert json.loads(out.read_text())==result
 else:out.write_text(json.dumps(result,indent=2)+'\n')
 print(result['conclusion']);print('Display only gap lower:',float(F(gap.lo,S)))
 return result
if __name__=='__main__':main()
