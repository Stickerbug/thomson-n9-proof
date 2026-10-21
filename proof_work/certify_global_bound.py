"""Exact outward dyadic verification of constants in global_bound_notes.md.
No floating-point arithmetic enters the proof computation.
"""
from dyadic_interval import I
import json
from pathlib import Path
s=I(6).sqrt(); v=s/5
a=(-1+s)/5; b=(-1-s)/5
fa=1/(2-2*a).sqrt(); fb=1/(2-2*b).sqrt()
ga=1/((2-2*a)*(2-2*a).sqrt())
gb=1/((2-2*b)*(2-2*b).sqrt())
C=(ga-gb)/(4*v)
D=((ga+gb)/2-(fa-fb)/(2*v))/(2*v*v)
B=(fa-fb)/(2*v)-D*v*v
A=(fa+fb)/2-C*v*v
c=[A+B/5+C/25+D/125,B+2*C/5+3*D/25,C+3*D/5,D]
p=[c[0]+c[2]/3,c[1]+3*c[3]/5,2*c[2]/3,2*c[3]/5]
assert all(x.lo>0 for x in p)
B0=(81*p[0]-9*sum(p))/2
B0_alt=I(9)/2*((4+s/4)*fa+(4-s/4)*fb)
assert (B0-B0_alt).lo<=0<=(B0-B0_alt).hi
kappa=(I(1)/2-(c[0]-c[1]+c[2]-c[3]))/(I(2)/5)**2
assert kappa.lo>0
alpha=p[1]/2; beta=6*kappa/25
eta=(2*s-3)/5
G=8*eta**2+I(9)/25
improvement=G/(16/beta+9/alpha)
lower=B0+improvement
assert lower.lo>I('25.71015').hi
assert lower.hi<I('25.71016').lo
result={'description':'Global bound constants; analytic proof in global_bound_notes.md',
        'legendre_coefficients':[x.bounds() for x in p],
        'B0':B0.bounds(),'kappa':kappa.bounds(),'alpha':alpha.bounds(),'beta':beta.bounds(),
        'G':G.bounds(),'improvement':improvement.bounds(),'lower_bound':lower.bounds(),
        'certified_safe_lower_bound':'25.71015',
        'display_only':{k:x.pretty() for k,x in [('B0',B0),('kappa',kappa),('improvement',improvement),('lower_bound',lower)]}}
Path(__file__).with_name('global_bound_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result['display_only'],indent=2))
print('PASS: E > 25.71015 for all nine-point configurations, given analytic lemma.')
