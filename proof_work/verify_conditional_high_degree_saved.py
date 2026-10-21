"""Exact-only replay of saved rational conditional Coulomb minorants. No interpolation."""
if not __debug__:raise RuntimeError('Assertions must be active')
from fractions import Fraction as F
from pathlib import Path
import argparse,json,time
from certify_conditional_h19 import plus,times,check
ap=argparse.ArgumentParser();ap.add_argument('certificate');ap.add_argument('--out');args=ap.parse_args();start=time.time();src=Path(args.certificate);data=json.loads(src.read_text());h=[F(x)for x in data['h_monomial']];eps=F(data['error_upper']);lo,hi=map(F,data['domain'])
assert(lo,hi)==(F(-1),F(14,25))and len(h)==data['degree']+1 and h[-1]!=0
assert 0<eps<=F(1,1000000000)
pos=check(h,lo,hi);minor=check(plus([F(1)],[-x for x in times([F(2),F(-2)],times(h,h))]),lo,hi)
q=plus(h,[eps]);upper=check(plus(times([F(2),F(-2)],times(q,q)),[F(-1)]),lo,hi)
result={'status':'certified','source':str(src.resolve()),'degree':data['degree'],'domain':[str(lo),str(hi)],'error_upper':str(eps),'positive_nodes':pos,'minorant_nodes':minor,'error_nodes':upper,'arithmetic':'Fraction Bernstein, no floating point discovery','seconds':time.time()-start}
if args.out:
 out=Path(args.out);assert not out.exists();out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result),flush=True)
