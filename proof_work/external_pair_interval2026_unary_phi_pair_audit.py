#!/usr/bin/env python3
"""Reproduce the saved-leaf Fraction bounds and pair count without polynomial evaluation."""
from pathlib import Path
from fractions import Fraction as F
from bisect import bisect_left
import hashlib,json
if not __debug__:raise RuntimeError('Do not use Python -O')
def run():
 root=Path(__file__).resolve().parent;src=root/'t2_unary_screen2026_result.json';data=json.loads(src.read_text());tau=F(1,5000)
 assert F(1,10**25)>F(data['rounding_error_upper']);rows=[]
 for chart in data['results']:
  for leaf in chart['leaves']:
   if leaf['kind']!='low_pending':continue
   b=F(leaf['lower_coefficients'][0],1<<data['bits']);assert b<0
   x,dx,y,dy=leaf['location']
   box=[(F(-1)+F(2*x,1<<dx),F(-1)+F(2*(x+1),1<<dx)),(F(-1)+F(2*y,1<<dy),F(-1)+F(2*(y+1),1<<dy))]
   dmin=1+sum(F(0)if lo<=0<=hi else min(lo*lo,hi*hi)for lo,hi in box)
   lower=max(F(0),tau+b/dmin**27)
   rows.append({'sign':chart['sign'],'location':leaf['location'],'brmin_scaled':str(b),'Dmin':str(dmin),'phi_lower':str(lower)})
 values=sorted(F(r['phi_lower'])for r in rows);n=len(values);passed=sum(n-bisect_left(values,tau-v)for v in values)
 assert n==894 and passed==303673
 saved=json.loads((root/'external_pair_interval2026_unary_phi_pair_audit.json').read_text())
 assert saved['source_sha256']==hashlib.sha256(src.read_bytes()).hexdigest() and saved['rows']==rows
 assert saved['ordered_pairs_passing_phi_sum']==passed and saved['ordered_pairs_remaining']==n*n-passed
 out={'status':'PASS_saved_leaf_algebra_and_pair_count','low_boxes':n,'zeros':sum(v==0 for v in values),'max_phi_lower_display':float(values[-1]),'ordered_pairs':n*n,'passed':passed,'remaining':n*n-passed,'new_polynomial_evaluations':0}
 print(json.dumps(out,indent=2));return out
if __name__=='__main__':run()
