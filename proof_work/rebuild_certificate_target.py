"""Rebuild residual from exact kernel, new target, and optionally another exact minorant.
Does not certify positivity. Run verify_high_degree_conditional.py on output.
"""
import argparse,json
from pathlib import Path
from fractions import Fraction as F
from certify_three_point_d4 import add,scale,diag,const

def rebuild(source,dest,target,minorant=None):
 source,dest=Path(source),Path(dest)
 assert not dest.exists()
 d=json.loads(source.read_text());p={tuple(k):F(v)for k,v in d['F_monomial']};target=F(target)
 if minorant:
  m=json.loads(Path(minorant).read_text());d['h_monomial']=m['h_monomial'];d['minorant_dependency']=Path(minorant).name
 h=list(map(F,d['h_monomial']));hs={}
 for axis in range(3):
  for i,v in enumerate(h):
   a=[0]*3;a[axis]=i;a=tuple(a);hs[a]=hs.get(a,F(0))+v
 c=(target+F(3,2)*sum(p.values()))/12
 r=add(hs,scale(p,-7),*(scale(diag(p,i),-1)for i in range(3)),const(-c))
 d.update(target=str(target),c=str(c),source_rebuilt=source.name,residual_monomial=[[list(k),str(v)]for k,v in sorted(r.items())if v],status='exact_components_prepared_global_positivity_UNPROVED')
 dest.write_text(json.dumps(d,indent=2)+'\n');print('Prepared',dest,'target',str(target),'h degree',len(h)-1)

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('source');p.add_argument('dest');p.add_argument('target');p.add_argument('--minorant');a=p.parse_args();rebuild(a.source,a.dest,a.target,a.minorant)
