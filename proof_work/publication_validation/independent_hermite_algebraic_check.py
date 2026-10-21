"""Finite algebraic Hermite minorant via exact divisibility and interval Bernstein quotient."""
from pathlib import Path
from fractions import Fraction as Rat
from math import comb
from hashlib import sha256
from time import monotonic
import json
from independent_integer_interval import Box,BITS,S,InvalidMath
from independent_hermite_RH import hermite
ROOT=Path(__file__).resolve().parent;PREFIX='independent_hermite_algebraic_';Z=Box(0)
def need(ok,msg):
 if not ok:raise InvalidMath(msg)
def mul(a,b):
 c=[Box(0)for _ in range(len(a)+len(b)-1)]
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]=c[i+j]+x*y
 return c
def power_to_bernstein(q,a,b):
 n=len(q)-1;power=[Box(0)for _ in q]
 for k,c in enumerate(q):
  for j in range(k+1):power[j]=power[j]+c*comb(k,j)*Box(a)**(k-j)*Box(b-a)**j
 return [sum((power[j]*Rat(comb(i,j),comb(n,j))for j in range(i+1)),Box(0))for i in range(n+1)]
def split(b):
 left=[b[0]];right=[b[-1]];level=b
 while len(level)>1:
  level=[(a+c)/2 for a,c in zip(level,level[1:])];left.append(level[0]);right.append(level[-1])
 return left,list(reversed(right))
def val(q,x):
 v=Box(0)
 for c in reversed(q):v=v*x+c
 return v
def main():
 start=monotonic();names=['independent_integer_interval.py','independent_hermite_RH.py','independent_hermite_RH_result.json','independent_kernel_refined_result.json','independent_coefficient_binding_result.json'];raw={name:(ROOT/name).read_bytes()for name in names};stored=json.loads(raw['independent_hermite_RH_result.json']);need(stored['status']=='INDEPENDENT_H27_RH_BINDING_PASS','H/R coefficient binding not PASS');r=Box(*json.loads(raw['independent_kernel_refined_result.json'])['root_interval']);candidate=[r*r/2-1,-r,Box(Rat(-1,2)),2*r*r-1,1-Rat(3,2)*r*r,r/2];extra=list(map(Rat,['-1','-9/10','-2/5','-1/5','1/10','9/20','13/25','14/25']));nodes=sorted(candidate+[Box(x)for x in extra],key=lambda x:x.l);_,_,_,H,_=hermite(nodes);need(all(Box(*v).lo<=h.lo<=h.hi<=Box(*v).hi for h,v in zip(H,stored['H_coefficients_ascending'])),'rebuilt H escaped prior independent enclosure');W=[Box(1)]
 for x in nodes:W=mul(W,[x*x,-2*x,Box(1)])
 need(len(W)==29 and W[-1].l==S==W[-1].h,'W is not monic degree28');sq=mul(H,H);G=[Box(0)for _ in range(56)];G[0]=Box(1)
 for i,c in enumerate(sq):G[i]=G[i]-2*c;G[i+1]=G[i+1]+2*c
 rem=G[:];q=[Box(0)for _ in range(28)]
 for degree in range(55,27,-1):
  lead=rem[degree];offset=degree-28;q[offset]=lead
  for j in range(28):rem[offset+j]=rem[offset+j]-lead*W[j]
  rem[degree]=Box(0)
 remainder=rem[:28];consistent=all(v.l<=0<=v.h for v in remainder);need(consistent,'longdivision remainder enclosure excludes exact zero: inconsistent source or arithmetic')
 initial=power_to_bernstein(q,Rat(-1),Rat(14,25));stack=[('',initial)];leaves=[];negative=None;visited=0;depthmax=0;stop=None
 while stack:
  if monotonic()-start>125:stop='time budget with pending nodes';break
  if visited>=200000:stop='node cap with pending nodes';break
  address,b=stack.pop();visited+=1;depth=len(address);depthmax=max(depthmax,depth)
  if min(c.l for c in b)>=0:leaves.append({'address':address,'depth':depth,'minimum_lower_numerator':str(min(c.l for c in b)),'bernstein':[c.serial()for c in b]});continue
  numerator=int(address,2)if address else 0;mid=Rat(2*numerator+1,2**(depth+1));t=Rat(-1)+Rat(39,25)*mid;point=val(q,Box(t))
  if point.h<0:negative={'address':address,'t':str(t),'Q_interval':point.serial()};stop='proved negative Q point';break
  if depth>=30:stop='depth cap with pending nodes';stack.append((address,b));break
  left,right=split(b);stack.extend([(address+'1',right),(address+'0',left)])
 # An exact rational Kraft sum plus explicit addresses witnesses disjoint exhaustive dyadic coverage.
 kraft=sum((Rat(1,2**leaf['depth'])for leaf in leaves),Rat(0));complete=not stack and negative is None and stop is None;need(not complete or kraft==1,'leaf partition coverage is not exact1');status='ALGEBRAIC_HERMITE_MINORANT_Q_BERNSTEIN_PASS'if complete else('ALGEBRAIC_QUOTIENT_NEGATIVE'if negative else'ALGEBRAIC_QUOTIENT_INCOMPLETE')
 result={'status':status,'bits':BITS,'domain':['-1','14/25'],'nodes':[x.serial()for x in nodes],'H_coefficients_ascending':[x.serial()for x in H],'W_coefficients_ascending':[x.serial()for x in W],'G_coefficients_ascending':[x.serial()for x in G],'Q_coefficients_ascending':[x.serial()for x in q],'longdivision_remainder_enclosures':[x.serial()for x in remainder],'remainder_zero_containment_consistent':consistent,'exact_divisibility_basis':'For distinct true nodes xi<1, Hermite H satisfies H(xi)=fi,Hprime(xi)=fi^3 and (2-2xi)fi^2=1. Thus G(xi)=Gprime(xi)=0 exactly. Pairwise coprime factors (t-xi)^2 divide G in the real coefficient field; monic product W divides G, quotient degree<=27. Interval remainder zero containment is only a consistency diagnostic, never the exactness proof.','minorant_implication':'W>=0 and Q>=0 yield 1-(2-2t)H^2>=0 on domain. Since 2-2t>0, |H|sqrt(2-2t)<=1, hence H<=1/sqrt(2-2t); no H>=0 premise.','complete':complete,'visited_nodes':visited,'max_depth':depthmax,'leaf_count':len(leaves),'leaves':leaves,'pending':[{'address':a,'bernstein':[v.serial()for v in b]}for a,b in stack],'negative':negative,'stop_reason':stop,'exact_dyadic_leaf_measure':str(kraft),'source_sha256':{name:sha256(data).hexdigest()for name,data in raw.items()},'self_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'elapsed_seconds':monotonic()-start,'scope':'Only algebraic Hermite minorant; does not certify R_H positivity, contacts, PSD or Thomson optimality.'}
 out=ROOT/(PREFIX+'result.json');need(not out.exists(),'refuse overwrite');out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k]for k in ['status','complete','visited_nodes','max_depth','leaf_count','exact_dyadic_leaf_measure','negative','stop_reason','elapsed_seconds']},indent=2),flush=True)
if __name__=='__main__':main()
