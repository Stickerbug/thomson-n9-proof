"""Range/noise assessment ONLY. No global check or root traversal is called."""
import json,time,hashlib
from pathlib import Path
from fractions import Fraction as Q
from math import comb
from analytic10_sharp2026_engine import AxisCache,ROOT_BOX,coefficients
from certify_three_point_d4 import mul,add,scale,mono,const
BASE=Path(__file__).parent;start=time.monotonic();src=BASE/'d10_relative_normal2026_results.json';data=json.loads(src.read_text());model=data['solution'];AA=[[[Q(str(x))for x in row]for row in block]for block in model['A']]
a=add(mono(2,1),scale(mul(mono(0,1),mono(1,1)),-1));b=mul(add(const(1),scale(mono(0,2),-1)),add(const(1),scale(mono(1,2),-1)));qq=[const(1),a]
for k in range(1,10):qq.append(add(scale(mul(a,qq[-1]),2),scale(mul(b,qq[-2]),-1)))
from itertools import permutations
fp={}
for k,A in enumerate(AA):
 for i,row in enumerate(A):
  for j,v in enumerate(row):
   for e,cc in qq[k].items():
    es=(e[0]+i,e[1]+j,e[2])
    for pm in permutations(range(3)):
     ee=[0]*3
     for axis in range(3):ee[pm[axis]]=es[axis]
     ee=tuple(ee);fp[ee]=fp.get(ee,Q(0))+v*cc/6
D={}
for (i,j,k),v in fp.items():D[j+k]=D.get(j+k,Q(0))+v
K={p:-7*v for p,v in fp.items()};K[(0,0,0)]=K.get((0,0,0),0)-Q(str(model['c']))
rows=[];sqcount=0
for bits in [80,96,104]:
 cache=AxisCache(D,bits);S=1<<bits;KB=coefficients(K,ROOT_BOX,degrees=(10,10,10),bits=bits);km=max(abs(int(x))for x in KB.flat);hroot=cache.H(0,0);rec={'bits':bits,'K_root_absmax':str(km),'K_root_absmax_bitlength':km.bit_length(),'K_root_safe_strict_2pow124':km<1<<124,'H_root_absmax_bitlength':max(abs(x)for x in hroot[1]).bit_length(),'H_root_native_eligible':hroot[0]is not None,'intervals':[]}
 for level in [12,20,24,28]:
  center=Q(-1,2);idx=((center+1)*Q(25,39)*(1<<level)).numerator//((center+1)*Q(25,39)*(1<<level)).denominator
  _,h,q=cache.H(level,idx);l=Q(-1)+Q(39,25)*Q(idx,1<<level);w=Q(39,25*(1<<level));lam=w/(1-l);vv=2-2*l
  from math import isqrt
  n=isqrt(vv.denominator*(1<<(2*bits))//vv.numerator);af=[n*comb(2*k,k)*lam.numerator**k//(4**k*lam.denominator**k)for k in range(11)]
  exactad=[S*w**k*sum((v*comb(j,k)*l**(j-k)for j,v in D.items()if j>=k),Q(0))for k in range(21)];tail=sum(max(v,0)for v in exactad[11:]);ideal=[Q(af[k])-exactad[k]for k in range(11)];ideal[0]-=tail;idealh=[]
  for i in range(11):
   v=sum((ideal[k]*Q(comb(i,k),comb(10,k))for k in range(i+1)),Q(0));idealh.append(v.numerator//v.denominator)
  err=Q(max(abs(a-b)for a,b in zip(idealh,h)),S);rec['intervals'].append({'level':level,'index':idx,'width':str(w),'h_integer_upper_D_vs_exact_D_max_difference':str(err),'difference_float':float(err)})
  db=cache.D(level,idx)
  for z in [Q(0),Q(1,3),Q(2,3),Q(1)]:
   dup=sum(Q(v,S)*comb(20,i)*z**i*(1-z)**(20-i)for i,v in enumerate(db));qv=sum(Q(v,S)*z**i for i,v in enumerate(q));v=dup+qv;t=l+w*z;assert v<=0 or v*v*(2-2*t)<=1;sqcount+=1
 rows.append(rec)
assert AxisCache({0:Q(1<<40)},104).H(0,0)[0]is None
report={'status':'PREPARED_NO_ROOT_RUN','source_scope':'Ranges use rational decimal reconstruction of NUMERICAL solution A/c only. They are not certified bounds for forthcoming true exact coefficients. No root traversal or check_analytic was called.','source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'engine_sha256':hashlib.sha256((BASE/'analytic10_sharp2026_engine.py').read_bytes()).hexdigest(),'F_degree':[max(p[i]for p in fp)for i in range(3)],'d_degree':max(D),'precision_assessment':rows,'exact_fraction_square_samples':sqcount,'h_overflow_returns_None_without_cast':True,'seconds':time.monotonic()-start}
p=BASE/'analytic10_sharp2026_prepare.json';assert not p.exists();p.open('x').write(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2),flush=True)
