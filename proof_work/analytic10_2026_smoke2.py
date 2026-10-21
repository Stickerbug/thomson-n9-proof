import random,json,time
from fractions import Fraction as F
from math import comb
from pathlib import Path
import numpy as np
from analytic10_2026_engine import AxisCache,minimum,words,check_analytic,SCALE,NativeTensor
start=time.monotonic();rng=random.Random(2026106021);base=Path(__file__).parent
co=json.loads((base/'narrowroot2026_coefficients.json').read_text());fm={tuple(p):F(int(v['lo_numerator'])+int(v['hi_numerator']),1<<(v['denominator_power_of_two']+1))for p,v in co['F_coefficients']};deg=[max(p[i]for p in fm)for i in range(3)];assert max(deg)<=10;dm={}
for (i,j,k),v in fm.items():dm[j+k]=dm.get(j+k,F(0))+v
cache=AxisCache(dm);nc=0
for it in range(50):
 level=rng.randrange(21);index=rng.randrange(1<<level);_,h,q=cache.H(level,index);db=cache.D(level,index);l=F(-1)+F(39,25)*F(index,1<<level);w=F(39,25*(1<<level))
 for z in [F(0),F(1,7),F(1,2),F(6,7),F(1)]:
  t=l+w*z;dexact=sum(v*t**k for k,v in dm.items());dup=sum(F(v,SCALE)*comb(20,i)*z**i*(1-z)**(20-i)for i,v in enumerate(db));qp=sum(F(v,SCALE)*z**i for i,v in enumerate(q));hb=sum(F(v,SCALE)*comb(10,i)*z**i*(1-z)**(10-i)for i,v in enumerate(h));assert dexact<=dup and hb<=qp
  v=qp+dup
  assert v<=0 or v*v*(2-2*t)<=1
  nc+=1
for it in range(100):
 bound=(1<<123)if it<10 else(1<<90);a=np.array([rng.randrange(-bound,bound)for _ in range(1331)],dtype=object).reshape(11,11,11);h=[[rng.randrange(-bound,bound)for _ in range(11)]for _ in range(3)];ref=min(int(a[i,j,k])+h[0][i]+h[1][j]+h[2][k]for i in range(11)for j in range(11)for k in range(11));assert minimum(NativeTensor(a),list(map(words,h)))==ref
r=check_analytic({(0,0,0):(F(0),F(0))},(F(0),F(0)),[],[],10,10);assert r['status']=='CONDITIONAL_NONSHARP_CLOSED'and r['visited_nodes']==1
r0=check_analytic({(0,0,0):(F(0),F(0))},(F(0),F(0)),[],[],0,1);assert r0['status']=='INCOMPLETE'and r0['pending_count']==1
out={'status':'PASS','exact_univariate_fraction_square_points':nc,'native_python_exact_comparisons':100,'F_degree':deg,'d_degree':max(dm),'positive_root_closed':True,'zero_budget_fullroot_pending':True,'seconds':time.monotonic()-start};p=base/'analytic10_2026_smoke2.json';assert not p.exists();p.open('x').write(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
