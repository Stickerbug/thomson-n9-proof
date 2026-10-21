"""Exact, root-only two-cap certificate for one fixed rational anchor triangle.
No new global Thomson bound is claimed. Independent replay needs only numpy,
certify_all_degree.I and exact_tensor_bernstein.coefficients.
"""
if not __debug__: raise RuntimeError('Assertions must be enabled')
from pathlib import Path
from fractions import Fraction as F
from math import lcm
import argparse, numpy as np, json, time, hashlib
from exact_tensor_bernstein import coefficients
from certify_all_degree import I, S
BASE=Path(__file__).parent
Q=1<<128
ANCHORS=[[Q,0,0],[-258349438023425705468166417870692938362,221467056489890423021022487582886620347,0],[-99401926522924573437696996217667627444,56224497025898536080227031712707522912,320546645864579319756704150369479978900]]
U,V,T=map(F,['-0.759220762336624','-0.29211600772137486','0.32931701954562287'])
CENTERS=[[F(z)*F(9999999,10000000) for z in row] for row in [['.3213589784','.5134140431','-.7956974471'],['.3181271408','-.7597356584','-.5670950993']]]
EPS=F(1,10**25);M=F(3,100000);TAU=F(1,10000);HEIGHT=F(89,100)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def add(a,b):
 out=np.zeros((max(a.shape[0],b.shape[0]),max(a.shape[1],b.shape[1])),dtype=object)
 out[:a.shape[0],:a.shape[1]]+=a;out[:b.shape[0],:b.shape[1]]+=b;return out
def mul(a,b):
 if not np.any(a):return np.zeros((1,1),dtype=object)
 out=np.zeros((a.shape[0]+2,a.shape[1]+2),dtype=object)
 for (i,j),z in b.items():
  if z:out[i:i+a.shape[0],j:j+a.shape[1]]+=a*z
 return out
def split(a,axis):
 w=np.moveaxis(a,axis,0).copy();left=np.empty_like(w);right=np.empty_like(w);n=w.shape[0]-1
 left[0]=w[0];right[n]=w[-1]
 for k in range(1,n+1):
  w=(w[:-1]+w[1:])//2;left[k]=w[0];right[n-k]=w[-1]
 return np.moveaxis(left,0,axis),np.moveaxis(right,0,axis)
def run(bits=64,budget=60000,seconds=260,allowed_slack=F(1,10**8)):
 source=BASE/'nonsharp_d10_root25_7599205_v10.json';raw=json.loads(source.read_text())
 terms=[(tuple(e),F(z))for e,z in raw['residual_monomial']]
 assert all(sum(e)<=27 for e,z in terms)
 # Verify coordinate rounding against true algebraic unit anchors.
 g=1+2*U*V*T-U*U-V*V-T*T;assert g>0
 b=(1-I(U)**2).sqrt()
 actual=[[I(1),I(0),I(0)],[I(U),b,I(0)],[I(V),(T-I(U)*V)/b,I(g).sqrt()/b]]
 for ar,ir in zip(ANCHORS,actual):
  for k,x in zip(ar,ir):assert F(k,Q)<=F(x.lo,S)<=F(x.hi,S)<F(k+1,Q)
 derivative_sum=sum(abs(z)*(e[1]+e[2])for e,z in terms)
 assert (1+F(3,Q))**26<2
 perturbation=F(18,Q)*derivative_sum;assert perturbation<EPS
 # Mean-value bound: 3 residuals, each argument error <=3/Q,
 # derivatives <=2 sum |coefficient|*(j+k) on |args|<=1+3/Q.
 norms=[sum(z*z for z in p)for p in CENTERS]
 assert all(n<=1 for n in norms)
 assert 2*HEIGHT**2-1>F(14,25)
 cs=[];den=1
 for e in [U,V,T]:
  c={}
  for (i,j,k),z in terms:c[j,k]=c.get((j,k),F(0))+z*e**i
  cs.append(c)
  for z in c.values():den=lcm(den,z.denominator)
 cs=[{a:z.numerator*(den//z.denominator)for a,z in c.items()}for c in cs]
 d={(0,0):Q,(2,0):Q,(0,2):Q};dp=[np.ones((1,1),dtype=object)]
 for k in range(27):dp.append(mul(dp[-1],d))
 box=[(F(-1),F(1))]*2
 dpoly={(i,j):F(int(z),Q**27)for (i,j),z in np.ndenumerate(dp[27])if z}
 du=coefficients(dpoly,box,degrees=(54,54),bits=bits,upper=True)
 start=time.monotonic();results=[]
 for sign in [1,-1]:
  ns=[{(0,0):sign*c,(1,0):2*a,(0,1):2*b,(2,0):-sign*c,(0,2):-sign*c}for a,b,c in ANCHORS]
  p=np.zeros((1,1),dtype=object)
  for (ii,jj),c in zip([(0,1),(0,2),(1,2)],cs):
   outer=np.zeros((1,1),dtype=object)
   for j in range(27,-1,-1):
    n=27-j;h=np.zeros((1,1),dtype=object)
    for k in range(n,-1,-1):
     if k<n:h=mul(h,ns[jj])
     cc=c.get((j,k),0)
     if cc:h=add(h,dp[n-k]*cc)
    outer=add(mul(outer,ns[ii]),h)
   p=add(p,outer)
  assert p.shape==(55,55)
  poly={(i,j):F(int(z),den*Q**27)for (i,j),z in np.ndenumerate(p)if z}
  bp=coefficients(poly,box,degrees=(54,54),bits=bits)
  roots=[]
  for threshold in [M+EPS,TAU+EPS]:
   roots.append(bp-np.array([-((-int(z)*threshold.numerator)//threshold.denominator)for z in du.flat],dtype=object).reshape(du.shape))
  cuts=[]
  for ni in ns:
   cc={a:F(z,Q)for a,z in ni.items()};cut=F(14,25)+allowed_slack+F(3,Q)
   for a in d:cc[a]=cc.get(a,F(0))-cut
   cuts.append(coefficients(cc,box,degrees=(2,2),bits=bits))
  for a,b,c in CENTERS:
   cc={(0,0):sign*c-HEIGHT,(1,0):2*a,(0,1):2*b,(2,0):-sign*c-HEIGHT,(0,2):-sign*c-HEIGHT}
   cuts.append(coefficients(cc,box,degrees=(2,2),bits=bits))
  stack=[(roots+cuts,0,(0,0,0,0))];nodes=positive=excluded=capresolved=maxdepth=0
  treehash=hashlib.sha256();clock=time.monotonic();leaves=[]
  while stack and nodes<budget and time.monotonic()-clock<seconds:
   arr,depth,location=stack.pop();nodes+=1;maxdepth=max(maxdepth,depth)
   mins=[int(min(z.flat))for z in arr]
   if max(mins[2:5])>0:
    excluded+=1;treehash.update(b'X');leaves.append({'box_dyadic':location,'type':'anchor_excluded','lower_coefficients':mins});continue
   cap=max(mins[5:])>0
   if mins[0]>=0 and (cap or mins[1]>=0):
    positive+=1;capresolved+=int(cap);treehash.update(b'P');leaves.append({'box_dyadic':location,'type':'positive_inside_cap'if cap else'positive_tau','lower_coefficients':mins});continue
   assert depth<80,'Unresolved depth80: no certificate'
   axis=depth%2;treehash.update(bytes([axis]));parts=[split(z,axis)for z in arr]
   x,dx,y,dy=location
   locations=[(2*x,dx+1,y,dy),(2*x+1,dx+1,y,dy)]if axis==0 else[(x,dx,2*y,dy+1),(x,dx,2*y+1,dy+1)]
   stack.append(([z[1]for z in parts],depth+1,locations[1]));stack.append(([z[0]for z in parts],depth+1,locations[0]))
  row={'chart':sign,'nodes':nodes,'positive_leaves':positive,'excluded_leaves':excluded,'cap_resolved_leaves':capresolved,'pending':len(stack),'max_depth':maxdepth,'seconds':time.monotonic()-clock,'tree_sha256':treehash.hexdigest(),'root_phi_sha256':hashlib.sha256(str(bp.tolist()).encode()).hexdigest(),'terminal_leaves':leaves}
  results.append(row);print('CHART',json.dumps({k:v for k,v in row.items()if k!='terminal_leaves'}),flush=True)
  if stack:break
 complete=len(results)==2 and all(z['pending']==0 for z in results)
 report={'status':'certified_fixed_triangle_two_cap_bounds'if complete else'incomplete','scope':'Fixed triangle with widened anchor-dot admissible domain; no new global Thomson energy bound.','allowed_anchor_dot_upper':str(F(14,25)+allowed_slack),'source':str(source),'source_sha256':sha(source),'verifier_sha256':sha(Path(__file__)),'bernstein_dependency_sha256':sha(BASE/'exact_tensor_bernstein.py'),'interval_dependency_sha256':sha(BASE/'certify_all_degree.py'),'anchor_parameter':[str(z)for z in [U,V,T]],'dyadic_anchor_numerators':ANCHORS,'dyadic_denominator':str(Q),'coordinate_error_upper':str(F(1,Q)),'phi_perturbation_upper':str(perturbation),'phi_perturbation_allowance':str(EPS),'derivative_coefficient_sum':str(derivative_sum),'cap_centers':[[str(z)for z in row]for row in CENTERS],'cap_norm_squared':[str(z)for z in norms],'cap_height':str(HEIGHT),'pair_inner_product_upper':str(F(14,25)),'global_phi_lower':str(M),'outside_caps_phi_lower':str(TAU),'six_point_cost_lower':str(4*TAU+2*M),'chart_formula':'q=(2a,2b,sign*(1-a*a-b*b))/(1+a*a+b*b); full square [-1,1]^2 for each sign covers S2.','phi_formula':'R(u,a.q,b.q)+R(v,a.q,c.q)+R(t,b.q,c.q), with true algebraic unit anchor vectors','root_only':True,'scale_bits':bits,'box_dyadic_encoding':'[i,dx,j,dy] means x in [-1+2*i/2^dx,-1+2*(i+1)/2^dx], likewise y','results':results,'seconds':time.monotonic()-start}
 return report
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,default=BASE/'fixed_triangle_two_caps_widened_certificate_v1.json');parser.add_argument('--bits',type=int,default=64)
 args=parser.parse_args();report=run(bits=args.bits);args.out.write_text(json.dumps(report,indent=2)+'\n');print('SAVED',args.out,report['status'],flush=True)
 if report['status']!='certified_fixed_triangle_two_cap_bounds':raise SystemExit(2)
