"""Ten-second numerical design probe; sampled minima are NEVER lower bounds."""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
import time,json,numpy as np
BASE=Path(__file__).parent;start=time.monotonic();rng=np.random.default_rng(20260703)
model=json.loads((BASE/'nonsharp_d10_root25_7599205_v10.json').read_text());terms=[(tuple(e),np.longdouble(F(c).numerator)/np.longdouble(F(c).denominator))for e,c in model['residual_monomial']]
row=json.loads((BASE/'two_other_valleys2026_probe.json').read_text())['results'][1];u,v,t=map(np.longdouble,row['triangle_decimal']);g=1+2*u*v*t-u*u-v*v-t*t;A=np.array([[1,0,0],[u,np.sqrt(1-u*u),0],[v,(t-u*v)/np.sqrt(1-u*u),np.sqrt(g)/np.sqrt(1-u*u)]],dtype=np.longdouble)
def R(x,y,z):
 powers=[[a**i for i in range(28)]for a in [x,y,z]]
 return sum(c*powers[0][i]*powers[1][j]*powers[2][k]for(i,j,k),c in terms)
def phi(q):
 d=q@A.T
 return R(u,d[:,0],d[:,1])+R(v,d[:,0],d[:,2])+R(t,d[:,1],d[:,2])
Q=np.array([w['q']for w in row['wells']],dtype=np.longdouble);Q/=np.sqrt(np.sum(Q*Q,axis=1))[:,None];radius=.02;cap_samples=[];boundary=[]
for q in Q:
 axis=np.array([1.,0,0])if abs(q[0])<.8 else np.array([0.,1.,0]);e=axis-np.dot(axis,q)*q;e/=np.sqrt(np.dot(e,e));f=np.cross(q,e);angles=rng.uniform(0,2*np.pi,64);rads=radius*np.sqrt(rng.uniform(0,1,64));cap_samples.append(np.cos(rads)[:,None]*q+np.sin(rads)[:,None]*(np.cos(angles)[:,None]*e+np.sin(angles)[:,None]*f));aa=np.arange(64)*2*np.pi/64;boundary.extend(np.cos(radius)*q+np.sin(radius)*(np.cos(a)*e+np.sin(a)*f)for a in aa)
random=rng.normal(size=(20000,3));random/=np.linalg.norm(random,axis=1)[:,None];random=np.vstack([random,np.array(boundary)]);allowed=np.max(random@A.T,axis=1)<=.56;outside=np.max(random@Q.T,axis=1)<=np.cos(radius)+1e-14;pts=random[allowed&outside];values=phi(pts);pairs=[]
for i,j in combinations(range(len(Q)),2):
 p,q=cap_samples[i],cap_samples[j];dp=p@A.T;dq=q@A.T;s=np.sum(p*q,axis=1);ok=(s<=.56)&(np.max(dp,axis=1)<=.56)&(np.max(dq,axis=1)<=.56)
 if not np.any(ok):pairs.append({'cells':[i,j],'allowed_sample_pairs':0});continue
 vv=sum(R(dp[ok,a],dq[ok,a],s[ok])for a in range(3));pairs.append({'cells':[i,j],'allowed_sample_pairs':int(ok.sum()),'psi_sample_min':float(vv.min()),'psi_sample_max':float(vv.max()),'sample_min_exceeds_entire_K':bool(vv.min()>row['budget_display'])})
result={'status':'discovery_only_no_lower_bounds','triangle':'T3','radius_radians':radius,'sphere_random_count':20000,'outside_allowed_samples':len(pts),'outside_phi_sample_min':float(values.min()),'outside_phi_witness':list(map(float,pts[np.argmin(values)])),'budget_K':row['budget_display'],'cap_phi_sample_min':[float(phi(p).min())for p in cap_samples],'pair_samples':pairs,'seconds':time.monotonic()-start}
out=BASE/'two_other_valleys2026_cell_design_probe.json';out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True);print('SAVED',out)
