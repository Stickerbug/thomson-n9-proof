"""Strict pointwise second jets for archived true-root contact+PSD kernel."""
import json,time,itertools,argparse
from pathlib import Path
from fractions import Fraction as F
from dyadic_interval import I,S,BITS
from d10_exact_contact_psd_seed1_v1 import run as kernel
class J:
 def __init__(self,v,g=None,h=None):
  self.v=I.cast(v);self.g=[I(0)for _ in range(3)]if g is None else g;self.h=[[I(0)for _ in range(3)]for _ in range(3)]if h is None else h
 @staticmethod
 def cast(x):return x if isinstance(x,J)else J(x)
 def __add__(a,b):
  b=J.cast(b);return J(a.v+b.v,[a.g[i]+b.g[i]for i in range(3)],[[a.h[i][j]+b.h[i][j]for j in range(3)]for i in range(3)])
 __radd__=__add__
 def __neg__(a):return J(-a.v,[-v for v in a.g],[[-v for v in row]for row in a.h])
 def __sub__(a,b):return a+-J.cast(b)
 def __rsub__(a,b):return J.cast(b)+-a
 def __mul__(a,b):
  b=J.cast(b);return J(a.v*b.v,[a.g[i]*b.v+a.v*b.g[i]for i in range(3)],[[a.h[i][j]*b.v+a.g[i]*b.g[j]+a.g[j]*b.g[i]+a.v*b.h[i][j]for j in range(3)]for i in range(3)])
 __rmul__=__mul__
 def __truediv__(a,b):return a*(1/I.cast(b))
 def __pow__(a,n):
  ans=J(1)
  for _ in range(n):ans=ans*a
  return ans

def raw(d):return I(int(d['lo_numerator']),int(d['hi_numerator']),raw=True)
def bounds(A):return [[x.bounds()for x in row]for row in A]
def ldl(A):
 n=len(A);L=[[I(int(i==j))for j in range(n)]for i in range(n)];D=[]
 for i in range(n):
  d=A[i][i]-sum((L[i][j]**2*D[j]for j in range(i)),I(0));assert d.lo>0,('LDL_nonpositive',i,d.pretty());D.append(d)
  for j in range(i+1,n):L[j][i]=(A[j][i]-sum((L[j][k]*L[i][k]*D[k]for k in range(i)),I(0)))/d
 return [d.bounds()for d in D]
def run(cert,output):
 start=time.time();ctx=kernel(None,cert,True);Ns=ctx['N'];xx=ctx['x'];nodes=ctx['nodes'];r=ctx['r'];names='ABCDFG';lookup={tuple(t):j for j,t in enumerate(ctx['indices'])}
 AA=[]
 for k,N in enumerate(Ns):
  if not N:AA.append(None);continue
  n=len(N);B=[[xx[lookup[k,min(i,j),max(i,j)]]for j in range(n)]for i in range(n)]
  # Reconstruct original matrices once; all ensuing AD is independent of contact design.
  m=len(N[0]);A=[[sum((N[a][i]*sum((B[a][b]*N[b][j]for b in range(n)),I(0))for a in range(n)),I(0))for j in range(m)]for i in range(m)];AA.append(A)
 def fj(point):
  vs=[J(x,[I(int(i==j))for j in range(3)])for i,x in enumerate(point)];out=J(0)
  for perm in itertools.permutations(range(3)):
   u,v,t=[vs[i]for i in perm];a=t-u*v;b=(1-u*u)*(1-v*v);Q=[J(1),a]
   for k in range(1,10):Q.append(2*a*Q[-1]-b*Q[-2])
   for k,A in enumerate(AA):
    if A is None:continue
    up=[J(1)];vp=[J(1)]
    for _ in range(len(A)-1):up.append(up[-1]*u);vp.append(vp[-1]*v)
    z=sum((up[i]*sum((vp[j]*A[i][j]for j in range(len(A))),J(0))for i in range(len(A))),J(0));out+=Q[k]*z/6
  return out
 diag=[]
 for x in nodes:
  j=fj([I(1),x,x]);diag.append((j.g[1]+j.g[2],j.h[1][1]+2*j.h[1][2]+j.h[2][2]))
 curvature=json.loads(Path('proof_work/contact_minorant_curvature_v1.json').read_text());assert curvature['status']=='certified_upper_bounds'
 loss=[None]*6
 for a,row in zip([2,5,3,1,0,4],curvature['candidate_nodes']):
  z=raw(row['node']);assert not(z.hi<nodes[a].lo or nodes[a].hi<z.lo);u=raw(row['curvature_upper']);assert u.lo>0;loss[a]=I(0,u.hi,raw=True)
 geom=json.loads(Path('proof_work/candidate_triple_types_v1.json').read_text())['triangle_types'];rows=[]
 for item in geom:
  labs=item['labels'];ids=[names.index(a)for a in labs];pt=[nodes[a]for a in ids];Fj=fj(pt);G=[];H=[]
  for i,a in enumerate(ids):
   fp=1/((2-2*nodes[a])**3).sqrt();G.append(fp-7*Fj.g[i]-diag[a][0]);hrow=[]
   for j,b in enumerate(ids):hrow.append(-7*Fj.h[i][j]+(3/((2-2*nodes[a])**5).sqrt()-diag[a][1]if i==j else 0))
   H.append(hrow)
  HH=[[H[i][j]-(loss[ids[i]]if i==j else 0)for j in range(3)]for i in range(3)]
  row={'labels':labs,'kind':item['status'],'Rf_Hessian':bounds(H),'RH27_Hessian_enclosure':bounds(HH)}
  if item['status']!='identically_boundary':row['Rf_LDL']=ldl(H);row['RH27_LDL']=ldl(HH)
  else:
   u,v,t=pt;normal=[2*(v*t-u),2*(u*t-v),2*(u*v-t)];lam=sum((a*b for a,b in zip(G,normal)),I(0))/sum((a*a for a in normal),I(0));assert lam.lo>0,('lambda',labs,lam.pretty())
   Hg=[[-2,2*t,2*v],[2*t,-2,2*u],[2*v,2*u,-2]]
   if labs==['B','G','G']:T=[[I(0),-4*r],[I(1),I(1)],[I(-1),I(1)]]
   elif labs==['C','F','F']:T=[[I(0),2*r],[I(1),I(1)],[I(-1),I(1)]]
   else:assert labs==['D','D','D'];T=[[I(1),I(1)],[I(-1),I(1)],[I(0),I(-2)]]
   def project(A):return [[sum((T[i][a]*(A[i][j]-lam*Hg[i][j])*T[j][b]for i in range(3)for j in range(3)),I(0))for b in range(2)]for a in range(2)]
   P=project(H);PH=project(HH);row.update({'lambda':lam.bounds(),'lambda_display':lam.pretty(),'tangent_basis':bounds(T),'Rf_tangent_Lagrangian':bounds(P),'RH27_tangent_Lagrangian':bounds(PH),'Rf_tangent_LDL':ldl(P),'RH27_tangent_LDL':ldl(PH)})
  rows.append(row);print('PASS',labs,'seconds',time.time()-start,flush=True)
 witness=[I('-.759220762336624'),I('-.29211600772137486'),I('.32931701954562287')]
 gram=1+2*witness[0]*witness[1]*witness[2]-sum((x*x for x in witness),I(0));assert gram.lo>0
 E=sum((w/(2-2*x).sqrt()for w,x in zip([6,3,6,3,12,6],nodes)),I(0));c=E/12+fj([I(1)]*3).v/8
 wr=sum((1/(2-2*x).sqrt()for x in witness),I(0))-c-7*fj(witness).v-sum((fj([I(1),x,x]).v for x in witness),I(0));assert wr.hi<0
 assert I('-0.000007738').hi<wr.lo and wr.hi<I('-0.000007737').lo
 witness_data={'point':[x.bounds()for x in witness],'Gram':gram.bounds(),'Rf':wr.bounds(),'display':wr.pretty(),'consequence':'exact corrected kernel fails global Rf>=0; H27<=f implies RH27<=Rf<0 too. Not a Thomson configuration counterexample.'}
 out={'negative_residual_witness':witness_data,'status':'CERTIFIED_CANDIDATE_SECOND_JETS_f_AND_H27','certificate':cert,'bits':BITS,'curvature_source':'contact_minorant_curvature_v1.json','scope':'pointwise jets only: 9 interior Hessians positive definite,3 boundary lambda strictlypositive and tangent Lagrangian Hessians positive definite; no neighborhood or global R proof','rows':rows,'seconds':time.time()-start}
 p=Path(output);assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');print(out['status'],out['seconds'],flush=True)
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--certificate',default='proof_work/d10_exact_contact_psd_seed1_v1.json');p.add_argument('--output',default='proof_work/d10_exact_contact_jets_v1.json');a=p.parse_args();run(a.certificate,a.output)
