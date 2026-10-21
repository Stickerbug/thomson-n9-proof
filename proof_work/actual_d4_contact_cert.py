"""Exact Q(r) and dyadic-interval obstruction for sharp d4 three-point kernels."""
import itertools,json,time,argparse
from pathlib import Path
from fractions import Fraction
import sympy as s
import numpy as np
from candidate_low_rank import features
from dyadic_interval import I,BITS
from certify_pair_moments import L,U,derivative
r=s.Symbol('r');K=s.QQ.frac_field(r);z=K.zero;o=K.one

def conv(x):return K.from_sympy(s.cancel(x))
def add(*ps):
 d={}
 for p in ps:
  for a,c in p.items():d[a]=d.get(a,z)+c
 return {a:c for a,c in d.items()if c}
def scale(p,c):return {a:v*c for a,v in p.items()if v*c}
def mul(p,q):
 d={}
 for a,c in p.items():
  for b,e in q.items():
   k=tuple(x+y for x,y in zip(a,b));d[k]=d.get(k,z)+c*e
 return {a:c for a,c in d.items()if c}
def mono(a):return {a:o}
def perm(p,pi):
 d={}
 for a,c in p.items():
  b=[0]*3
  for j in range(3):b[pi[j]]=a[j]
  d[tuple(b)]=d.get(tuple(b),z)+c
 return d

def null(p,c):
 n=len(p);N=[]
 if n==1:
  assert p[0] or c[0]
  return [],p[0] if p[0] else c[0]
 if any(c):
  i,j=next((i,j)for i in range(n)for j in range(i+1,n)if p[i]*c[j]-p[j]*c[i]);det=p[i]*c[j]-p[j]*c[i]
  for k in range(n):
   if k in (i,j):continue
   v=[z]*n;v[k]=det;v[i]=p[j]*c[k]-p[k]*c[j];v[j]=p[k]*c[i]-p[i]*c[k];N.append(v)
 else:
  i=next(i for i in range(n)if p[i]);det=p[i]
  for k in range(n):
   if k==i:continue
   v=[z]*n;v[k]=det;v[i]=-p[k];N.append(v)
 for v in N:assert sum((a*b for a,b in zip(v,p)),z)==0 and sum((a*b for a,b in zip(v,c)),z)==0
 return N,det

def build():
 u,v,t=[mono(tuple(int(i==j)for i in range(3)))for j in range(3)]
 a=add(t,scale(mul(u,v),-o));b=mul(add({(0,0,0):o},scale(mul(u,u),-o)),add({(0,0,0):o},scale(mul(v,v),-o)))
 Q=[{(0,0,0):o},a]
 for k in range(1,4):Q.append(add(scale(mul(a,Q[-1]),K(2)),scale(mul(b,Q[-2]),-o)))
 bases=[];pivs=[];Ns=[]
 for k in range(5):
  pp,cc=features(r,k,5-k);N,pv=null([conv(x)for x in pp],[conv(x)for x in cc]);pivs.append(pv);Ns.append(N)
  for i in range(len(N)):
   for j in range(i,len(N)):
    raw={}
    for a0 in range(5-k):
     for b0 in range(5-k):
      c=N[i][a0]*N[j][b0]+(N[j][a0]*N[i][b0]if i!=j else z)
      raw=add(raw,scale(mul(mono((a0,b0,0)),Q[k]),c))
    bases.append(scale(add(*(perm(raw,pi)for pi in itertools.permutations(range(3)))),o/6))
 print('built',len(bases),'basis polynomials',flush=True);return bases,pivs,Ns

def ev(p,pt):return sum((c*pt[0]**a[0]*pt[1]**a[1]*pt[2]**a[2]for a,c in p.items()),z)
def diff(p,j):
 d={}
 for a,c in p.items():
  if a[j]:b=list(a);b[j]-=1;d[tuple(b)]=c*a[j]
 return d

def interval(x,rr):
 def poly(p):
  ans=I(0)
  for c in p.to_dense():ans=ans*rr+I(Fraction(int(c.numerator),int(c.denominator)))
  return ans
 return poly(x.numer)/poly(x.denom)
def f(x):return 1/(2-2*x).sqrt()
def fp(x):return 1/((2-2*x)**3).sqrt()
def report(x):return {'exact':x.bounds(),'display':x.pretty()}
def number(x):return s.cancel(K.to_sympy(x).subs(r,s.Rational(71,100)))

def run(output):
 start=time.time();bases,pivs,Ns=build();rr=I(L,U)
 assert [len(n)for n in Ns]==[3,3,1,1,0]
 for p in pivs:assert interval(p,rr).lo*interval(p,rr).hi>0
 mons=sorted(set().union(*(set(b)for b in bases)));C=[[b.get(a,z)for b in bases]for a in mons]
 C0=s.Matrix([[number(x)for x in row]for row in C]);_,cols=C0.rref();_,rows=C0.T.rref();assert len(cols)==13
 cols=list(cols);omit=next(i for i in range(14)if i not in cols);A=[[C[i][j]for j in cols]+[C[i][omit]]for i in rows]
 for k in range(13):
  q=next(i for i in range(k,13)if A[i][k]);A[k],A[q]=A[q],A[k];pv=A[k][k];A[k]=[x/pv for x in A[k]]
  for i in range(k+1,13):
   d=A[i][k]
   if d:A[i]=[x-d*y for x,y in zip(A[i],A[k])]
 sol=[z]*13
 for i in reversed(range(13)):sol[i]=A[i][-1]-sum((A[i][j]*sol[j]for j in range(i+1,13)),z)
 assert all(row[omit]==sum((row[j]*x for j,x in zip(cols,sol)),z)for row in C)
 gauge_bounds=[report(interval(x,rr))for x in sol]
 print('exact F gauge and finite coefficients verified',flush=True)
 from sharp_three_point import candidate_data
 cand,*_=candidate_data(4)
 nodes=[conv(1-s.Rational(3,2)*r*r),conv(2*r*r-1),conv(r*r/2-1),conv(-s.Rational(1,2)),conv(r/2),conv(-r)]
 nf=[float(K.to_sympy(x).subs(r,.7105483340929538))for x in nodes]
 labels=[tuple(min(range(6),key=lambda j:abs(nf[j]-t))for t in row)for row in cand];assert len(set(labels))==12
 def dot(i,j):
  if i==j:return o
  if i<6 and j<6:
   si,ki=divmod(i,3);sj,kj=divmod(j,3)
   return nodes[0]if si==sj else nodes[1]if ki==kj else nodes[2]
  if i>=6 and j>=6:return nodes[3]
  if i>=6:i,j=j,i
  return nodes[5]if (i%3-(j-6))%3==2 else nodes[4]
 types={tuple(sorted((nodes.index(dot(i,j)),nodes.index(dot(i,k)),nodes.index(dot(j,k)))))for i,j,k in itertools.combinations(range(9),3)}
 assert types=={tuple(sorted(a))for a in labels}
 # Reconstruct all ordered kernel sums independently from the 9-point dot table.
 for k in range(5):
  pp,cc=features(r,k,5-k);pp=[conv(x)for x in pp];cc=[conv(x)for x in cc]
  G=[[z for _ in range(5-k)]for _ in range(5-k)]
  for anchor,weight in [(0,6),(6,3)]:
   for y in range(9):
    for zz in range(9):
     u0,v0,t0=dot(anchor,y),dot(anchor,zz),dot(y,zz)
     a0=t0-u0*v0;b0=(o-u0*u0)*(o-v0*v0);q=[o,a0]
     for kk in range(1,4):q.append(2*a0*q[-1]-b0*q[-2])
     for i in range(5-k):
      for j in range(5-k):G[i][j]+=weight*u0**i*v0**j*q[k]
  assert all(G[i][j]==6*(o-conv(r)**2)**(k%2)*pp[i]*pp[j]+3*cc[i]*cc[j]for i in range(5-k)for j in range(5-k))
 print('all five candidate G kernel identities verified',flush=True)
 pts=[[nodes[a]for a in lab]for lab in labels];inside=[];dets=[]
 for j,p in enumerate(pts):
  d=o+2*p[0]*p[1]*p[2]-sum((x*x for x in p),z);iv=interval(d,rr);dets.append(report(iv))
  if d:assert iv.lo>0;inside.append(j)
 assert len(inside)==9
 ds=[]
 for b in bases:
  dg={}
  for a,c in b.items():dg[(0,a[1]+a[2],0)]=dg.get((0,a[1]+a[2],0),z)+c
  ds.append(add(scale(b,K(7)),*(perm(dg,pi)for pi in [(0,1,2),(1,0,2),(0,2,1)]),{(0,0,0):sum(b.values(),z)/8}))
 ni=[interval(x,rr)for x in nodes]
 for x in ni:assert x.lo>I(-1).hi and x.hi<I('0.57').lo
 for i in range(6):
  for j in range(i):assert ni[i].hi<ni[j].lo or ni[j].hi<ni[i].lo
 energy=sum((w*f(x)for w,x in zip([6,3,6,3,12,6],ni)),I(0));M=[];rhs=[];meta=[]
 for j,p in enumerate(pts):
  M.append([ev(ds[c],p)for c in cols]);rhs.append(sum((f(ni[a])for a in labels[j]),I(0))-energy/12);meta.append(['value',j])
 for axis in range(3):
  for j in inside:
   M.append([ev(diff(ds[c],axis),pts[j])for c in cols]);rhs.append(fp(ni[labels[j][axis]]));meta.append(['derivative',j,axis])
 print('exact analytic jets built',flush=True)
 mn=np.array([[float(K.to_sympy(x).subs(r,float(Fraction(L))))for x in row]for row in M])
 from scipy.linalg import qr
 _,_,order=qr(mn.T,pivoting=True);selected=list(map(int,order[:13]));rest=[i for i in range(39)if i not in selected]
 mat=[[interval(x,rr)for x in M[i]]+[rhs[i]]for i in selected];pvs=[]
 for k in range(13):
  q=max(range(k,13),key=lambda i:abs(mat[i][k].lo+mat[i][k].hi));mat[k],mat[q]=mat[q],mat[k];pv=mat[k][k]
  assert pv.lo*pv.hi>0,('pivot',k,pv.pretty());pvs.append(report(pv))
  for i in range(k+1,13):
   fac=mat[i][k]/pv
   for j in range(k+1,14):mat[i][j]=mat[i][j]-fac*mat[k][j]
   mat[i][k]=I(0)
 solI=[I(0)]*13
 for i in reversed(range(13)):solI[i]=(mat[i][-1]-sum((mat[i][j]*solI[j]for j in range(i+1,13)),I(0)))/mat[i][i]
 residuals=[]
 for i in rest:
  v=sum((interval(c,rr)*x for c,x in zip(M[i],solI)),I(0))-rhs[i];residuals.append({'row':i,'type':meta[i],**report(v)})
 witness=next(x for x in residuals if int(x['exact']['lo_numerator'])*int(x['exact']['hi_numerator'])>0)
 wx=witness['exact'];wv=I(int(wx['lo_numerator']),int(wx['hi_numerator']),raw=True)
 assert I('-0.014300741173147').hi<wv.lo and wv.hi<I('-0.014300741173128').lo
 assert derivative(I(L)).hi<0 and derivative(I(U)).lo>0
 result={'status':'certified_inconsistent','scope':'current d4 symmetric three-point truncation, any differentiable minorant; no trace cap','bits':BITS,'r_interval':[L,U],'null_dimensions':[len(n)for n in Ns],'feature_pivots':[report(interval(p,rr))for p in pivs],'F_gauge_exact_identity':True,'gauge_coefficient_enclosures':gauge_bounds,'candidate_G_exact_identity':True,'conditional_domain':'all six nodes strictly inside (-1,0.57)','retained_columns':cols,'omitted_column':omit,'omitted_equals':[str(K.to_sympy(x))for x in sol],'triangle_labels':labels,'gram_determinants':dets,'equations':39,'unknowns_after_gauge':13,'selected_rows':selected,'gaussian_pivots':pvs,'solution':[report(x)for x in solI],'residuals':residuals,'contradiction_witness':witness,'seconds':time.time()-start}
 path=Path(output);assert not path.exists();path.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':result['status'],'witness':witness,'seconds':result['seconds']}),flush=True)
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--output',default='proof_work/actual_d4_contact_cert.json');a=p.parse_args();run(a.output)
