"""Exact small geometric row identities. No rank claim about numerical d10 model."""
import sympy as s,json
from pathlib import Path
from dyadic_interval import I
from certify_pair_moments import L,U
r=s.symbols('r');names='ABCDFG';nodes=[1-s.Rational(3,2)*r*r,2*r*r-1,r*r/2-1,-s.Rational(1,2),r/2,-r];weights=[6,3,6,3,12,6]
geom=json.loads(Path('proof_work/candidate_triple_types_v1.json').read_text())['triangle_types'];meta=[];H=[];values=[];derivs={};tangents={};sym=[]
for j,t in enumerate(geom):
 lab=[names.index(a)for a in t['labels']];pt=[nodes[a]for a in lab];values.append(len(meta));meta.append(['value',t['labels']]);hh=[-s.Rational(w,12)for w in weights]
 for a in lab:hh[a]+=1
 H.append(hh)
 hp=s.zeros(3,6)
 for i,a in enumerate(lab):hp[i,a]=1/(2-2*nodes[a])
 if t['status']!='identically_boundary':
  ids=[]
  for axis in range(3):ids.append(len(meta));meta.append(['gradient',t['labels'],axis]);H.append(list(hp[axis,:]))
  derivs[j]=ids
  for a in range(3):
   for b in range(a+1,3):
    if lab[a]==lab[b] and (a==0 or lab[a-1]!=lab[a]):sym.append({ids[a]:1,ids[b]:-1})
 else:
  u,v,t0=pt;g=[2*(v*t0-u),2*(u*t0-v),2*(u*v-t0)];ids=[]
  for axis in [1,2]:ids.append(len(meta));meta.append(['tangent',t['labels'],axis]);H.append(list(g[0]*hp[axis,:]-g[axis]*hp[0,:]))
  tangents[j]=(ids,g)
  if len(set(lab))==1:sym.extend([{ids[0]:1},{ids[1]:1}])
  else:assert lab[1]==lab[2];sym.append({ids[0]:1,ids[1]:-1})
assert len(meta)==45 and len(sym)==10
rows=[]
for d in sym:rows.append([d.get(j,0)for j in range(45)])
v=[0]*45;dv=[0]*45
for j,t in enumerate(geom):
 w=t['multiplicity'];v[values[j]]=w;lab=[names.index(a)for a in t['labels']];vel=[s.diff(nodes[a],r)for a in lab]
 if j in derivs:
  for axis,k in enumerate(derivs[j]):dv[k]=w*vel[axis]
 else:
  ids,g=tangents[j];assert s.factor(sum(a*b for a,b in zip(g,vel)))==0
  for axis,k in enumerate(ids,1):dv[k]=s.cancel(w*vel[axis]/g[0])
rows.extend([v,dv]);W=s.Matrix(rows);HH=s.Matrix(H);HH[:,0]+=r*HH[:,3];HH=HH[:,[0,1,2,4,5]]
ep=s.Matrix([[-6/r,3*r/(1-r*r),6*r/(4-r*r),6/(2-r),-6/(2+2*r)]])
Q=(W*HH).applyfunc(s.cancel);assert Q[:11,:]==s.zeros(11,5);assert (Q[11:12,:]-7*ep).applyfunc(s.cancel)==s.zeros(1,5)
_,piv=W.subs(r,s.Rational(7,10)).rref();assert len(piv)==12;det=s.factor(W[:,list(piv)].det());assert det!=0
rr=I(L,U)
def poly(x):
 ans=I(0)
 for c in s.Poly(x,r).all_coeffs():ans=ans*rr+I(str(c))
 return ans
num,den=s.fraction(det);di=poly(num)/poly(den);assert di.lo*di.hi>0
out={'status':'exact_12_geometric_row_relations_and_rhs_verified','warning':'W*M=0 follows from stated complementarity and differentiated kernel-sum argument; this small script checks W independence and RHS identities, not a d10 full kernel identity or invertible33minor','rows':[list(map(str,row))for row in rows],'row_meta':meta,'minor_columns':list(piv),'minor_determinant':str(det),'minor_bounds':di.bounds(),'rhs_product':'first11=0,last=7Eprime','Eprime_coefficients':list(map(str,list(ep))),'scope':'true r_star, no rational-radius sharp claim'}
p=Path('proof_work/d10_contact_left_geometry_v1.json');assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k]for k in ['status','minor_determinant','rhs_product']}))
