"""Enumerate existing <=9 wells only; no new optimization and no global certificate."""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
import json,time,hashlib
import numpy as np
BASE=Path(__file__).parent
mp=BASE/'nonsharp_d10_root25_7599205_v10.json';model=json.loads(mp.read_text());terms=[(tuple(e),np.longdouble(F(c).numerator)/np.longdouble(F(c).denominator))for e,c in model['residual_monomial']]
def vectorR(xyz):
 xyz=np.asarray(xyz,dtype=np.longdouble);powers=[]
 for k in range(3):powers.append(np.array([xyz[:,k]**j for j in range(28)]))
 return np.array(sum(c*powers[0][i]*powers[1][j]*powers[2][k]for (i,j,k),c in terms),dtype=np.longdouble)
start=time.monotonic();probe=json.loads((BASE/'two_other_valleys2026_probe.json').read_text())['results'];out=[]
for row in probe:
 u,v,t=map(np.longdouble,row['triangle_decimal']);g=1+2*u*v*t-u*u-v*v-t*t;A=np.array([[1,0,0],[u,np.sqrt(1-u*u),0],[v,(t-u*v)/np.sqrt(1-u*u),np.sqrt(g)/np.sqrt(1-u*u)]],dtype=np.longdouble)
 wells=row['wells'][:9];Q=np.array([p['q']for p in wells],dtype=np.longdouble);Q/=np.sqrt(np.sum(Q*Q,axis=1))[:,None];points=np.vstack([A,Q]);dots=points@points.T
 triples=list(combinations(range(len(points)),3));res=vectorR([[dots[i,j],dots[i,k],dots[j,k]]for i,j,k in triples]);lookup={tri:r for tri,r in zip(triples,res)};Ranchor=lookup[(0,1,2)];candidates=[]
 for ids in combinations(range(len(Q)),6):
  ext=[i+3 for i in ids];vertices=[0,1,2]+ext
  if any(dots[i,j]>.56+1e-12 for i,j in combinations(vertices,2)):continue
  phi=sum(lookup[tuple(sorted([i,j,q]))]for i,j in combinations(range(3),2)for q in ext)
  psi=sum(lookup[tuple(sorted([a,q,r]))]for a in range(3)for q,r in combinations(ext,2))
  eta=sum(lookup[tri]for tri in combinations(ext,3));total=Ranchor+phi+psi+eta
  energy=sum(1/np.sqrt(2-2*dots[i,j])for i,j in combinations(vertices,2))
  candidates.append({'well_indices':list(ids),'phi18':float(phi),'psi45':float(psi),'eta20':float(eta),'phi_plus_psi63':float(phi+psi),'all_external83':float(phi+psi+eta),'all84R':float(total),'energy':float(energy),'max_pair_dot':float(max(dots[i,j]for i,j in combinations(vertices,2)))})
 budget=float(F(row['budget_exact']));whole=budget+float(Ranchor);mins={k:min(candidates,key=lambda c:c[k])for k in ['phi18','phi_plus_psi63','all_external83','all84R','energy']}if candidates else {}
 rec={'name':row['name'],'triangle':row['triangle_decimal'],'wells_considered':len(Q),'combinations_tested':len(list(combinations(range(len(Q)),6))),'feasible_combinations':len(candidates),'R_anchor':float(Ranchor),'external83_budget_K':budget,'all84_budget_7UminusB':whole,'minima':mins,'all_feasible_combinations':candidates,'all_discovered_phi_plus_psi_exceed_K':bool(candidates)and min(c['phi_plus_psi63']for c in candidates)>budget,'all_discovered_full83_exceed_K':bool(candidates)and min(c['all_external83']for c in candidates)>budget};out.append(rec)
 print('RESULT',json.dumps({k:v for k,v in rec.items()if k!='all_feasible_combinations'}),flush=True)
path=BASE/'two_other_valleys2026_augmented_enum.json';path.write_text(json.dumps({'status':'finite_existing_well_enumeration_only_not_global_bound','warning':'Minima are only among existing discrete well combinations. Full84R compares to7(U-B); external83R compares toK=7(U-B)-R(T).','model_sha256':hashlib.sha256(mp.read_bytes()).hexdigest(),'seconds':time.monotonic()-start,'rows':out},indent=2)+'\n');print('SAVED',path)
