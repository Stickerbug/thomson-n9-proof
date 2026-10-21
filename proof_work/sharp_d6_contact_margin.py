"""NONRIGOROUS equality-eliminated feasibility crosscheck; no global rounds."""
import json
from pathlib import Path
from fractions import Fraction as F
import numpy as np
import cvxpy as cp
from sharp_d6_analytic_psd import polynomials,evaluate
from candidate_low_rank import features,nullspace_two_rows
from sharp_three_point import candidate_data,ENERGY
out=Path(__file__).with_suffix('.json');assert not out.exists()
r=F('0.71054833409295381132770417927279124');N=[]
for k in range(7):
 p,c=features(r,k,7-k);cols=nullspace_two_rows(p,c)
 z=np.array([[float(v)for v in col]for col in cols]).T if cols else np.empty((7-k,0))
 N.append(np.linalg.qr(z,mode='reduced')[0]if cols else z)
P,indices=polynomials(N);cand,_,_,_=candidate_data(6)
interior=cand[(1+2*np.prod(cand,axis=1)-np.sum(cand*cand,axis=1))>1e-7]
A=np.vstack([evaluate(P,cand)]+[evaluate(P,interior,i)for i in range(3)])
b=np.concatenate([np.sum((2-2*cand)**(-.5),axis=1)-ENERGY/12]+[(2-2*interior[:,i])**(-1.5)for i in range(3)])
u,s,vh=np.linalg.svd(A,full_matrices=True);rank=int((s>s[0]*1e-10).sum());x0=np.linalg.lstsq(A,b,rcond=1e-10)[0];Z=vh[rank:].T
v=cp.Variable(Z.shape[1]);x=x0+Z@v;B={};index={t:j for j,t in enumerate(indices)}
for k,n in enumerate(N):
 if n.shape[1]:B[k]=cp.bmat([[x[index[k,min(i,j),max(i,j)]]for j in range(n.shape[1])]for i in range(n.shape[1])])
trace=sum(cp.trace(bb)for bb in B.values());margin=cp.Variable();p=cp.Problem(cp.Maximize(margin),[bb-margin*np.eye(bb.shape[0])>>0 for bb in B.values()]+[trace<=10000]);p.solve(solver='CLARABEL',tol_gap_abs=1e-10,tol_gap_rel=1e-10,tol_feas=1e-10,max_iter=300)
result={'warning':'NONRIGOROUS SVD elimination drops dependent equations at rcond1e-10; NOT proof','status':p.status,'rank':rank,'equations':len(b),'unknowns':len(x0),'free_dimensions':Z.shape[1],'singular_values':s.tolist(),'linear_max_error':float(abs(A@x0-b).max()),'nullspace_defect':float(abs(A@Z).max()),'trace_cap':10000,'maximized_margin':float(margin.value)if margin.value is not None else None}
if x.value is not None:
 result.update({'trace':float(trace.value),'contact_max_error':float(abs(A@x.value-b).max()),'min_eigenvalue':float(min(np.linalg.eigvalsh(bb.value).min()for bb in B.values())),'x':x.value.tolist(),'B':{str(k):bb.value.tolist()for k,bb in B.items()}})
print(json.dumps(result),flush=True);out.write_text(json.dumps(result,indent=2)+'\n')
