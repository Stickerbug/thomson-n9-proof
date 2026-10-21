"""Numerical projection diagnostic only, not proof."""
import json,time
from pathlib import Path
from fractions import Fraction as F
import numpy as np
from candidate_low_rank import features,nullspace_two_rows
from sharp_boundary_actualf_v3 import polynomials
from sharp_d8_conditional_actualf_eliminated import evaluate
from sharp_three_point import candidate_data,ENERGY
ROOT=Path(__file__).parent
start=time.time();src=json.loads((ROOT/'nonsharp_nullspace_actualf_d10_run2.json').read_text());best=src['best_solution'];degree=10;r=F('0.71054833409295381132770417927279124');N=[]
for k in range(degree+1):
 p,c=features(r,k,degree+1-k);cols=nullspace_two_rows(p,c);z=np.array([[float(v)for v in col]for col in cols]).T if cols else np.empty((degree+1-k,0));N.append(np.linalg.qr(z,mode='reduced')[0]if cols else z)
P,indices=polynomials(N,degree);cand,_,_,_=candidate_data(degree);interior=cand[(1+2*np.prod(cand,axis=1)-np.sum(cand*cand,axis=1))>1e-7]
Aeq=np.vstack([evaluate(P,cand)]+[evaluate(P,interior,i)for i in range(3)])
target=np.concatenate([np.sum((2-2*cand)**(-.5),axis=1)-ENERGY/12]+[(2-2*interior[:,i])**(-1.5)for i in range(3)])
sol,_,rank,sv=np.linalg.lstsq(Aeq,target,rcond=1e-10);_,_,Vh=np.linalg.svd(Aeq,full_matrices=True);Z=Vh[rank:].T
rawA=[np.array(a)for a in best['A']];B=[n.T@a@n for n,a in zip(N,rawA)];x=np.array([B[k][i,j]for k,i,j in indices]);oldx=np.array(best['x']);projected=sol+Z@(Z.T@(x-sol))
index={a:j for j,a in enumerate(indices)}
def blocks(xx):return {str(k):np.array([[xx[index[k,min(i,j),max(i,j)]]for j in range(n.shape[1])]for i in range(n.shape[1])])for k,n in enumerate(N)if n.shape[1]}
def eigenvalues(xx):return {k:np.linalg.eigvalsh(b).tolist()for k,b in blocks(xx).items()}
eig=eigenvalues(projected);mn=min(min(v)for v in eig.values())
result={'warning':'NUMERICAL diagnostic; no PSD existence or global certificate proof','source':'nonsharp_nullspace_actualf_d10_run2.json best_solution','source_iteration':best['iteration'],'unknowns':len(x),'contact_equations':len(target),'contact_rank':int(rank),'singular_values':sv.tolist(),'source_x_vs_reconstructed_max':float(abs(x-oldx).max()),'source_N_vs_rebuilt_max':float(max((abs(n-np.array(old)).max()if n.size else 0)for n,old in zip(N,src['nullspace_bases']))),'original_contact_max_error':float(abs(Aeq@x-target).max()),'projection_contact_max_error':float(abs(Aeq@projected-target).max()),'least_squares_contact_max_error':float(abs(Aeq@sol-target).max()),'projection_distance':float(np.linalg.norm(projected-x)),'original_x_norm':float(np.linalg.norm(x)),'original_block_eigenvalues':eigenvalues(x),'projected_block_eigenvalues':eig,'projected_min_eigenvalue':float(mn),'source_x':x.tolist(),'projected_x':projected.tolist(),'projected_B':{k:b.tolist()for k,b in blocks(projected).items()},'seconds':time.time()-start,'near_PSD_threshold':-3e-7,'permit_one_contact_SDP':bool(mn>=-3e-7)}
out=ROOT/'project_nonsharp_d10_contactjets_v1.json';assert not out.exists();out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in ['source_x','projected_x','projected_B','singular_values','original_block_eigenvalues','projected_block_eigenvalues']},indent=2),flush=True)
print('projected block minima',{k:min(v)for k,v in eig.items()},flush=True)
