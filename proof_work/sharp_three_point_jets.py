"""NONRIGOROUS necessary contact equations for sharp three-point bounds.
Interior triangles require all first derivatives of R to vanish. Derivatives
use fourth-order finite differences. Linear inconsistency is only diagnostic.
"""
import json
from pathlib import Path
import numpy as np
from sharp_three_point import candidate_data,reduced_design,ENERGY
from three_point_sampled import minorant

def vectorize(points,degree,null):
    cols=[]
    for k,M in reduced_design(points,degree,null,sharp=True):
        n=M.shape[1]
        for i in range(n):
            for j in range(i,n):cols.append(M[:,i,j]*(1 if i==j else 2))
    return np.stack(cols,axis=1)

def run(d):
    h,_,_,_=minorant();cand,G,N,eigs=candidate_data(d)
    det=lambda p:1+2*np.prod(p,axis=1)-np.sum(p*p,axis=1)
    interior=cand[det(cand)>1e-7]
    mats=[vectorize(cand,d,N)];rhs=[np.sum(h(cand),axis=1)-ENERGY/12]
    for axis in range(3):
        step=2e-5;shift=np.eye(3)[axis]*step
        samples=[interior-2*shift,interior-shift,interior+shift,interior+2*shift]
        coef=[1,-8,8,-1]
        mats.append(sum(c*vectorize(p,d,N)for c,p in zip(coef,samples))/(12*step))
        rhs.append(sum(c*np.sum(h(p),axis=1)for c,p in zip(coef,samples))/(12*step))
    A=np.vstack(mats);b=np.concatenate(rhs)
    sol,_,rank,s=np.linalg.lstsq(A,b,rcond=1e-10)
    r=A@sol-b
    result={'warning':'NONRIGOROUS finite-difference linear-system diagnostic, no PSD imposed','degree':d,'unknowns':A.shape[1],'equations':A.shape[0],'rank':int(rank),'singular_values':s.tolist(),'interior_candidate_triangles':len(interior),'max_absolute_contact_equation_error':float(abs(r).max()),'l2_equation_error':float(np.linalg.norm(r)),'coefficient_l2_norm':float(np.linalg.norm(sol)),'all_candidate_gram_determinants':det(cand).tolist()}
    print(json.dumps(result),flush=True)
    return result
if __name__=='__main__':
    out=[run(d)for d in (4,6)]
    p=Path(__file__).with_name('sharp_contact_jets.json');assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n')
