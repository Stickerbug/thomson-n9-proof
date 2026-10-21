"""Numerical sharp Thomson n=9 contact diagnostics; DISCOVERY ONLY."""
import json, itertools, time
from pathlib import Path
from fractions import Fraction as Fr
import numpy as np
from candidate_low_rank import features, nullspace_two_rows
from sharp_boundary_actualf_v3 import polynomials, Compiled
from sharp_three_point import ENERGY
ROOT=Path(__file__).parent
PREFIX='d12_contact2026_'
RSTRING='0.71054833409295381132770417927279124'
KEY=np.array([-.29693709,.4225354,.4225354])
DEGREE=12

def exact_candidate(r):
    A=1-Fr(3,2)*r*r; B=2*r*r-1; C=r*r/2-1
    def dot(i,j):
        if i==j:return Fr(1)
        if i>=6 and j>=6:return Fr(-1,2)
        if i>=6:i,j=j,i
        if j>=6:return -r if (j-6-i%3)%3==1 else r/2
        return (A if i//3==j//3 else B if i%3==j%3 else C)
    points=sorted(set(tuple(sorted([dot(i,j),dot(i,k),dot(j,k)])) for i,j,k in itertools.combinations(range(9),3)))
    det=lambda p:1+2*p[0]*p[1]*p[2]-sum(x*x for x in p)
    return points,[det(p) for p in points]

def derivative(comp, points, axes=()):
    pw=comp.powers.copy(); factors=np.ones(len(pw))
    for axis in axes:
        factors*=pw[:,axis]; pw[:,axis]=np.maximum(0,pw[:,axis]-1)
    return np.asarray(comp.M.T.dot((comp.monomials(points,pw)*factors).T).T)

def gram_geometry(p):
    u,v,t=p
    g=np.array([2*(v*t-u),2*(u*t-v),2*(u*v-t)])
    H=np.array([[-2,2*t,2*v],[2*t,-2,2*u],[2*v,2*u,-2.]])
    _,_,vh=np.linalg.svd(g[None,:],full_matrices=True)
    T=vh[1:].T
    return g,H,T

def blocks(xx, N, indices):
    lookup={t:j for j,t in enumerate(indices)}
    return {str(k):np.array([[xx[lookup[k,min(i,j),max(i,j)]] for j in range(n.shape[1])] for i in range(n.shape[1])]) for k,n in enumerate(N) if n.shape[1]}

def original(xx,N,indices):
    bb=blocks(xx,N,indices)
    AA=[n@bb[str(k)]@n.T if str(k) in bb else np.zeros((DEGREE+1-k,DEGREE+1-k)) for k,n in enumerate(N)]
    cc=(ENERGY+1.5*AA[0].sum())/12
    return bb,AA,float(cc)

def jets(xx, comp, cand):
    grads=np.column_stack([(2-2*cand[:,i])**(-1.5)-derivative(comp,cand,(i,))@xx for i in range(3)])
    HH=np.empty((len(cand),3,3))
    for i in range(3):
        for j in range(3):
            HH[:,i,j]=(-derivative(comp,cand,(i,j))@xx)
            if i==j:HH[:,i,j]+=3*(2-2*cand[:,i])**(-2.5)
    return grads,HH

def build():
    start=time.time(); r=Fr(RSTRING); N=[]
    for k in range(DEGREE+1):
        pp,cc=features(r,k,DEGREE+1-k); cols=nullspace_two_rows(pp,cc)
        z=np.array([[float(v) for v in col] for col in cols]).T if cols else np.empty((DEGREE+1-k,0))
        N.append(np.linalg.qr(z,mode='reduced')[0] if cols else z)
    P,indices=polynomials(N,DEGREE);comp=Compiled(P)
    exact,det=exact_candidate(r);cand=np.array([[float(v) for v in p] for p in exact]); interior=np.array([d>0 for d in det]); boundary=~interior
    Aeq=np.vstack([derivative(comp,cand)]+[derivative(comp,cand[interior],(i,)) for i in range(3)])
    target=np.concatenate([np.sum((2-2*cand)**(-.5),axis=1)-ENERGY/12]+[(2-2*cand[interior,i])**(-1.5) for i in range(3)])
    sol,_,rank,sv=np.linalg.lstsq(Aeq,target,rcond=1e-10);_,_,vh=np.linalg.svd(Aeq,full_matrices=True); Z=vh[rank:].T
    Dr=np.stack([derivative(comp,cand,(i,)) for i in range(3)],axis=1)
    fprime=(2-2*cand)**(-1.5)
    tang=[];targ=[];bd=[]
    for j in np.flatnonzero(boundary):
        g,H,T=gram_geometry(cand[j]);tmat=T.T@Dr[j];trhs=T.T@fprime[j]
        tang.append(tmat);targ.append(trhs)
        bd.append({'candidate_index':int(j),'point':cand[j].tolist(),'gram_gradient':g.tolist(),'tangent_basis':T.tolist(),'tangent_coeff_nullspace_norm':float(np.linalg.norm(tmat@Z)),'tangent_rhs_mismatch':float(np.linalg.norm(trhs-tmat@sol))})
    At=np.vstack(tang);bt=np.concatenate(targ);AA=np.vstack([Aeq,At]);bb=np.r_[target,bt]
    ss,_,rank_aug,sv_aug=np.linalg.lstsq(AA,bb,rcond=1e-10);_,_,vv=np.linalg.svd(AA,full_matrices=True);ZZ=vv[rank_aug:].T
    diag={'warning':'DISCOVERY ONLY; numerical rank and PSD are not proofs; rational r is not an exact root','r_rational_approximation':RSTRING,'degree':DEGREE,'unknowns':len(indices),'nullities':[n.shape[1] for n in N],'contact_equations':len(target),'contact_rank':int(rank),'singular_values':sv.tolist(),'linear_contact_max_error':float(np.max(abs(Aeq@sol-target))),'contact_plus_tangent_rank':int(rank_aug),'contact_plus_tangent_max_error':float(np.max(abs(AA@ss-bb))),'augmented_singular_values':sv_aug.tolist(),'boundary_tangent_conditions':bd,'candidate_points':cand.tolist(),'candidate_exact_fraction':[[str(v) for v in p] for p in exact],'candidate_gram_determinants':[str(v) for v in det],'key_point':KEY.tolist(),'key_gram':float(1+2*np.prod(KEY)-KEY@KEY),'sources':[]}
    sources=[('psd_project_nonsharp_d10_contactjets_v1.json','psd_projection'),('sharp_boundary_actualf_d10_v3.json','best_solution'),('nonsharp_nullspace_actualf_d10_run2.json','best_solution')]
    srcs={}
    for filename,key in sources:
        data=json.loads((ROOT/filename).read_text()); val=data.get(key) or data.get('solution'); aa=[np.array(a) for a in val['A']]; aa=[np.pad(aa[k],((0,2),(0,2))) if k<len(aa) else np.zeros((DEGREE+1-k,DEGREE+1-k)) for k in range(DEGREE+1)]
        bs=[n.T@a@n for n,a in zip(N,aa)]; xx=np.array([bs[k][i,j] for k,i,j in indices]); bbs=blocks(xx,N,indices)
        gg,hh=jets(xx,comp,cand);bdj=[]
        for j in np.flatnonzero(boundary):
            g,H,T=gram_geometry(cand[j]);lam=float(gg[j]@g/(g@g));bdj.append({'index':int(j),'lambda':lam,'tangent_gradient':(T.T@gg[j]).tolist(),'tangent_Lagrangian_H_eigenvalues':np.linalg.eigvalsh(T.T@(hh[j]-lam*H)@T).tolist()})
        row={'source':filename,'key':key,'contact_max_error':float(max(abs(Aeq@xx-target))),'tangent_max_error':float(max(abs(At@xx-bt))),'min_B_eigenvalue':float(min(np.linalg.eigvalsh(b).min() for b in bbs.values())),'trace':float(sum(np.trace(b) for b in bbs.values())),'key_R':float(comp.kernel(xx)(KEY)[0]),'interior_H_min_eigenvalue':float(min(np.linalg.eigvalsh(hh[interior]).ravel())),'boundary_jets':bdj}
        diag['sources'].append(row);srcs[filename]=(data,xx)
    diag['build_seconds']=time.time()-start
    return dict(N=N,indices=indices,comp=comp,cand=cand,interior=interior,boundary=boundary,Aeq=Aeq,target=target,sol=sol,Z=Z,At=At,bt=bt,augA=AA,augb=bb,augsol=ss,augZ=ZZ,Dr=Dr,fprime=fprime,diagnostic=diag,sources=srcs)

def main():
    b=build();out=ROOT/(PREFIX+'diagnostics.json');assert not out.exists();out.write_text(json.dumps(b['diagnostic'],indent=2)+chr(10))
    print(json.dumps(b['diagnostic'],indent=2),flush=True)
if __name__=='__main__':main()
