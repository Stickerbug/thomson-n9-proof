"""NONRIGOROUS sharp-subspace three-point experiments. Never a certificate.
Run with PYTHONPATH=proof_work/python_deps and OPENBLAS_NUM_THREADS=1.
"""
import argparse,itertools,json,time
from pathlib import Path
import numpy as np
import cvxpy as cp
from scipy.optimize import differential_evolution, minimize
from three_point_sampled import kernels,design,sample_triangles,minorant
ENERGY=25.759986531269831564

def candidate_data(degree):
    r=.7105483340929538113;h=np.sqrt(1-r*r)
    X=np.array([[r*np.cos(2*np.pi*k/3),r*np.sin(2*np.pi*k/3),sgn*h]for sgn in (1,-1)for k in range(3)]+[[np.cos((2*k+1)*np.pi/3),np.sin((2*k+1)*np.pi/3),0]for k in range(3)])
    gram=X@X.T
    alltrip=np.array([[gram[i,j],gram[i,k],gram[j,k]]for i,j,k in itertools.product(range(9),repeat=3)])
    distinct=np.array([[gram[i,j],gram[i,k],gram[j,k]]for i,j,k in itertools.combinations(range(9),3)])
    distinct=np.unique(np.round(np.sort(distinct,axis=1),13),axis=0)
    G=[m.sum(axis=0)for m in kernels(alltrip,degree)]
    eigen=[];null=[]
    for g in G:
        ev,U=np.linalg.eigh((g+g.T)/2)
        eigen.append(ev.tolist());null.append(U[:,ev<1e-8])
    return distinct,G,null,eigen

def reduced_design(points,degree,null,sharp=True):
    raw=design(points,degree)
    out=[]
    for k,N in enumerate(null):
        if N.shape[1]==0:continue
        m=np.einsum('ai,nab,bj->nij',N,raw[k],N)
        if k==0 and sharp:
            j=N.T@np.ones((degree+1,degree+1))@N
            m=m+j[None,:,:]/8
        out.append((k,m))
    return out

def lhs_expr(matrices,B,count):
    return sum(cp.sum(cp.multiply(m.reshape(count,-1),cp.reshape(B[k],(1,B[k].size),order='C')),axis=1)for k,m in matrices)

def residual(points,degree,A,c,h):
    return np.sum(h(points),axis=1)-c-sum(np.einsum('nij,ij->n',m,a)for m,a in zip(design(points,degree),A))

def from_angles(v):
    u,w,theta=v
    return np.array([[u,w,u*w+np.sqrt(max(0,(1-u*u)*(1-w*w)))*np.cos(theta)]])

def validate(degree,A,c,h,rng,count=15000):
    test=sample_triangles(count,rng)
    res=residual(test,degree,A,c,h)
    idx=np.argsort(res)[:100]
    def fun(v):
        v=np.asarray(v);single=v.ndim==1
        if single:v=v[:,None]
        u,w,theta=v
        pts=np.column_stack([u,w,u*w+np.sqrt(np.maximum(0,(1-u*u)*(1-w*w)))*np.cos(theta)])
        out=residual(pts,degree,A,c,h)
        return float(out[0])if single else out
    worst=test[idx[0]]
    angle=np.arccos(np.clip((worst[2]-worst[0]*worst[1])/np.sqrt((1-worst[0]**2)*(1-worst[1]**2)),-1,1))
    start=[worst[0],worst[1],angle]
    des=[]
    for seed in (710+degree,1710+degree):
        opt=differential_evolution(fun,[(-1,1),(-1,1),(0,np.pi)],seed=seed,popsize=10,maxiter=65,tol=1e-8,polish=True,workers=1,x0=start,vectorized=True,updating='deferred')
        des.append({'residual':float(opt.fun),'angle_parameters':opt.x.tolist(),'triangle':from_angles(opt.x)[0].tolist(),'evaluations':int(opt.nfev)})
    additions=np.vstack([test[idx]]+[from_angles(row['angle_parameters'])for row in des])
    return {'random_minimum':float(res.min()),'differential_evolution':des},additions

def run(degree,rounds=4,count=1800,trace_cap=10000,equality=True,free_target=False):
    started=time.time();rng=np.random.default_rng(90031+degree)
    h,nodes,coefs,x=minorant()
    cand,G,null,evals=candidate_data(degree)
    dims=[a.shape[1]for a in null]
    print('degree',degree,'nullities',dims,'candidate triangle types',len(cand),flush=True)
    points=np.vstack([sample_triangles(count,rng),cand])
    # Include singular and almost singular triangles from the outset.
    uv=rng.uniform(-1,1,(400,2))
    boundary=np.vstack([np.column_stack([uv,uv[:,0]*uv[:,1]+sgn*np.sqrt((1-uv[:,0]**2)*(1-uv[:,1]**2))])for sgn in (-1,1)])
    points=np.vstack([points,boundary,[[1,1,1],[-1,-1,1],[-1,1,-1],[1,-1,-1]]])
    B={k:cp.Variable((n,n),symmetric=True)for k,n in enumerate(dims)if n}
    tau=cp.Variable(nonneg=True)
    cvar=cp.Variable()if free_target else None
    csharp=ENERGY/12
    trace=sum(cp.trace(b)for b in B.values())
    f111=cp.sum(null[0]@B[0]@null[0].T)
    history=[];last=None
    for iteration in range(rounds):
        mats=reduced_design(points,degree,null,sharp=not free_target)
        rhs=np.sum(h(points),axis=1)
        constraints=[b>>0 for b in B.values()]+[trace<=trace_cap]
        lhs=lhs_expr(mats,B,len(points))
        if free_target:
            constraints+=[cvar+lhs<=rhs]
            objective=cp.Maximize(12*cvar-1.5*f111)
        else:
            constraints+=[lhs+csharp<=rhs+tau]
            if equality:
                cm=reduced_design(cand,degree,null,sharp=True)
                constraints+=[lhs_expr(cm,B,len(cand))+csharp==np.sum(h(cand),axis=1)]
            objective=cp.Minimize(tau+1e-12*trace)
        problem=cp.Problem(objective,constraints)
        try:
            problem.solve(solver='CLARABEL',tol_gap_abs=2e-9,tol_gap_rel=2e-9,tol_feas=2e-9,max_iter=140)
        except Exception as error:
            print('solver exception',str(error),flush=True)
        row={'iteration':iteration,'status':problem.status,'training_count':len(points),'time_seconds':time.time()-started}
        if any(b.value is None for b in B.values()):
            print(json.dumps(row),flush=True);history.append(row);break
        A=[null[k]@B[k].value@null[k].T if k in B else np.zeros((degree-k+1,degree-k+1))for k in range(degree+1)]
        c=float(cvar.value)if free_target else (ENERGY+1.5*A[0].sum())/12
        validation,additions=validate(degree,A,c,h,rng)
        cres=residual(cand,degree,A,c,h)
        row.update({'objective':float(12*c-1.5*A[0].sum()),'tau':None if free_target else float(tau.value),'trace':float(trace.value),'candidate_residual_min':float(cres.min()),'candidate_residual_max':float(cres.max()),'min_B_eigenvalue':float(min(np.linalg.eigvalsh(b.value).min()for b in B.values())),'validation':validation})
        print(json.dumps(row),flush=True);history.append(row)
        last={'A':[a.tolist()for a in A],'B':{str(k):b.value.tolist()for k,b in B.items()},'c':c}
        points=np.vstack([points,additions])
        if not free_target and tau.value>0.1 and iteration>=1:break
    result={'warning':'NONRIGOROUS SDP plus sampled and differential-evolution validation; NOT a global proof or an infeasibility certificate. Trace cap is an extra numerical restriction.','degree':degree,'trace_cap':trace_cap,'candidate_equalities':equality,'free_target':free_target,'nullities':dims,'candidate_G_eigenvalues':evals,'nullspace_bases':[a.tolist()for a in null],'candidate_triangle_types':cand.tolist(),'history':history,'solution':last,'minorant_newton_nodes':x.tolist(),'minorant_newton_coefficients':coefs.tolist(),'elapsed_seconds':time.time()-started}
    suffix=('_free'if free_target else ('_eq'if equality else '_noeq'))
    path=Path(__file__).with_name('sharp_three_point_d'+str(degree)+suffix+'.json')
    assert not path.exists(),path
    path.write_text(json.dumps(result,indent=2)+'\n')
    print('saved',str(path),'seconds',result['elapsed_seconds'],flush=True)
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--degree',type=int,default=4);p.add_argument('--rounds',type=int,default=4);p.add_argument('--count',type=int,default=1800);p.add_argument('--trace-cap',type=float,default=10000);p.add_argument('--no-equality',action='store_true');p.add_argument('--free-target',action='store_true')
    a=p.parse_args();run(a.degree,a.rounds,a.count,a.trace_cap,not a.no_equality,a.free_target)
