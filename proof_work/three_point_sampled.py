"""NONRIGOROUS sampled three-point SDP experiment, N=9 on S^2.
Run PYTHONPATH=proof_work/python_deps python3 proof_work/three_point_sampled.py --degree 3
S_k matrices use Chebyshev transverse kernels and S_3 permutation average.
"""
import argparse,itertools,json
import numpy as np
import cvxpy as cp
from pathlib import Path
from numpy.polynomial import Polynomial
N=9

def minorant():
    r=.71054833409295381132770417927279124
    nodes=np.array([1-1.5*r*r,-.5,2*r*r-1,r*r/2-1,r/2,-r])
    # Newton divided differences for double Hermite nodes.
    x=np.repeat(np.sort(nodes),2);m=len(x);Q=np.zeros((m,m))
    f=lambda t:(2-2*t)**(-.5)
    fp=lambda t:(2-2*t)**(-1.5)
    for i in range(m):
        Q[i,0]=f(x[i])
        if i:
            Q[i,1]=fp(x[i]) if x[i]==x[i-1] else (Q[i,0]-Q[i-1,0])/(x[i]-x[i-1])
        for j in range(2,i+1):Q[i,j]=(Q[i,j-1]-Q[i-1,j-1])/(x[i]-x[i-j])
    coefficients=np.diag(Q)
    def evaluate(t):
        t=np.asarray(t);v=np.zeros_like(t)+coefficients[-1]
        for k in range(m-2,-1,-1):v=coefficients[k]+(t-x[k])*v
        return v
    return evaluate,nodes,coefficients,x

def sample_triangles(count,rng):
    # Anchor x=e_z; y,z chosen by their z coordinates and transverse angle.
    u=rng.uniform(-1,1,count);v=rng.uniform(-1,1,count)
    theta=rng.uniform(0,np.pi,count)
    t=u*v+np.sqrt((1-u*u)*(1-v*v))*np.cos(theta)
    return np.column_stack([u,v,t])

def kernels(points,degree):
    out=[np.zeros((len(points),degree-k+1,degree-k+1))for k in range(degree+1)]
    for perm in itertools.permutations(range(3)):
        u,v,t=points[:,perm].T;a=t-u*v;b=(1-u*u)*(1-v*v)
        Q=[np.ones(len(points))]
        if degree:Q.append(a)
        for k in range(1,degree):Q.append(2*a*Q[-1]-b*Q[-2])
        for k in range(degree+1):
            powers=np.arange(degree-k+1)
            z=u[:,None]**powers;w=v[:,None]**powers
            out[k]+=Q[k][:,None,None]*z[:,:,None]*w[:,None,:]/6
    return out

def design(points,degree):
    s=kernels(points,degree)
    repeats=[kernels(np.column_stack([np.ones(len(points)),points[:,j],points[:,j]]),degree)for j in range(3)]
    return [(N-2)*s[k]+sum(row[k]for row in repeats)for k in range(degree+1)]

def candidate_triangles():
    r=.7105483340929538;h=np.sqrt(1-r*r)
    X=np.array([[r*np.cos(2*np.pi*k/3),r*np.sin(2*np.pi*k/3),sgn*h]for sgn in (1,-1)for k in range(3)]+[[np.cos((2*k+1)*np.pi/3),np.sin((2*k+1)*np.pi/3),0]for k in range(3)])
    G=X@X.T
    return np.unique(np.round([[G[i,j],G[i,k],G[j,k]]for i,j,k in itertools.permutations(range(9),3)],13),axis=0)

def run(degree,count,rounds):
    rng=np.random.default_rng(9017+degree)
    h,nodes,coefs,x=minorant()
    grid=np.linspace(-1,.999,5000)
    print('Hermite float diagnostic max(h-f)=',float(np.max(h(grid)-(2-2*grid)**(-.5))),flush=True)
    points=np.vstack([sample_triangles(count,rng),candidate_triangles()])
    A=[cp.Variable((degree-k+1,degree-k+1),symmetric=True)for k in range(degree+1)]
    c=cp.Variable();F111=cp.sum(A[0]);objective=12*c-1.5*F111
    history=[]
    for iteration in range(rounds):
        matrices=design(points,degree)
        lhs=c+sum(cp.sum(cp.multiply(m.reshape(len(points),-1),cp.reshape(a,(1,a.size),order='C')),axis=1)for m,a in zip(matrices,A))
        rhs=np.sum(h(points),axis=1)
        problem=cp.Problem(cp.Maximize(objective),[a>>0 for a in A]+[lhs<=rhs])
        try:problem.solve(solver='CLARABEL',tol_gap_abs=1e-8,tol_feas=1e-8,max_iter=150)
        except Exception as e:
            print('CLARABEL exception',repr(e),flush=True)
            problem.solve(solver='SCS',eps=1e-6,max_iters=20000)
        if any(a.value is None for a in A):raise RuntimeError(problem.status)
        # Entirely independent sample finds violations; this is NOT a certificate.
        test=sample_triangles(12000,rng);testdesign=design(test,degree)
        residual=np.sum(h(test),axis=1)-float(c.value)-sum(np.einsum('nij,ij->n',m,a.value)for m,a in zip(testdesign,A))
        smallest=np.argsort(residual)[:250]
        row={'iteration':iteration,'status':problem.status,'sampled_objective':float(problem.value),'minimum_test_residual':float(residual.min()),'training_triangles':len(points),'minimum_psd_eigenvalue':float(min(np.linalg.eigvalsh(a.value).min()for a in A))}
        print(json.dumps(row),flush=True);history.append(row)
        if residual.min()>-1e-7:break
        points=np.vstack([points,test[smallest]])
    result={'warning':'NONRIGOROUS sampled constraints; objective need not be a valid global lower bound','degree':degree,'history':history,'c':float(c.value),'A':[a.value.tolist()for a in A],'minorant_newton_nodes':x.tolist(),'minorant_newton_coefficients':coefs.tolist(),'normalization':'maximize 12c-1.5F(1,1,1), subject to c+7F+sum F(1,t,t)<=sum h'}
    path=Path(__file__).with_name('three_point_sampled_d'+str(degree)+'.json')
    if not path.exists():path.write_text(json.dumps(result,indent=2)+'\n')
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--degree',type=int,default=3);p.add_argument('--count',type=int,default=1000);p.add_argument('--rounds',type=int,default=3)
    a=p.parse_args();run(a.degree,a.count,a.rounds)
