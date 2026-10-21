import json, math, time
from pathlib import Path
import numpy as np
from scipy.optimize import differential_evolution, minimize

ROOT=Path(__file__).parent
MODEL=json.loads((ROOT/'nonsharp_d10_root25_7599205_v10.json').read_text())
terms=[(tuple(e),float(s.split('/')[0])/float(s.split('/')[1])) for e,s in MODEL['residual_monomial']]
# Horner-free vectorized long-double monomial evaluation; coefficients are exact rationals

def R(points):
    x=np.asarray(points,dtype=np.longdouble)
    out=np.zeros(x.shape[:-1],dtype=np.longdouble)
    for (i,j,k),c in terms:
        out += np.longdouble(c)*x[...,0]**i*x[...,1]**j*x[...,2]**k
    return out

def anchors(uvt):
    u,v,t=map(float,uvt)
    sb=math.sqrt(max(0.0,1-u*u))
    z=(1+2*u*v*t-u*u-v*v-t*t)
    z=max(0.0,z)
    c2=(t-u*v)/sb
    return np.array([[1.,0.,0.],[u,sb,0.],[v,c2,math.sqrt(z)]])

def q_from_angles(x):
    th,ph=x
    return np.array([math.sin(th)*math.cos(ph),math.sin(th)*math.sin(ph),math.cos(th)])

def make_obj(uvt):
    A=anchors(uvt); a,b,c=A
    def val(x, hard=False):
        q=q_from_angles(x)
        dots=A@q
        if np.max(dots)>0.56:
            return 1e2+1e2*float(np.max(dots)-.56)
        pts=np.array([[uvt[0],float(a@q),float(b@q)], [uvt[1],float(a@q),float(c@q)], [uvt[2],float(b@q),float(c@q)]],dtype=np.longdouble)
        # Ordering of coordinates is irrelevant since R is symmetric; preserve exact pair labels.
        return float(R(pts).sum())
    return val

def feasible_random(A,rng,n=200000):
    z=rng.normal(size=(n,3)); z/=np.linalg.norm(z,axis=1)[:,None]
    ok=np.max(z@A.T,axis=1)<=.56
    return z[ok]

def run(uvt,seed):
    rng=np.random.default_rng(seed); A=anchors(uvt); obj=make_obj(uvt)
    # 50+ feasible starts, local constrained angle minimizations
    qs=feasible_random(A,rng,120000)
    starts=[]
    for q in qs[:max(60,min(len(qs),120))]:
        starts.append([math.acos(float(q[2])),math.atan2(float(q[1]),float(q[0]))%(2*math.pi)])
    best=(float('inf'),None,None)
    for x0 in starts:
        rr=minimize(obj,x0,method='Nelder-Mead',options={'maxiter':700,'xatol':1e-11,'fatol':1e-15})
        q=q_from_angles(rr.x); dots=A@q
        if np.max(dots)<=.560000001 and rr.fun<best[0]: best=(rr.fun,rr.x,dots)
    de=differential_evolution(obj,[(0,math.pi),(0,2*math.pi)],seed=seed,popsize=20,maxiter=40,tol=1e-10,polish=True,workers=1)
    q=q_from_angles(de.x); dots=A@q
    if np.max(dots)<=.560000001 and de.fun<best[0]: best=(de.fun,de.x,dots)
    return {'seed':seed,'feasible_starts':len(starts),'de_fun':float(de.fun),'best_3R':float(best[0]),'angles':None if best[1] is None else [float(x) for x in best[1]],'q_dots':None if best[2] is None else [float(x) for x in best[2]],'best_q':None if best[1] is None else q_from_angles(best[1]).tolist()}

def main():
    cases=[('first',(-.759220762336624,-.29211600772137486,.32931701954562287),2.10252384e-5),('batch2',(-.9932727408102706,-.5711472561258527,.4722521849123732),None)]
    out={'model_terms':len(terms),'count_check':{'fixed_T':1,'two_T_one_q':18,'one_T_or_zero_T':'not in strengthened sum','no_overlap_reason':'each triangle is identified by its intersection with fixed vertex set T; q is unique for each two-T triple'},'cases':[]}
    for name,uvt,r0 in cases:
        A=anchors(uvt); gram=float(1+2*np.prod(uvt)-np.dot(uvt,uvt)); rows=[]
        for seed in range(50,52):
            t=time.time(); row=run(uvt,seed); row['seconds']=time.time()-t; rows.append(row)
        out['cases'].append({'name':name,'uvt':list(uvt),'gram_det':gram,'R_T_reported':r0,'runs':rows})
    print(json.dumps(out,indent=2))
    (ROOT/'explore_fixed_triangle_q_min_v1.json').write_text(json.dumps(out,indent=2)+'\n')
if __name__=='__main__': main()
