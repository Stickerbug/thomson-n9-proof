"""Finite two-external-point W discovery, <=30 seconds per fixed T; no SDP."""
import json,time,hashlib,itertools
from fractions import Fraction as F
from pathlib import Path
import numpy as np
import mpmath as mp
from scipy.optimize import minimize,differential_evolution,NonlinearConstraint
ROOT=Path(__file__).parent;PREFIX='external_pair_field2026_'
class Deadline(Exception):pass
class Residual:
    def __init__(self,model):
        self.terms=model['residual_monomial'];self.ex=np.array([e for e,c in self.terms],dtype=int);self.co=np.array([float(F(c))for e,c in self.terms]);self.m=int(self.ex.max())
    def __call__(self,p,grad=False,dtype=float):
        p=np.atleast_2d(p).astype(dtype);out=[];gs=[];co=self.co if dtype==float else np.array([dtype(F(c).numerator)/dtype(F(c).denominator)for e,c in self.terms])
        for i in range(0,len(p),512):
            q=p[i:i+512];pw=[]
            for a in range(3):
                z=np.ones((len(q),self.m+1),dtype=dtype)
                for j in range(1,self.m+1):z[:,j]=z[:,j-1]*q[:,a]
                pw.append(z)
            mon=np.prod(np.stack([pw[a][:,self.ex[:,a]] for a in range(3)]),axis=0);out.append(mon@co)
            if grad:
                gg=[]
                for a in range(3):
                    z=np.prod(np.stack([pw[b][:,np.maximum(self.ex[:,b]-(a==b),0)]for b in range(3)]),axis=0);gg.append(z@(co*self.ex[:,a]))
                gs.append(np.stack(gg,axis=1))
        return (np.concatenate(out),np.concatenate(gs)) if grad else np.concatenate(out)

def qs(x):
    x=np.asarray(x);a,b=x[...,0],x[...,1];return np.stack([np.sin(a)*np.cos(b),np.sin(a)*np.sin(b),np.cos(a)],axis=-1)
def angles(q):return np.array([np.arccos(np.clip(q[2],-1,1)),np.arctan2(q[1],q[0])%(2*np.pi)])
def tangent(x):
    a,b=x;return np.array([[np.cos(a)*np.cos(b),-np.sin(a)*np.sin(b)],[np.cos(a)*np.sin(b),np.sin(a)*np.cos(b)],[-np.sin(a),0.]])

def work(row,R,model):
    case_budget={'T2':8.0,'T3':30.0}[row['name']];prior_seconds=20.86400008201599 if row['name']=='T2' else 0.0
    start=time.monotonic();end=start+case_budget-.5;algorithm_end=end-3;coords=row['triangle_decimal'];u,v,t=map(float,coords);g=1+2*u*v*t-u*u-v*v-t*t;A=np.array([[1.,0,0],[u,np.sqrt(1-u*u),0],[v,(t-u*v)/np.sqrt(1-u*u),np.sqrt(g)/np.sqrt(1-u*u)]]);edges=np.array([u,v,t]);pairs=[(0,1),(0,2),(1,2)];budget=F(row['budget_exact']);threshold=float(budget)/15;history=[];best=None;cache={};rng=np.random.default_rng(2026111300+(row['name']=='T3'))
    def clock():
        if time.monotonic()>algorithm_end:raise Deadline()
    def calc(x):
        nonlocal best
        clock();x=np.asarray(x);key=x.tobytes()
        if cache.get('key')==key:return cache['value']
        q,r=qs(x[:2]),qs(x[2:]);Jq,Jr=tangent(x[:2]),tangent(x[2:]);dq,dr=A@q,A@r;s=q@r;Dq,Dr=A@Jq,A@Jr;dsq=q*0+0
        triples=np.vstack([[[edges[k],dq[a],dq[b]]for k,(a,b)in enumerate(pairs)],[[edges[k],dr[a],dr[b]]for k,(a,b)in enumerate(pairs)],np.column_stack([dq,dr,np.repeat(s,3)])]);values,grad=R(triples,True);W=(sum(values[:6])/5+sum(values[6:]));G=np.zeros(4)
        for k,(a,b)in enumerate(pairs):G[:2]+=(grad[k,1]*Dq[a]+grad[k,2]*Dq[b])/5;G[2:]+=(grad[k+3,1]*Dr[a]+grad[k+3,2]*Dr[b])/5
        G[:2]+=grad[6:,0]@Dq+sum(grad[6:,2])*(r@Jq);G[2:]+=grad[6:,1]@Dr+sum(grad[6:,2])*(q@Jr)
        cons=np.r_[.56-dq,.56-dr,.56-s];C=np.zeros((7,4));C[:3,:2]=-Dq;C[3:6,2:]=-Dr;C[6,:2]=-r@Jq;C[6,2:]=-q@Jr
        val=(float(W),G,cons,C,values,q,r,triples)
        if not cache.get('freeze_best') and min(cons)>=-1e-12 and(best is None or W<best['W']):best={'W':float(W),'angles':x.tolist(),'q':q.tolist(),'r':r.tolist(),'phi_q':float(sum(values[:3])),'phi_r':float(sum(values[3:6])),'psi':float(sum(values[6:])),'min_pair_separation_slack':float(min(cons)),'constraints':cons.tolist(),'residual_terms':values.tolist()}
        cache.update(key=key,value=val);return val
    Q=np.array([w['q']for w in row['wells']]);Q/=np.linalg.norm(Q,axis=1)[:,None];pool=[]
    for q,r in itertools.combinations(Q,2):
        if max(np.r_[A@q,A@r,q@r])<=.56:pool.append(np.r_[angles(q),angles(r)])
    p=rng.normal(size=(1800,2,3));p/=np.linalg.norm(p,axis=2)[:,:,None]
    for q,r in p:
        if max(np.r_[A@q,A@r,q@r])<.56:pool.append(np.r_[angles(q),angles(r)])
    initial=[]
    for x in pool:
        try:initial.append((calc(x)[0],x))
        except Deadline:break
    initial.sort(key=lambda z:z[0]);scan_best=dict(best)if best else None;starts=[]
    for value,x in initial:
        qr=np.r_[qs(x[:2]),qs(x[2:])]
        if not starts or min(min(np.linalg.norm(qr-s),np.linalg.norm(np.r_[qr[3:],qr[:3]]-s))for s in starts)>.1:starts.append(qr)
        if len(starts)>=10:break
    for j,qr in enumerate(starts):
        if time.monotonic()>start+18:break
        x=np.r_[angles(qr[:3]),angles(qr[3:])];before=time.monotonic()
        try:
            op=minimize(lambda z:(1e5*calc(z)[0],1e5*calc(z)[1]),x,jac=True,method='SLSQP',bounds=[(0,np.pi),(0,2*np.pi)]*2,constraints=[{'type':'ineq','fun':lambda z:calc(z)[2],'jac':lambda z:calc(z)[3]}],callback=lambda z:clock(),options={'maxiter':160,'ftol':1e-11});value=calc(op.x);history.append({'kind':'SLSQP','start':j,'W':value[0],'success':bool(op.success),'message':str(op.message),'min_constraint':float(min(value[2])),'seconds':time.monotonic()-before})
        except Deadline:break
    if len(initial)>=40 and time.monotonic()<algorithm_end-2:
        population=np.array([x for _,x in initial[:20]]+[initial[int(i)][1]for i in rng.choice(len(initial),40,replace=False)]);before=time.monotonic()
        try:
            op=differential_evolution(lambda z:1e5*calc(z)[0],[(0,np.pi),(0,2*np.pi)]*2,constraints=(NonlinearConstraint(lambda z:calc(z)[2],0,np.inf),),init=population,maxiter=80,popsize=15,seed=2026111333+(row['name']=='T3'),polish=False,updating='deferred',tol=1e-8,callback=lambda x,convergence:time.monotonic()>algorithm_end-.5);value=calc(op.x);history.append({'kind':'DE','W':value[0],'success':bool(op.success),'nit':int(op.nit),'min_constraint':float(min(value[2])),'seconds':time.monotonic()-before})
        except Deadline:pass
    cache['freeze_best']=True
    # Validate the saved feasible candidate independently with longdouble monomials.
    q=np.array(best['q']);r=np.array(best['r']);dq=A@q;dr=A@r;s=q@r;tri=np.vstack([[[edges[k],dq[a],dq[b]]for k,(a,b)in enumerate(pairs)],[[edges[k],dr[a],dr[b]]for k,(a,b)in enumerate(pairs)],np.column_stack([dq,dr,np.repeat(s,3)])]);rv=R(tri,dtype=np.longdouble);Wld=(sum(rv[:6])/5+sum(rv[6:]));best['W_longdouble']=float(Wld);best['float_vs_longdouble_abs_error']=float(abs(Wld-best['W']));best['threshold_K_over_15']=threshold;best['gap_W_minus_K_over_15']=float(Wld-threshold);best['ratio_W_to_threshold']=float(Wld/threshold);best['15W_minus_K']=float(15*Wld-float(budget))
    # Numerical Jacobian check at the witness, not an extra minimization.
    if time.monotonic()<algorithm_end-.1:
        x=np.array(best['angles']);analytic=calc(x)[1];h=1e-6;fd=np.array([(calc(x+np.eye(4)[j]*h)[0]-calc(x-np.eye(4)[j]*h)[0])/(2*h)for j in range(4)]);best['analytic_vs_finite_difference_gradient_max_error']=float(max(abs(analytic-fd)))
    rec={'name':row['name'],'triangle_decimal':coords,'anchors_float':A.tolist(),'K_exact':str(budget),'K_display':float(budget),'threshold_K_over_15':threshold,'geometrically_feasible_initial_pairs':len(initial),'initial_scan_best':scan_best,'best':best,'optimization_history':history,'seconds':time.monotonic()-start,'prior_failed_attempt_seconds_upper':prior_seconds,'cumulative_case_seconds_upper':prior_seconds+time.monotonic()-start,'current_case_budget':case_budget,'deadline_seconds':30,'uniform_bound_numerically_refuted':best['W_longdouble']<threshold,'recommendation':'Uniform W>=K/15 has a feasible numerical counter-witness; do not spend effort certifying that false-looking uniform inequality. Retain spatial potentials/cap capacities or optimize a coupled six-point relaxation.'if best['W_longdouble']<threshold else'No counter-witness found in the finite search; this is not a lower bound. Additional analysis required before deciding certification.'};print('RESULT',json.dumps(rec),flush=True);return rec

def main():
    start=time.monotonic();modelpath=ROOT/'nonsharp_d10_root25_7599205_v10.json';model=json.loads(modelpath.read_text());R=Residual(model);probe=ROOT/'two_other_valleys2026_probe.json';rows=json.loads(probe.read_text())['results'];result={'status':'finite_numerical_strategy_probe_only','warning':'Each feasible W value is an upper bound on inf W; no certified lower bound or Thomson counterexample. No SDP.','model':str(modelpath),'model_sha256':hashlib.sha256(modelpath.read_bytes()).hexdigest(),'triangle_source':str(probe),'triangle_source_sha256':hashlib.sha256(probe.read_bytes()).hexdigest(),'residual_terms':len(R.terms),'normalization':'W=(phi(q)+phi(r))/5+psi(q,r); sum15W=sum6phi+sum45R; eta20>=0 dropped; necessary external budget K.','dual_capacity_identity':'If W>=beta+(alpha(q)+alpha(r))/5 for every allowed pair and sum6alpha>=L_alpha by a separate capacity proof, then sum15W>=15beta+L_alpha. Exclude if 15beta+L_alpha>K.','rows':[],'no_SDP':True}
    for row in rows:
        result['rows'].append(work(row,R,model));out=ROOT/(PREFIX+'data.json');out.write_text(json.dumps(result,indent=2)+'\n')
    result['seconds']=time.monotonic()-start;out.write_text(json.dumps(result,indent=2)+'\n');print('SAVED',out,'seconds',result['seconds'],flush=True)
if __name__=='__main__':main()
