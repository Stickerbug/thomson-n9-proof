"""Bounded three-round CLARABEL sharp search; NUMERICAL DISCOVERY ONLY."""
import json,time,itertools,warnings
import numpy as np
import cvxpy as cp
from scipy.optimize import minimize,differential_evolution
from sharp_contact_refinement2026_core import *
from sharp_boundary_actualf_v3 import validate,random_cond,dedup,valid,LIMIT
from three_point_sampled import design

class IndependentActual:
    """Direct recurrence of original A; no compiled polynomial or h11."""
    def __init__(self,A,c):self.A=A;self.c=c
    def F(self,points,gradient=False):
        pts=np.atleast_2d(points);out=np.zeros(len(pts));grad=np.zeros((len(pts),3))
        for perm in itertools.permutations(range(3)):
            u,v,t=pts[:,perm].T;a=t-u*v;b=(1-u*u)*(1-v*v)
            da=np.column_stack([-v,-u,np.ones(len(pts))]);db=np.column_stack([-2*u*(1-v*v),-2*v*(1-u*u),np.zeros(len(pts))])
            Q=[np.ones(len(pts)),a];dQ=[np.zeros((len(pts),3)),da]
            for k in range(1,DEGREE):
                Q.append(2*a*Q[-1]-b*Q[-2]);dQ.append(2*da*Q[-2][:,None]+2*a[:,None]*dQ[-1]-db*Q[-3][:,None]-b[:,None]*dQ[-2])
            for k,A in enumerate(self.A):
                m=A.shape[0];pow=np.arange(m);U=u[:,None]**pow;V=v[:,None]**pow
                z=np.einsum('ni,ij,nj->n',U,A,V);out+=Q[k]*z/6
                if gradient:
                    du=(u[:,None]**np.maximum(0,pow-1))*pow;dv=(v[:,None]**np.maximum(0,pow-1))*pow
                    dz=np.column_stack([np.einsum('ni,ij,nj->n',du,A,V),np.einsum('ni,ij,nj->n',U,A,dv),np.zeros(len(pts))])
                    local=(dQ[k]*z[:,None]+Q[k][:,None]*dz)/6
                    for j,ax in enumerate(perm):grad[:,ax]+=local[:,j]
        return (out,grad) if gradient else out
    def __call__(self,points,gradient=False):
        pts=np.atleast_2d(points);out=np.sum((2-2*pts)**(-.5),axis=1)-self.c;gr=(2-2*pts)**(-1.5)
        if gradient:
            v,g=self.F(pts,True);out-=7*v;gr-=7*g
        else:out-=7*self.F(pts)
        for i in range(3):
            diag=np.column_stack([np.ones(len(pts)),pts[:,i],pts[:,i]])
            if gradient:
                v,g=self.F(diag,True);out-=v;gr[:,i]-=g[:,1]+g[:,2]
            else:out-=self.F(diag)
        return (out,gr) if gradient else out

def section_search(actual,rng):
    seeds=[KEY[:2],[-.75,.35],[-.5,-.5],[-.7,.01],[.24,.24],[.01,.35]]
    grid=np.array(list(itertools.product(np.linspace(-.98,.56,14),np.linspace(-.56,.56,14))))
    grid=grid[1+grid[:,0]-2*grid[:,1]**2>=0]
    pp=np.column_stack([grid[:,0],grid[:,1],grid[:,1]]);vv=actual(pp);seeds.extend(grid[np.argsort(vv)[:16]])
    seeds.extend(rng.uniform([-1,-.56],[.56,.56],(10,2)))
    def obj(v):
        val,g=actual([[v[0],v[1],v[1]]],True);return float(val[0]),np.array([g[0,0],g[0,1]+g[0,2]])
    rows=[]
    for seed in seeds:
        opt=minimize(obj,seed,jac=True,method='SLSQP',bounds=[(-1,LIMIT),(-1,LIMIT)],constraints=[{'type':'ineq','fun':lambda z:1+z[0]-2*z[1]**2,'jac':lambda z:np.array([1.,-4*z[1]])}],options={'maxiter':150,'ftol':2e-14})
        pp=np.array([opt.x[0],opt.x[1],opt.x[1]])
        if valid(pp)[0]:rows.append({'kind':'independent_v_equals_t_local','residual':float(actual(pp)[0]),'triangle':pp.tolist(),'gram_determinant':float(1+2*np.prod(pp)-pp@pp),'success':bool(opt.success)})
    return sorted(rows,key=lambda row:row['residual'])

def solver_info(prob):
    out={'cvxpy_status':prob.status,'objective':None if prob.value is None else float(prob.value),'num_iters':prob.solver_stats.num_iters,'solve_time':prob.solver_stats.solve_time}
    solver=prob._solver_cache.get('CLARABEL')
    if solver is not None:
        info=solver.get_info()
        for name in ['status','iterations','res_primal','res_dual','gap_abs','gap_rel','cost_primal','cost_dual','solve_time']:
            val=getattr(info,name,None)
            out[name]=str(val) if name=='status' else val
    return out

def run():
    start=time.time();b=build();N=b['N'];indices=b['indices'];comp=b['comp'];cand=b['cand'];rng=np.random.default_rng(2026101709)
    diagout=ROOT/(PREFIX+'diagnostics_refine.json');assert not diagout.exists();diagout.write_text(json.dumps(b['diagnostic'],indent=2)+chr(10))
    ref=b['sources']['psd_project_nonsharp_d10_contactjets_v1.json'][1]
    src=b['sources']['nonsharp_nullspace_actualf_d10_run2.json'][0]; old=b['sources']['sharp_boundary_actualf_d10_v3.json'][0]
    points0=np.vstack([np.array(src['training_points']),np.array(old['training_points'])])
    neighborhoods=np.vstack([KEY+rng.normal(0,s,(400,3)) for s in (1e-3,1e-2)])
    symnear=np.vstack([np.column_stack([KEY[0]+rng.normal(0,s,200),KEY[1]+rng.normal(0,s,200),np.zeros(200)]) for s in (1e-3,1e-2)])
    symnear[:,2]=symnear[:,1]
    points=dedup(np.vstack([points0,neighborhoods,symnear,KEY,cand]))
    sol=b['augsol'];Z=b['augZ'];free=cp.Variable(Z.shape[1]);x=sol+Z@free;free.value=Z.T@(ref-sol)
    index={t:j for j,t in enumerate(indices)}
    B={k:cp.bmat([[x[index[k,min(i,j),max(i,j)]] for j in range(n.shape[1])] for i in range(n.shape[1])]) for k,n in enumerate(N) if n.shape[1]}
    trace=sum(cp.trace(bb) for bb in B.values());constraints=[bb>>0 for bb in B.values()]+[trace<=10000]
    HH={}
    for j,p in enumerate(cand):
        H=cp.bmat([[(float(3*(2-2*p[i])**(-2.5)) if i==q else 0.)-derivative(comp,p[None],(i,q))[0]@x for q in range(3)] for i in range(3)])
        HH[j]=H
        if b['interior'][j]:constraints.append(H>>0)
        else:
            gg,Hg,T=gram_geometry(p);grad=b['fprime'][j]-b['Dr'][j]@x;lam=gg@grad/(gg@gg)
            constraints.extend([lam>=0,T.T@H@T-lam*(T.T@Hg@T)>>0])
    # Scale the objective into order one at the desired 1e-7 residual;
    # no trace penalty competes with sharp feasibility.
    tau_scaled=cp.Variable(nonneg=True);tau=1e-6*tau_scaled
    result={'warning':'NUMERICAL DISCOVERY ONLY; NOT global proof, NOT SDP infeasibility proof. Rational approximate r is not exact candidate root.','degree':DEGREE,'r_approximation':RSTRING,'energy_double':ENERGY,'domain':'Gram PSD intersect [-1,.56]^3; independent pair-exclusion prerequisite','unknowns':len(indices),'contact_equations':len(b['target']),'contact_rank':b['diagnostic']['contact_rank'],'contact_plus_boundary_tangent_rank':b['diagnostic']['contact_plus_tangent_rank'],'trace_cap':10000,'trace_penalty':0,'objective':'minimize tau/1e-6','Hessian_constraints':'9 internal 3x3 Hess_R PSD, 3 boundary lambda>=0 and 2x2 tangent Hess(R-lambda*g) PSD','nullspace_bases':[n.tolist() for n in N],'indices':[list(t) for t in indices],'source_training_counts':{'nonsharp':len(src['training_points']),'sharp':len(old['training_points']),'union_before_key_neighbors':len(dedup(points0))},'initial_training_count':len(points),'key_point':KEY.tolist(),'diagnostic':b['diagnostic'],'settings':{'solver':'CLARABEL','tol_gap_abs':1e-10,'tol_gap_rel':1e-10,'tol_feas':1e-10,'max_iter':350,'time_limit':90,'warm_start':True},'history':[],'training_points':points.tolist()}
    out=ROOT/(PREFIX+'results.json');assert not out.exists()
    def save():out.write_text(json.dumps(result,indent=2)+chr(10))
    save();print('BUILD',len(points),'contactrank',result['contact_rank'],'augmentedrank',result['contact_plus_boundary_tangent_rank'],'seconds',time.time()-start,flush=True)
    for iteration in range(3):
        D=comp.design(points);rhs=np.sum((2-2*points)**(-.5),axis=1)-ENERGY/12
        problem=cp.Problem(cp.Minimize(tau_scaled),constraints+[D@x<=rhs+tau]);error=None;solve_start=time.time()
        try:problem.solve(**result['settings'])
        except cp.error.SolverError as ex:error=repr(ex)
        row={'iteration':iteration,'training_count':len(points),'solver_error':error,'solve_wall_seconds':time.time()-solve_start}
        if problem.solver_stats is not None:row['solver_precision']=solver_info(problem)
        if x.value is None:
            row['no_iterate_returned']=True;result['history'].append(row);result['stop_reason']='CLARABEL returned no iterate; no SCS fallback';save();break
        xx=np.asarray(x.value).ravel();bb,AA,cc=original(xx,N,indices);ev={k:np.linalg.eigvalsh(v).tolist() for k,v in bb.items()};mineig=min(min(v) for v in ev.values())
        row.update({'tau':None if tau.value is None else float(tau.value),'trace':float(sum(np.trace(v) for v in bb.values())),'min_B_eigenvalue':float(mineig),'block_eigenvalues':ev,'min_original_A_eigenvalue':float(min(np.linalg.eigvalsh(a).min() for a in AA)),'contact_max_error':float(max(abs(b['Aeq']@xx-b['target']))),'boundary_tangent_max_error':float(max(abs(b['At']@xx-b['bt']))),'training_min_R':float(min(rhs-D@xx))})
        gg,hh=jets(xx,comp,cand);row['interior_H_min_eigenvalue']=float(np.linalg.eigvalsh(hh[b['interior']]).min());row['boundary_jets']=[]
        for j in np.flatnonzero(b['boundary']):
            g,Hg,T=gram_geometry(cand[j]);lam=float(g@gg[j]/(g@g));row['boundary_jets'].append({'index':int(j),'lambda':lam,'tangent_gradient':(T.T@gg[j]).tolist(),'tangent_H_eigenvalues':np.linalg.eigvalsh(T.T@(hh[j]-lam*Hg)@T).tolist()})
        print('SOLVED',json.dumps({k:v for k,v in row.items() if k not in ['block_eigenvalues','boundary_jets']}),flush=True)
        val,additions=validate(comp,xx,rng,iteration,DEGREE);row['compiled_search']=val
        actual=IndependentActual(AA,cc);sections=section_search(actual,rng);row['independent_v_equals_t']=sections[:16]
        found=val['worst_points']+sections
        check=np.array([d['triangle'] for d in found]+[KEY.tolist()]);actualvals=actual(check);compiledvals=comp.kernel(xx)(check)
        row['independent_original_A_discrepancy']=float(max(abs(actualvals-compiledvals)))
        k=int(np.argmin(actualvals));row['independent_actual_min_R']=float(actualvals[k]);row['worst_point']={'triangle':check[k].tolist(),'R':float(actualvals[k]),'gram_determinant':float(1+2*np.prod(check[k])-check[k]@check[k])};row['key_point_R_actual']=float(actual(KEY)[0])
        cross=random_cond(160,rng);row['independent_design_crosscheck']=float(np.max(abs(actual(cross)-(np.sum((2-2*cross)**(-.5),axis=1)-cc-sum(np.einsum('nij,ij->n',m,a) for m,a in zip(design(cross,DEGREE),AA))))))
        row['elapsed_seconds']=time.time()-start;solution={'iteration':iteration,'x':xx.tolist(),'N':[n.tolist() for n in N],'B':{k:v.tolist() for k,v in bb.items()},'A':[a.tolist() for a in AA],'c':cc,'F111':float(AA[0].sum()),'objective_B':float(12*cc-1.5*AA[0].sum()),'min_B_eigenvalue':float(mineig),'trace':row['trace'],'independent_actual_min_R':row['independent_actual_min_R'],'worst_point':row['worst_point'],'solver_precision':row.get('solver_precision')}
        row['solution']=solution;result['history'].append(row);result['solution']=solution;result['training_points']=points.tolist()
        if mineig>=-1e-9 and ('best_solution' not in result or row['independent_actual_min_R']>result['best_solution']['independent_actual_min_R']):result['best_solution']=solution
        if 'best_unfiltered_solution' not in result or row['independent_actual_min_R']>result['best_unfiltered_solution']['independent_actual_min_R']:result['best_unfiltered_solution']=solution
        save();print('VALIDATED',iteration,'minR',row['independent_actual_min_R'],'worst',row['worst_point'],'seconds',time.time()-start,flush=True)
        if mineig>=-1e-9 and row['independent_actual_min_R']>-1e-7:result['stop_reason']='Observed goals attained; still discovery only';save();break
        secpoints=np.array([d['triangle'] for d in sections[:12]])
        local=[]
        for p in check[np.argsort(actualvals)[:4]]:
            for scale in (1e-3,1e-2):local.append(p+rng.normal(0,scale,(50,3)))
        points=dedup(np.vstack([points,additions,secpoints,*local]))
    result.setdefault('stop_reason','Fixed three-round budget exhausted; preserve data and diagnose without repeating')
    result['elapsed_seconds']=time.time()-start;save();print('FINAL',result['stop_reason'],'seconds',result['elapsed_seconds'],flush=True)
if __name__=='__main__':run()
