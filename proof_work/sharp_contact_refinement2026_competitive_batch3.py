"""Third authorized finite batch: C plus kernel budget, positive PSD/Hessian margins.
All floating-point output is DISCOVERY ONLY, never an exact certificate.
"""
import json,time,itertools
import numpy as np
import mpmath as mp
import cvxpy as cp
from scipy.optimize import minimize,differential_evolution,NonlinearConstraint
from sharp_contact_refinement2026_core import ROOT,DEGREE,RSTRING,KEY,build,derivative,gram_geometry,original,jets
from sharp_contact_refinement2026_refine import IndependentActual,solver_info
from sharp_contact_refinement2026_kernel_domain import JointBudget
from sharp_contact_refinement2026_export import mpR
from sharp_boundary_actualf_v3 import random_cond,boundary_points
PREFIX='sharp_contact_refinement2026_batch3_'
VALLEY=np.array([-.759220762336624,-.29211600772137486,.32931701954562287])


def gram(p):
    p=np.atleast_2d(p);return 1+2*np.prod(p,axis=1)-np.sum(p*p,axis=1)


def clean(points,C):
    p=np.sort(np.atleast_2d(points),axis=1)
    keep=(np.max(p,axis=1)<=.56+2e-13)&(np.min(p,axis=1)>=-1-2e-13)&(gram(p)>=-2e-12)&(C(p)>=-1e-12)
    p=p[keep]
    _,ix=np.unique(np.round(p,12),axis=0,return_index=True)
    return p[np.sort(ix)]


def competitive_random(count,C,rng,boundary=False):
    out=[];n=0
    while n<count:
        p=(boundary_points if boundary else random_cond)(max(count-n,1000),rng);p=np.sort(p,axis=1);p=p[C(p)>=0]
        out.append(p);n+=len(p)
    return np.vstack(out)[:count]


def choose(pool,mandatory,residual,C,rng,limit=3500):
    mandatory=clean(mandatory,C);values=residual(pool);selected=[mandatory,pool[np.argsort(values)[:min(1400,len(pool))]]]
    # Preserve geometry and competitive-budget layers as well as the current low residuals.
    gg=gram(pool);cv=C(pool)
    cells=np.column_stack([np.digitize(gg,[1e-7,1e-3,.03,.2,.6]),np.digitize(cv,[1e-6,1e-3,.01,.025]),np.digitize(pool[:,0],[-.9,-.6,-.3,0,.3])])
    for cell in np.unique(cells,axis=0):
        ix=np.flatnonzero(np.all(cells==cell,axis=1));take=min(12,len(ix));selected.append(pool[rng.choice(ix,take,replace=False)])
    active=clean(np.vstack(selected),C)
    if len(active)>limit:active=active[:limit]
    if len(active)<limit:
        candidates=clean(np.vstack([active,pool[rng.permutation(len(pool))]]),C);active=candidates[:limit]
    return active


def independent_validation(comp,xx,AA,cc,C,pool,cand,rng,iteration):
    start=time.time();residual=comp.kernel(xx);actual=IndependentActual(AA,cc)
    randoms=competitive_random(10000,C,rng);boundary=competitive_random(1500,C,rng,True)
    scan=clean(np.vstack([pool,randoms,boundary,cand,KEY,VALLEY]),C);compiled=residual(scan)
    def cf(p,jac=False):
        u,v,t=p;cv,cg=C.C(p,True);kv,kg=C.K(p,True)
        if jac:return np.vstack([[2*(v*t-u),2*(u*t-v),2*(u*v-t)],cg[0],kg[0],[-1,1,0],[0,-1,1]])
        return np.array([gram(p)[0],cv[0],kv[0],v-u,t-v])
    def objective(p):
        val,g=residual(p,True);return float(val[0]),g[0]
    order=np.argsort(compiled);seeds=list(scan[order[:45]])+list(randoms[rng.choice(len(randoms),20,replace=False)])+list(cand)+[KEY,VALLEY]
    local=[]
    for seed in seeds:
        op=minimize(objective,seed,jac=True,method='SLSQP',bounds=[(-1,.56)]*3,constraints=[{'type':'ineq','fun':cf,'jac':lambda p:cf(p,True)}],options={'maxiter':160,'ftol':1e-13})
        if min(cf(op.x))>=-2e-10:local.append({'point':op.x.tolist(),'R_compiled':float(residual(op.x)[0]),'success':bool(op.success),'constraints':cf(op.x).tolist()})
    def vc(p):
        pp=np.asarray(p);single=pp.ndim==1;pp=pp[:,None] if single else pp;u,v,t=pp
        ans=np.vstack([1+2*u*v*t-u*u-v*v-t*t,C.C(pp.T),C.K(pp.T),v-u,t-v]);return ans[:,0] if single else ans
    def vo(p):
        pp=np.asarray(p);single=pp.ndim==1;pp=pp[None] if single else pp.T;v=residual(pp);return float(v[0]) if single else v
    de=differential_evolution(vo,[(-1,.56)]*3,constraints=(NonlinearConstraint(vc,0,np.inf),),seed=2026300900+iteration,popsize=24,maxiter=250,vectorized=True,updating='deferred',polish=False,tol=1e-9,x0=scan[order[0]])
    local.append({'point':de.x.tolist(),'R_compiled':float(residual(de.x)[0]),'success':bool(de.success),'constraints':cf(de.x).tolist(),'kind':'DE','message':str(de.message),'nit':int(de.nit),'nfev':int(de.nfev)})
    # Independently evaluate every one of the 10000 competitive random points in original A.
    audit=np.concatenate([actual(randoms[i:i+512]) for i in range(0,len(randoms),512)])
    candpoints=np.vstack([np.array([r['point'] for r in local]),scan[order[:30]],randoms[np.argmin(audit)]])
    av=actual(candpoints);ix=np.argsort(av);polished=[]
    def direct(p):
        v,g=actual(p,True);return float(v[0]),g[0]
    for j in ix[:5]:
        op=minimize(direct,candpoints[j],jac=True,method='SLSQP',bounds=[(-1,.56)]*3,constraints=[{'type':'ineq','fun':cf,'jac':lambda p:cf(p,True)}],options={'maxiter':100,'ftol':1e-14})
        if min(cf(op.x))>=-2e-10:polished.append(op.x)
    if polished:candpoints=np.vstack([candpoints,polished]);av=actual(candpoints)
    eligible=np.array([min(cf(p))>=-2e-10 for p in candpoints]);worst_idx=np.flatnonzero(eligible)[np.argmin(av[eligible])];worst=candpoints[worst_idx]
    strictseeds=randoms[(C(randoms)>.0001)&(gram(randoms)>.02)][:12];strict=[]
    for j in np.argsort(av)[:15]:
        p=candpoints[j]
        if min(cf(p))>0:strict.append(p);continue
        for target in strictseeds:
            found=False
            for delta in [1e-10,1e-8,1e-6,1e-4]:
                q=(1-delta)*p+delta*target
                if min(cf(q))>0:strict.append(q);found=True;break
            if found:break
    strict=np.array(strict);strictav=actual(strict);sp=strict[np.argmin(strictav)]
    found=clean(np.vstack([candpoints,scan[order[:80]]]),C)
    out={'warning':'NUMERICAL DISCOVERY ONLY','random_competitive_count_original_A':len(randoms),'boundary_competitive_count':len(boundary),'total_scan_count':len(scan),'scan_min_R_compiled':float(min(compiled)),'random_min_R_original_A':float(min(audit)),'random_worst_point':randoms[np.argmin(audit)].tolist(),'random_compiled_vs_original_max_error':float(max(abs(audit-residual(randoms)))),'local_seeds':len(seeds),'local_search':sorted(local,key=lambda row:row['R_compiled']),'DE':local[-1],'worst_numeric_tolerance':{'point':worst.tolist(),'R_actual':float(av[worst_idx]),'constraints':cf(worst).tolist()},'best_strict_feasible':{'point':sp.tolist(),'R_actual':float(min(strictav)),'constraints':cf(sp).tolist(),'C_decimal_80digit':C.C.exact_decimal_value(sp),'Ckernel_decimal_80digit':C.K.exact_decimal_value(sp),'Ckernel_exact_fraction':str(C.K.exact_fraction(sp)),'R_gram_decimal_80digit':mpR([a.tolist() for a in AA],cc,sp)},'direct_original_A_polishes':len(polished),'elapsed_seconds':time.time()-start}
    return out,found,randoms,boundary


def run():
    mp.mp.dps=80;start=time.time();b=build();N=b['N'];indices=b['indices'];comp=b['comp'];cand=b['cand'];rng=np.random.default_rng(2026300901)
    old=json.loads((ROOT/'sharp_contact_refinement2026_results.json').read_text());batch2=json.loads((ROOT/'sharp_contact_refinement2026_batch2_results.json').read_text());C=JointBudget();survivors=[np.array(row['validation']['best_strict_feasible']['point']) for row in batch2['history'] if C.K(row['validation']['best_strict_feasible']['point'])[0]>=0]
    ref=np.array(old['best_solution']['x']);oldpoints=np.array(old['training_points']);near=[]
    for center in [KEY,VALLEY,*survivors]:
        for scale in [1e-3,1e-2]:near.append(center+rng.normal(0,scale,(100,3)))
    mandatory=clean(np.vstack([cand,KEY,VALLEY,*survivors,*near]),C);pool=clean(np.vstack([oldpoints,np.array(batch2['training_points']),mandatory,competitive_random(10000,C,rng)]),C);active=choose(pool,mandatory,comp.kernel(ref),C,rng)
    sol=b['augsol'];Z=b['augZ'];free=cp.Variable(Z.shape[1]);x=sol+Z@free;free.value=Z.T@(ref-sol);index={t:j for j,t in enumerate(indices)}
    B={k:cp.bmat([[x[index[k,min(i,j),max(i,j)]] for j in range(n.shape[1])] for i in range(n.shape[1])]) for k,n in enumerate(N) if n.shape[1]};trace=sum(cp.trace(bb) for bb in B.values());cons=[bb>>1e-6*np.eye(bb.shape[0]) for bb in B.values()]+[trace<=2000]
    for j,p in enumerate(cand):
        H=cp.bmat([[(float(3*(2-2*p[i])**(-2.5)) if i==q else 0.)-derivative(comp,p[None],(i,q))[0]@x for q in range(3)] for i in range(3)])
        if b['interior'][j]:cons.append(H>>1e-6*np.eye(3))
        else:
            g,Hg,T=gram_geometry(p);grad=b['fprime'][j]-b['Dr'][j]@x;lam=g@grad/(g@g);cons.extend([lam>=0,T.T@H@T-lam*(T.T@Hg@T)>>0])
    taus=cp.Variable(nonneg=True);tau=1e-6*taus
    result={'warning':'DISCOVERY ONLY; rational approximate r is not exact root; no exact PSD/nonnegativity/global proof','scope':'Third explicitly authorized finite batch; true PSD first-batch seed; C and Ckernel; <=3500 cuts; max3 CLARABEL90s rounds','degree':DEGREE,'r_approximation':RSTRING,'contact_rank':b['diagnostic']['contact_rank'],'contact_plus_tangent_rank':b['diagnostic']['contact_plus_tangent_rank'],'diagnostic':b['diagnostic'],'objective':'tau+1e-9*trace, scaled by1e6','trace_penalty':1e-9,'trace_cap':2000,'PSD_margin':1e-6,'internal_Hessian_margin':1e-6,'active_limit':3500,'cut_competitive_tolerance':-1e-12,'source_seed':'first batch best_solution iteration2, minB+2.34436957e-6, trace660.66488464','settings':{'solver':'CLARABEL','tol_gap_abs':1e-10,'tol_gap_rel':1e-10,'tol_feas':1e-10,'max_iter':350,'time_limit':90,'warm_start':True},'initial_pool_count':len(pool),'initial_active_count':len(active),'source_old_training_count':len(oldpoints),'source_old_excluded_noncompetitive_count':int(np.sum(C(oldpoints)<-1e-10)),'N':[n.tolist() for n in N],'indices':[list(t) for t in indices],'history':[],'mandatory_points':mandatory.tolist()}
    out=ROOT/(PREFIX+'results.json');assert not out.exists()
    def save():out.write_text(json.dumps(result,indent=2)+chr(10))
    first_validation=json.loads((ROOT/'sharp_contact_refinement2026_competitive_validation.json').read_text());best_score=first_validation['best_strict_feasible']['R_actual'];stale_rounds=0
    save();print('BATCH3_BUILD',len(pool),len(active),'contactrank',result['contact_plus_tangent_rank'],'seconds',time.time()-start,flush=True)
    for iteration in range(3):
        assert len(active)<=3500 and np.min(C(active))>=-1.0001e-10
        D=comp.design(active);rhs=np.sum((2-2*active)**(-.5),axis=1)-old['energy_double']/12
        prob=cp.Problem(cp.Minimize(taus+.001*trace),cons+[D@x<=rhs+tau]);err=None;wall=time.time()
        try:prob.solve(**result['settings'])
        except cp.error.SolverError as ex:err=repr(ex)
        row={'iteration':iteration,'active_count':len(active),'pool_count':len(pool),'min_active_joint_budget':float(min(C(active))),'min_active_C':float(min(C.C(active))),'min_active_Ckernel':float(min(C.K(active))),'min_active_Gram':float(min(gram(active))),'solver_error':err,'solve_wall_seconds':time.time()-wall,'active_points':active.tolist()}
        if prob.solver_stats is not None:row['solver_precision']=solver_info(prob)
        if x.value is None:result['history'].append(row);result['stop_reason']='no iterate returned; no SCS fallback';save();break
        xx=np.asarray(x.value).ravel();bb,AA,cc=original(xx,N,indices);eigs={k:np.linalg.eigvalsh(v).tolist() for k,v in bb.items()};mineig=min(min(v) for v in eigs.values());gg,hh=jets(xx,comp,cand)
        row.update({'tau':None if tau.value is None else float(tau.value),'trace':float(sum(np.trace(v) for v in bb.values())),'min_B_eigenvalue':float(mineig),'min_original_A_eigenvalue':float(min(np.linalg.eigvalsh(a).min() for a in AA)),'block_eigenvalues':eigs,'contact_max_error':float(max(abs(b['Aeq']@xx-b['target']))),'boundary_tangent_max_error':float(max(abs(b['At']@xx-b['bt']))),'internal_Hessian_min_eigenvalue':float(np.linalg.eigvalsh(hh[b['interior']]).min()),'active_min_R_compiled':float(min(rhs-D@xx)),'boundary_jets':[]})
        for j in np.flatnonzero(b['boundary']):
            g,Hg,T=gram_geometry(cand[j]);lam=float(g@gg[j]/(g@g));row['boundary_jets'].append({'index':int(j),'lambda':lam,'tangent_gradient':(T.T@gg[j]).tolist(),'curvature_corrected_Hessian_eigenvalues':np.linalg.eigvalsh(T.T@(hh[j]-lam*Hg)@T).tolist()})
        solution={'iteration':iteration,'x':xx.tolist(),'N':[n.tolist() for n in N],'B':{k:v.tolist() for k,v in bb.items()},'A':[a.tolist() for a in AA],'c':cc,'F111':float(AA[0].sum()),'objective_B':float(12*cc-1.5*AA[0].sum()),'trace':row['trace'],'min_B_eigenvalue':float(mineig),'solver_precision':row.get('solver_precision')};row['solution']=solution;result['history'].append(row);result['solution']=solution;save()
        print('BATCH3_SOLVED',iteration,json.dumps({k:v for k,v in row.items() if k not in ['solution','active_points','boundary_jets','block_eigenvalues']}),flush=True)
        val,found,randoms,boundaries=independent_validation(comp,xx,AA,cc,C,pool,cand,rng,iteration);row['validation']=val;solution['independent_actual_min_R']=val['worst_numeric_tolerance']['R_actual'];solution['worst_point']=val['worst_numeric_tolerance'];actual=IndependentActual(AA,cc)
        original_values=np.concatenate([actual(oldpoints[i:i+512]) for i in range(0,len(oldpoints),512)]);oldC=C(oldpoints);mask=oldC>=-1e-12;ii=np.flatnonzero(mask)[np.argmin(original_values[mask])];bad=np.flatnonzero(~mask)[np.argmin(original_values[~mask])]
        row['full_previous_training_original_A_audit']={'count':len(oldpoints),'competitive_count':int(sum(mask)),'competitive_min_R':float(original_values[ii]),'competitive_worst_point':oldpoints[ii].tolist(),'noncompetitive_count':int(sum(~mask)),'noncompetitive_min_R_diagnostic_only':float(original_values[bad]),'noncompetitive_worst_point_diagnostic_only':oldpoints[bad].tolist()};row['key_R_actual']=float(actual(KEY)[0]);row['previous_valley_R_actual']=float(actual(VALLEY)[0])
        if mineig>=1e-9 and ('best_solution' not in result or solution['independent_actual_min_R']>result['best_solution']['independent_actual_min_R']):result['best_solution']=solution
        if 'best_unfiltered_solution' not in result or solution['independent_actual_min_R']>result['best_unfiltered_solution']['independent_actual_min_R']:result['best_unfiltered_solution']=solution
        row['elapsed_seconds']=time.time()-start;save();print('BATCH3_VALIDATED',iteration,'R',solution['independent_actual_min_R'],'strict',val['best_strict_feasible'],'seconds',time.time()-start,flush=True)
        if mineig>=1e-9 and solution['independent_actual_min_R']>-1e-7:result['stop_reason']='Observed positive PSD and independent strengthened-domain search thresholds attained; discovery only';save();break
        score=solution['independent_actual_min_R'] if mineig>=1e-9 else -float('inf')
        if score>best_score+1e-8:best_score=score;stale_rounds=0
        else:stale_rounds+=1
        row['consecutive_no_improvement']=stale_rounds;save()
        if stale_rounds>=2:result['stop_reason']='Two consecutive rounds without improvement over known PSD seed or best strengthened-domain residual';save();break
        near=[]
        low=found[np.argsort(comp.kernel(xx)(found))[:6]]
        for p in low:
            for scale in [1e-3,1e-2]:near.append(p+rng.normal(0,scale,(40,3)))
        mandatory=clean(np.vstack([cand,KEY,VALLEY,*survivors,low,*near]),C);pool=clean(np.vstack([pool,randoms,boundaries,found,*near]),C);active=choose(pool,mandatory,comp.kernel(xx),C,rng)
    result.setdefault('stop_reason','Third fixed finite batch exhausted; preserve all models and obstacles');result['final_pool_count']=len(pool);result['training_points']=pool.tolist();result['elapsed_seconds']=time.time()-start;save();print('BATCH3_FINAL',result['stop_reason'],'seconds',result['elapsed_seconds'],flush=True)

if __name__=='__main__':run()
