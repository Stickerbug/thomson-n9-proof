"""Local contact/PSD diagnostics, no cutting-plane optimization; discovery only."""
import json,time
import numpy as np
import cvxpy as cp
from sharp_contact_refinement2026_core import *
from sharp_contact_refinement2026_refine import IndependentActual,section_search,solver_info
from sharp_boundary_actualf_v3 import validate,random_cond

def run():
    start=time.time();b=build();N=b['N'];indices=b['indices'];comp=b['comp'];rng=np.random.default_rng(2026101909)
    ref=b['sources']['psd_project_nonsharp_d10_contactjets_v1.json'][1]
    free=cp.Variable(b['augZ'].shape[1]);x=b['augsol']+b['augZ']@free;free.value=b['augZ'].T@(ref-b['augsol'])
    index={t:j for j,t in enumerate(indices)}
    B=[cp.bmat([[x[index[k,min(i,j),max(i,j)]] for j in range(n.shape[1])] for i in range(n.shape[1])]) for k,n in enumerate(N) if n.shape[1]]
    base=[v>>0 for v in B];local=[]
    for j,p in enumerate(b['cand']):
        H=cp.bmat([[(float(3*(2-2*p[i])**(-2.5)) if i==q else 0.)-derivative(comp,p[None],(i,q))[0]@x for q in range(3)] for i in range(3)])
        if b['interior'][j]:local.append(H>>0)
        else:
            g,Hg,T=gram_geometry(p);gr=b['fprime'][j]-b['Dr'][j]@x;lam=g@gr/(g@g);local.extend([lam>=0,T.T@H@T-lam*T.T@Hg@T>>0])
    out=ROOT/(PREFIX+'contact_psd.json');assert not out.exists()
    result={'warning':'DISCOVERY ONLY. These are separate local-contact PSD diagnostics; no cutting-plane rounds or global claims. Rational r is not exact root.','contact_rank':b['diagnostic']['contact_rank'],'contact_plus_tangent_rank':b['diagnostic']['contact_plus_tangent_rank'],'objective':'minimize Euclidean squared distance to original PSD-contact projection; no tau target or sample inequalities','settings':{'solver':'CLARABEL','tol_gap_abs':1e-11,'tol_gap_rel':1e-11,'tol_feas':1e-11,'max_iter':250,'time_limit':90},'N':[n.tolist() for n in N],'indices':[list(t) for t in indices],'history':[]}
    def save():out.write_text(json.dumps(result,indent=2)+chr(10))
    save()
    cases=[('original_PSD_projection',None),('augmented_contact_PSD',base),('augmented_contact_PSD_local_Hessian',base+local)]
    for name,constraints in cases:
        row={'case':name}
        if constraints is None:xx=ref;row['solver_precision']='Original data: no new optimization'
        else:
            prob=cp.Problem(cp.Minimize(cp.sum_squares(x-ref)),constraints);err=None
            try:prob.solve(**result['settings'])
            except cp.error.SolverError as e:err=repr(e)
            row['solver_error']=err
            if prob.solver_stats is not None:row['solver_precision']=solver_info(prob)
            if x.value is None:row['no_iterate']=True;result['history'].append(row);save();continue
            xx=np.asarray(x.value).ravel()
        BB,AA,cc=original(xx,N,indices);ev={k:np.linalg.eigvalsh(v).tolist() for k,v in BB.items()};gg,hh=jets(xx,comp,b['cand'])
        row.update({'x':xx.tolist(),'B':{k:v.tolist() for k,v in BB.items()},'A':[a.tolist() for a in AA],'c':cc,'F111':float(AA[0].sum()),'objective_B':float(12*cc-1.5*AA[0].sum()),'trace':float(sum(np.trace(v) for v in BB.values())),'block_eigenvalues':ev,'min_B_eigenvalue':float(min(min(v) for v in ev.values())),'contact_max_error':float(max(abs(b['Aeq']@xx-b['target']))),'boundary_tangent_max_error':float(max(abs(b['At']@xx-b['bt']))),'internal_Hessian_min_eigenvalue':float(np.linalg.eigvalsh(hh[b['interior']]).min()),'boundary_jets':[]})
        for j in np.flatnonzero(b['boundary']):
            g,Hg,T=gram_geometry(b['cand'][j]);lam=float(g@gg[j]/(g@g));row['boundary_jets'].append({'index':int(j),'lambda':lam,'tangent_gradient':(T.T@gg[j]).tolist(),'tangent_corrected_Hessian_eigenvalues':np.linalg.eigvalsh(T.T@(hh[j]-lam*Hg)@T).tolist()})
        actual=IndependentActual(AA,cc);val,_=validate(comp,xx,rng,case_index(name),DEGREE);sections=section_search(actual,rng);points=np.array([v['triangle'] for v in val['worst_points']+sections]+[KEY.tolist()]);vv=actual(points);k=int(np.argmin(vv))
        row['compiled_validation']=val;row['independent_sections']=sections[:12];row['key_point_R_actual']=float(actual(KEY)[0]);row['worst_point']={'triangle':points[k].tolist(),'R':float(vv[k]),'gram_determinant':float(1+2*np.prod(points[k])-points[k]@points[k])};row['independent_actual_min_R']=float(vv[k]);row['compiled_original_discrepancy']=float(np.max(abs(vv-comp.kernel(xx)(points))));row['distance_from_original_projection']=float(np.linalg.norm(xx-ref))
        result['history'].append(row)
        if row['min_B_eigenvalue']>=-1e-9 and ('best_PSD_case' not in result or row['independent_actual_min_R']>result['history'][result['best_PSD_case']]['independent_actual_min_R']):result['best_PSD_case']=len(result['history'])-1
        save();print('CONTACT_DIAGNOSTIC',json.dumps({k:v for k,v in row.items() if k not in ['x','B','A','block_eigenvalues','compiled_validation','independent_sections']}),flush=True)
    result['elapsed_seconds']=time.time()-start;save();print('DONE contact diagnostic seconds',result['elapsed_seconds'],flush=True)

def case_index(name):return {'original_PSD_projection':31,'augmented_contact_PSD':32,'augmented_contact_PSD_local_Hessian':33}[name]
if __name__=='__main__':run()
