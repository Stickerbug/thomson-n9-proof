"""Bounded negative-valley discovery for FIRST PSD seed only; no SDP, no proof."""
import json,time,hashlib
from pathlib import Path
import numpy as np
from scipy.optimize import minimize,differential_evolution,NonlinearConstraint
from scipy.spatial import cKDTree
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components
from sharp_contact_refinement2026_refine import IndependentActual
from sharp_contact_refinement2026_kernel_domain import KernelBudget
from sharp_contact_refinement2026_competitive import Competitive
from sharp_boundary_actualf_v3 import random_cond,boundary_points
ROOT=Path(__file__).parent;PREFIX='negative_valley_seed1_2026_';LIMIT=np.nextafter(.56,-np.inf)

class Deadline(Exception):pass
class FastBudget(KernelBudget):
    def __call__(self,points,grad=False):
        points=np.atleast_2d(points);values=[];grads=[]
        for start in range(0,len(points),512):
            p=np.asarray(points[start:start+512],dtype=np.longdouble);pw=[]
            for axis in range(3):
                a=np.ones((len(p),self.maxdegree+1),dtype=np.longdouble)
                for j in range(1,self.maxdegree+1):a[:,j]=a[:,j-1]*p[:,axis]
                pw.append(a)
            mon=np.ones((len(p),len(self.powers)),dtype=np.longdouble)
            for axis in range(3):mon*=pw[axis][:,self.powers[:,axis]]
            values.append(np.asarray(self.constant-mon@self.coefficients,dtype=float))
            if grad:
                gg=[]
                for axis in range(3):
                    m=np.ones_like(mon)
                    for j in range(3):m*=pw[j][:,np.maximum(0,self.powers[:,j]-(j==axis))]
                    gg.append(np.asarray(-m@(self.coefficients*self.powers[:,axis]),dtype=float))
                grads.append(np.column_stack(gg))
        return (np.concatenate(values),np.vstack(grads)) if grad else np.concatenate(values)

def gram(p):p=np.atleast_2d(p);return 1+2*np.prod(p,axis=1)-np.sum(p*p,axis=1)
def unique(p):
    p=np.sort(np.atleast_2d(p),axis=1);mask=(p[:,0]>=-1)&(p[:,-1]<.56)&(gram(p)>=0);p=p[mask];_,ix=np.unique(np.round(p,12),axis=0,return_index=True);return p[np.sort(ix)]
def components(p,eps):
    if not len(p):return np.array([],dtype=int),0
    pairs=cKDTree(p).query_pairs(eps,output_type='ndarray');n=len(p)
    rr=np.r_[np.arange(n),pairs[:,0],pairs[:,1]];cc=np.r_[np.arange(n),pairs[:,1],pairs[:,0]];graph=coo_matrix((np.ones(len(rr)),(rr,cc)),shape=(n,n)).tocsr();ncomp,label=connected_components(graph,directed=False);return label,ncomp

def run():
    start=time.monotonic();end=start+174;rng=np.random.default_rng(2026111212);out=ROOT/(PREFIX+'data.json');assert not out.exists();oldpath=ROOT/'sharp_contact_refinement2026_results.json';old=json.loads(oldpath.read_text());seed=old['best_solution'];assert seed['iteration']==2 and seed['min_B_eigenvalue']>0
    actual=IndependentActual([np.array(a) for a in seed['A']],seed['c']);K=FastBudget();Cold=Competitive(json.loads((ROOT/'competitive_triple_constraint_certificate.json').read_text()));history=[];traces=[]
    packet={'warning':'DISCOVERY ONLY. Negative samples and coarse extents are not complete covers or proof. First PSD seed only; no batch2/3 kernel and no SDP.','model':{'file':str(oldpath),'sha256':hashlib.sha256(oldpath.read_bytes()).hexdigest(),'key':'best_solution','iteration':2,'c':seed['c'],'trace':seed['trace'],'min_B_eigenvalue':seed['min_B_eigenvalue'],'true_root_correction':'Not applied; parent reports order1e-11, irrelevant only for numerical discovery.'},'domain':'sorted -1<=u<=v<=t<.56; Gram>=0; Ckernel>=0. Old C is annotated, not imposed.','budget_seconds':180,'internal_deadline_seconds':174,'optimization_seed_limit':12,'optimizations':history,'threshold_primary':-1e-9,'rng_seed':2026111212}
    def save():out.write_text(json.dumps(packet,indent=2)+'\n')
    def check():
        if time.monotonic()>end:raise Deadline()
    def eval_actual(p,gradient=False):check();return actual(p,gradient)
    def constraints(p,jac=False):
        check();u,v,t=p;kv,kg=K(p,True)
        if jac:return np.vstack([[2*(v*t-u),2*(u*t-v),2*(u*v-t)],kg[0],[-1,1,0],[0,-1,1]])
        return np.array([gram(p)[0],kv[0],v-u,t-v])
    def objective(p):
        v,g=eval_actual(p,True);return float(v[0]),g[0]
    pools=[np.array(old['training_points'])];sources=[str(oldpath)]
    for name in ['sharp_contact_refinement2026_batch2_results.json','sharp_contact_refinement2026_batch3_results.json']:
        d=json.loads((ROOT/name).read_text());sources.append(str(ROOT/name))
        if 'training_points' in d:pools.append(np.array(d['training_points']))
        for row in d['history']:
            if 'active_points'in row:pools.append(np.array(row['active_points']))
            if 'validation'in row:pools.append(np.array([row['validation']['best_strict_feasible']['point']]))
    pools.extend([random_cond(7000,rng),boundary_points(2500,rng)])
    z=rng.uniform(-1,.56,(4000,2));pools.append(np.column_stack([z[:,0],z[:,1],z[:,1]]));known=np.array([-.759220762336624,-.29211600772137486,.32931701954562287]);pools.append(known[None]);pools.extend(known+rng.normal(0,s,(1000,3)) for s in [.003,.01,.03])
    p=unique(np.vstack(pools));all_count=len(p);keep=[]
    for i in range(0,len(p),2048):check();keep.append(K(p[i:i+2048])>=0)
    p=p[np.concatenate(keep)];values=[]
    for i in range(0,len(p),1024):values.append(eval_actual(p[i:i+1024]))
    values=np.concatenate(values);packet.update({'pool_sources':sources,'geometric_pool_count':all_count,'kernel_budget_pool_count':len(p),'pool_scan_seconds':time.monotonic()-start,'pool_negative_count_R_lt_minus1e9':int(sum(values<-1e-9)),'pool_min_R':float(min(values))});save();print('POOL',packet['geometric_pool_count'],len(p),packet['pool_negative_count_R_lt_minus1e9'],'min',min(values),'seconds',packet['pool_scan_seconds'],flush=True)
    candidate_points=[p];candidate_values=[values];neg=p[values<-1e-9];nv=values[values<-1e-9];lab,n=components(neg,.035);local_seeds=[]
    groups=sorted([np.flatnonzero(lab==j) for j in range(n)],key=lambda ix:min(nv[ix]))
    for ix in groups:
        point=neg[ix[np.argmin(nv[ix])]]
        if not local_seeds or min(np.linalg.norm(point-q) for q in local_seeds)>.005:local_seeds.append(point)
    # Max twelve independent starts: up to eight local and four vectorized DE regions.
    for point in neg[np.argsort(nv)]:
        if len(local_seeds)>=8:break
        if not local_seeds or min(np.linalg.norm(point-q) for q in local_seeds)>.012:local_seeds.append(point)
    for j,point in enumerate(local_seeds[:8]):
        if time.monotonic()>start+115:break
        before=time.monotonic();path=[]
        def callback(x):
            check()
            if min(constraints(x))>=0:path.append(np.array(x).tolist())
        try:
            op=minimize(objective,point,jac=True,method='SLSQP',bounds=[(-1,LIMIT)]*3,constraints=[{'type':'ineq','fun':constraints,'jac':lambda x:constraints(x,True)}],callback=callback,options={'maxiter':120,'ftol':2e-13});history.append({'kind':'SLSQP','seed_number':j,'initial_point':point.tolist(),'point':op.x.tolist(),'R':float(actual(op.x)[0]),'success':bool(op.success),'message':str(op.message),'constraints':constraints(op.x).tolist(),'seconds':time.monotonic()-before});traces.extend(path);candidate_points.append(op.x[None]);candidate_values.append(actual(op.x))
        except Deadline:packet['deadline_during_local']=True;break
        save()
    regions=[(-1,LIMIT),(-1,-.6),(-.6,-.2),(-.2,LIMIT)]
    for j,region in enumerate(regions):
        if len(history)>=12 or time.monotonic()>start+145:break
        eligible=p[(p[:,0]>=region[0])&(p[:,0]<=region[1])]
        if len(eligible)<36:continue
        initial=eligible[rng.choice(len(eligible),36,replace=False)];eligible_values=actual(eligible);initial[:min(8,len(initial))]=eligible[np.argsort(eligible_values)[:8]];before=time.monotonic()
        def vc(x):
            check();x=np.asarray(x);single=x.ndim==1;x=x[:,None] if single else x;u,v,t=x;ans=np.vstack([1+2*u*v*t-u*u-v*v-t*t,K(x.T),v-u,t-v]);return ans[:,0] if single else ans
        def vo(x):
            x=np.asarray(x);return float(eval_actual(x)[0]) if x.ndim==1 else eval_actual(x.T)
        def cb(x,convergence):return time.monotonic()>min(end-15,before+11)
        try:
            op=differential_evolution(vo,[region,(-1,LIMIT),(-1,LIMIT)],constraints=(NonlinearConstraint(vc,0,np.inf),),init=initial,seed=2026111220+j,maxiter=100,popsize=12,vectorized=True,updating='deferred',polish=False,tol=1e-9,callback=cb);history.append({'kind':'DE','seed_number':2026111220+j,'u_region':list(region),'point':op.x.tolist(),'R':float(actual(op.x)[0]),'constraints':constraints(op.x).tolist(),'success':bool(op.success),'nit':int(op.nit),'seconds':time.monotonic()-before});candidate_points.append(op.x[None]);candidate_values.append(actual(op.x))
        except Deadline:packet['deadline_during_DE']=True;break
        save()
    # Rough local extent by rays, plus every inherited negative sample. These are not covers.
    raypoints=[]
    current=np.vstack(candidate_points);v=np.concatenate(candidate_values);neg=current[v<-1e-9];nv=v[v<-1e-9];lab,n=components(neg,.035)
    for ix in sorted([np.flatnonzero(lab==j) for j in range(n)],key=lambda ix:min(nv[ix]))[:12]:
        center=neg[ix[np.argmin(nv[ix])]]
        for axis in range(3):
            for sign in [-1,1]:
                q=np.repeat(center[None],42,axis=0);q[:,axis]+=sign*np.geomspace(1e-6,.15,42);q=unique(q)
                if len(q):raypoints.append(q)
    if raypoints and time.monotonic()<end-4:
        ray=unique(np.vstack(raypoints));ray=ray[K(ray)>=0];rv=actual(ray);candidate_points.append(ray);candidate_values.append(rv)
    if traces:
        path=unique(np.array(traces));path=path[K(path)>=0];candidate_points.append(path);candidate_values.append(actual(path))
    current=np.vstack(candidate_points);v=np.concatenate(candidate_values);geometric=(current[:,0]>=-1)&(current[:,-1]<.56)&(gram(current)>=0);current=current[geometric];v=v[geometric];kk=K(current);mask=kk>=0;current=current[mask];v=v[mask];neg=current[v<-1e-9];nv=v[v<-1e-9]
    label,n=components(neg,.035);rows=[]
    for ix in sorted([np.flatnonzero(label==j) for j in range(n)],key=lambda ix:min(nv[ix])):
        q=neg[ix];vals=nv[ix];best=q[np.argmin(vals)];rows.append({'id':len(rows)+1,'center_minimum_sample':best.tolist(),'depth_R':float(min(vals)),'negative_sample_count':len(q),'sample_bbox_min':q.min(axis=0).tolist(),'sample_bbox_max':q.max(axis=0).tolist(),'sample_bbox_width':np.ptp(q,axis=0).tolist(),'max_sample_radius_from_center':float(np.max(np.linalg.norm(q-best,axis=1))),'Gram_center':float(gram(best)[0]),'Ckernel_center':float(K(best)[0]),'old_C_center':float(Cold(best)[0]),'K_center_exact_fraction_sign':int(np.sign(K.exact_fraction(best))), 'relevant_after_old_C_sample_count':int(sum(Cold(q)>=0))})
    sensitivity=[]
    for eps in [.01,.02,.035,.06]:_,nc=components(neg,eps);sensitivity.append({'radius':eps,'connected_sample_components':int(nc)})
    packet.update({'optimizations':history,'optimization_count':len(history),'valleys':rows,'cluster_radius':.035,'cluster_sensitivity':sensitivity,'negative_points':neg.tolist(),'negative_R':nv.tolist(),'negative_count':len(neg),'unthresholded_negative_count':int(sum(v<0)),'shallow_negative_count_minus1e9_to_zero':int(sum((v>=-1e-9)&(v<0))),'sampling_extent_warning':'Bounding boxes and radius enclose sampled negatives only. Sparse samples may split or merge basins; search cannot establish all negative components. Ckernel>=0 alone does not assert nine-point extendibility.','elapsed_seconds':time.monotonic()-start,'no_SDP':True,'stop_reason':'Completed at most12 independent starts within fixed wall budget; no automatic continuation.'});save();print('FINAL',json.dumps({'seconds':packet['elapsed_seconds'],'optimizations':len(history),'negative_count':len(neg),'valleys':rows,'cluster_sensitivity':sensitivity}),flush=True)

if __name__=='__main__':run()
