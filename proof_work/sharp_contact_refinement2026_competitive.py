"""Independent competitive-domain validation of final fixed sharp model; NO new SDP."""
import json,time,math
from fractions import Fraction as Fr
import numpy as np
import mpmath as mp
from scipy.optimize import minimize,differential_evolution,NonlinearConstraint
from sharp_contact_refinement2026_core import ROOT,PREFIX,KEY,DEGREE
from sharp_contact_refinement2026_refine import IndependentActual
from sharp_contact_refinement2026_export import mpR
from sharp_boundary_actualf_v3 import polynomials,Compiled,random_cond

class Competitive:
    def __init__(self,certificate):
        self.terms=certificate['C_monomial'];self.constant=mp.mpf(0);a=[mp.mpf(0)]*23
        def number(s):
            q=Fr(s);return mp.mpf(q.numerator)/q.denominator
        for e,s in self.terms:
            if not sum(e):self.constant+=number(s)
            elif e[0]:a[e[0]]+=number(s)
        # q(x), x=-.22+.78*z, formed and converted to Chebyshev at 80 digits.
        center=mp.mpf('-.22');radius=mp.mpf('.78');mono=[mp.mpf(0)]*len(a)
        for k,ak in enumerate(a):
            for j in range(k+1):mono[j]+=ak*math.comb(k,j)*center**(k-j)*radius**j
        powers=[mp.mpf(1)]+[mp.mpf(0)]*(len(a)-1);cheb=[mp.mpf(0)]*len(a)
        for k,ak in enumerate(mono):
            cheb=[v+ak*w for v,w in zip(cheb,powers)];nxt=[mp.mpf(0)]*len(a)
            if k<len(a)-1:
                nxt[1]+=powers[0]
                for j in range(1,len(a)-1):nxt[j-1]+=powers[j]/2;nxt[j+1]+=powers[j]/2
                powers=nxt
        self.coefficients=np.array([float(v) for v in cheb]);self.dc=np.polynomial.chebyshev.chebder(self.coefficients)/.78;self.const=float(self.constant)
    def __call__(self,points,grad=False):
        pp=np.atleast_2d(points);z=(pp+.22)/.78;value=self.const+np.polynomial.chebyshev.chebval(z,self.coefficients).sum(axis=1)
        return (value,np.polynomial.chebyshev.chebval(z,self.dc)) if grad else value
    def exact_decimal_value(self,point):
        p=[mp.mpf(str(v)) for v in point];out=mp.mpf(0)
        for e,s in self.terms:
            f=Fr(s);out+=mp.mpf(f.numerator)/f.denominator*mp.fprod(p[i]**e[i] for i in range(3))
        return mp.nstr(out,80)

def run(model_file=None):
    mp.mp.dps=80;start=time.time();source=ROOT/(PREFIX+'results.json') if model_file is None else ROOT/model_file;data=json.loads(source.read_text());sol=data['best_solution'];N=[np.array(n) for n in sol['N']];xx=np.array(sol['x']);A=[np.array(a) for a in sol['A']];c=sol['c'];actual=IndependentActual(A,c)
    cert=json.loads((ROOT/'competitive_triple_constraint_certificate.json').read_text());C=Competitive(cert);P,_=polynomials(N,DEGREE);comp=Compiled(P);residual=comp.kernel(xx);rng=np.random.default_rng(2026102009)
    def constraints(p,jac=False):
        u,v,t=p;g=1+2*u*v*t-u*u-v*v-t*t;cv,cg=C(p,True)
        if jac:return np.vstack([[2*(v*t-u),2*(u*t-v),2*(u*v-t)],cg[0],[-1,1,0],[0,-1,1]])
        return np.array([g,cv[0],v-u,t-v])
    def obj(p):
        v,g=residual(p,True);return float(v[0]),g[0]
    points=np.sort(np.vstack([np.array(data['training_points']),random_cond(18000,rng),np.array(data['diagnostic']['candidate_points']),KEY]),axis=1)
    feasible=(C(points)>=0)&(1+2*np.prod(points,axis=1)-np.sum(points*points,axis=1)>=-1e-13);points=points[feasible];v=residual(points);order=np.argsort(v)
    seeds=list(points[order[:45]])+list(points[rng.choice(len(points),20,replace=False)])
    seeds.extend(np.array(data['diagnostic']['candidate_points']))
    result={'warning':'NUMERICAL DISCOVERY ONLY; no new SDP or certificate','source_model':str(source)+' best_solution iteration'+str(sol['iteration']),'source_competitive_certificate':str(ROOT/'competitive_triple_constraint_certificate.json'),'constraints':'-1<=u<=v<=t<=.56, Gram>=0, certified necessary C>=0','C_evaluation':'80-digit affine Chebyshev coefficient conversion followed by stable double Chebyshev recurrence; exact rational C re-evaluated at final points with 80 digits','source_fullbox_worst':sol['worst_point'],'source_fullbox_worst_C_exact':C.exact_decimal_value(sol['worst_point']['triangle']),'sorted_feasible_sample_count':len(points),'sample_min_R':float(min(v)),'sample_min_point':points[order[0]].tolist(),'local_search':[]}
    out=ROOT/(PREFIX+'competitive_validation.json');assert not out.exists()
    def save():out.write_text(json.dumps(result,indent=2)+chr(10))
    save();print('BUILD competitive','seconds',time.time()-start,'fullbox_worst_C',result['source_fullbox_worst_C_exact'],flush=True)
    for seed in seeds:
        opt=minimize(obj,seed,jac=True,method='SLSQP',bounds=[(-1,.56)]*3,constraints=[{'type':'ineq','fun':constraints,'jac':lambda p:constraints(p,True)}],options={'maxiter':180,'ftol':2e-13})
        cf=constraints(opt.x)
        if min(cf)>=-2e-10:
            result['local_search'].append({'point':opt.x.tolist(),'R_compiled':float(residual(opt.x)[0]),'R_actual':float(actual(opt.x)[0]),'constraint_values':cf.tolist(),'success':bool(opt.success),'message':str(opt.message)})
    result['local_search'].sort(key=lambda row:row['R_actual']);save();print('LOCALS',result['local_search'][:2],'seconds',time.time()-start,flush=True)
    def vec_constraints(p):
        pp=np.asarray(p);single=pp.ndim==1;pp=pp[:,None] if single else pp;u,v,t=pp
        out=np.vstack([1+2*u*v*t-u*u-v*v-t*t,C(pp.T),v-u,t-v])
        return out[:,0] if single else out
    def vec_obj(p):
        pp=np.asarray(p);single=pp.ndim==1;pp=pp[None] if single else pp.T;vv=residual(pp)
        return float(vv[0]) if single else vv
    de=differential_evolution(vec_obj,[(-1,.56)]*3,constraints=(NonlinearConstraint(vec_constraints,0,np.inf),),seed=2026102009,popsize=24,maxiter=250,vectorized=True,updating='deferred',polish=False,tol=1e-10,x0=points[order[0]])
    result['DE']={'point':de.x.tolist(),'R_compiled':float(residual(de.x)[0]),'R_actual':float(actual(de.x)[0]),'constraint_values':constraints(de.x).tolist(),'success':bool(de.success),'message':str(de.message),'iterations':int(de.nit),'evaluations':int(de.nfev)}
    candidates=result['local_search']+[result['DE']];candidates.sort(key=lambda row:row['R_actual']);refined=[]
    for row in candidates[:5]:
        def direct_obj(p):
            val,g=actual(p,True);return float(val[0]),g[0]
        op=minimize(direct_obj,row['point'],jac=True,method='SLSQP',bounds=[(-1,.56)]*3,constraints=[{'type':'ineq','fun':constraints,'jac':lambda p:constraints(p,True)}],options={'maxiter':100,'ftol':1e-14})
        if min(constraints(op.x))>=-2e-10:refined.append({'point':op.x.tolist(),'R_actual':float(actual(op.x)[0]),'constraint_values':constraints(op.x).tolist(),'direct_original_A_polish':True})
    candidates+=refined;candidates.sort(key=lambda row:row['R_actual']);result['direct_original_A_polished']=refined
    # If a numerical minimizer falls slightly outside C=0 or Gram=0, retain it
    # separately and move toward a strict feasible candidate before quoting a witness.
    strict=points[(C(points)>1e-3)&(1+2*np.prod(points,axis=1)-np.sum(points*points,axis=1)>1e-2)][0]
    for row in candidates[:8]:
        for delta in [0.,1e-10,1e-8,1e-6]:
            point=(1-delta)*np.array(row['point'])+delta*strict
            if min(constraints(point))>0:
                value=float(actual(point)[0]);new={'point':point.tolist(),'R_actual':value,'constraint_values':constraints(point).tolist(),'strict_feasible_perturbation_delta':delta};refined.append(new);break
    strictrows=[row for row in refined if min(row['constraint_values'])>0]
    result['best_strict_feasible']=min(strictrows,key=lambda row:row['R_actual']) if strictrows else None;result['best_with_numeric_feasibility_tolerance']=candidates[0]
    if result['best_strict_feasible']:
        row=result['best_strict_feasible'];row['C_decimal_80digit']=C.exact_decimal_value(row['point']);row['R_gram_decimal_80digit']=mpR(sol['A'],sol['c'],row['point'])
    result['key_C_exact']=C.exact_decimal_value(KEY);result['C_chebyshev_coefficients']=C.coefficients.tolist();result['compiled_vs_original_on_best']=float(abs(residual(candidates[0]['point'])[0]-actual(candidates[0]['point'])[0]));result['elapsed_seconds']=time.time()-start;save()
    print('FINAL_COMPETITIVE',json.dumps({'best_strict_feasible':result['best_strict_feasible'],'best_numeric':result['best_with_numeric_feasibility_tolerance'],'DE':result['DE'],'elapsed_seconds':result['elapsed_seconds']},indent=2),flush=True)
if __name__=='__main__':run()
