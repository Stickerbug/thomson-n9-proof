"""NONRIGOROUS final model validation with parent's LP-defect competitive-triangle cut.
Does not prove that cut or any nonnegativity claim. No further SDP optimization.
"""
import json,time,argparse
from pathlib import Path
from fractions import Fraction as F
import numpy as np
from scipy.optimize import minimize,differential_evolution
from numpy.polynomial import legendre as LG,polynomial as PO
from sharp_boundary_actualf_v3 import Compiled,polynomials,map_angles,valid,random_cond,boundary_points,near_points,angle_of,LIMIT,ANGLE,ENERGY
from three_point_sampled import design
ROOT=Path(__file__).parent

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--model',required=True);ap.add_argument('--out',required=True);ap.add_argument('--best',action='store_true');args=ap.parse_args();out=Path(args.out);assert not out.exists();start=time.time()
 saved=json.loads(Path(args.model).read_text());selected=len(saved['history'])-1
 if args.best:
  saved['solution']=saved['best_solution'];selected=saved['best_solution']['iteration']
 degree=saved['degree'];N=[np.array(n)for n in saved['nullspace_bases']];P,indices=polynomials(N,degree);comp=Compiled(P);xx=np.array(saved['solution']['x']);residual=comp.kernel(xx)
 p=np.array([float(F(x))for x in json.loads((ROOT/'rational_lp24.json').read_text())['legendre_coefficients']]);hp=np.array([float(F(x))for x in json.loads((ROOT/'three_point_d4_exact_25_745.json').read_text())['h_monomial']]);pd=LG.legder(p);hd=PO.polyder(hp)
 # U is a deliberately rounded UP candidate bound; epsilon uncertainty in C comparisons is retained as -1e-10.
 U=25.759986531269832;B=(81*p[0]-9*np.sum(p))/2;gap=U-B
 def cfun(pts,gradient=False):
  pts=np.atleast_2d(pts);c=gap-np.sum(PO.polyval(pts,hp)-LG.legval(pts,p),axis=1)
  return (c,-(PO.polyval(pts,hd)-LG.legval(pts,pd)))if gradient else c
 def feasible(pts):return valid(pts)&(cfun(pts)>=-1e-10)
 rng=np.random.default_rng(231118);record=[];rows={}
 def found(kind,point):
  point=np.ravel(point);item={'kind':kind,'triangle':point.tolist(),'residual':float(residual(point)[0]),'C':float(cfun(point)[0]),'domain_feasible':bool(feasible(point)[0]),'gram_determinant':float(1+2*np.prod(point)-point@point)}
  if item['domain_feasible']:record.append(item)
  return item
 pools=[]
 for kind,points in [('random',random_cond(50000,rng)),('boundary',boundary_points(18000,rng)),('near_antipodal',near_points(12000,rng))]:
  points=points[feasible(points)];r=residual(points);ix=np.argsort(r);rows[kind]={'feasible_count':len(points),'minimum':found(kind,points[ix[0]])};pools.append(points[ix[:40]])
 # Check all unrestricted worst points and explicit vertices against the competitive predicate.
 rows['unrestricted_worst_predicate']=[found('unrestricted_worst',v['triangle'])for v in saved['history'][selected]['worst_points']]
 rows['corners']=[found('corner',v)for v in [[LIMIT,LIMIT,LIMIT],[-1,0,0]]]
 pool=np.vstack(pools);starts=[angle_of(p)for p in pool];locals=[]
 def obj(v,sign=None):
  pts,J=map_angles(v,sign,True);f,g=residual(pts,True);return float(f[0]),g[0]@J[0]
 def cf(v,sign=None):return float(cfun(map_angles(v,sign))[0])
 def cj(v,sign=None):
  pts,J=map_angles(v,sign,True);c,g=cfun(pts,True);return g[0]@J[0]
 def tc(v):return float(LIMIT-map_angles(v)[0,2])
 def tj(v):return -map_angles(v,None,True)[1][0,2]
 for seed in starts[:36]:
  opt=minimize(obj,seed,jac=True,method='SLSQP',bounds=[(ANGLE,np.pi),(ANGLE,np.pi),(0,np.pi)],constraints=[{'type':'ineq','fun':cf,'jac':cj},{'type':'ineq','fun':tc,'jac':tj}],options={'maxiter':200,'ftol':2e-13})
  locals.append(found('local3d',map_angles(opt.x)[0]))
 rows['local3D']=sorted(locals,key=lambda a:a['residual'])[:8]
 bounds=[]
 for sign,component in [(-1,0),(1,1),(1,-1)]:
  def linear(v,s=sign,c=component):return (2*np.pi-ANGLE-v[0]-v[1])if s==-1 else c*(v[0]-v[1])-ANGLE
  seeds=[]
  for pnt in pool:
   v=np.arccos(np.clip(pnt[:2],-1,1))
   if linear(v)>=0 and feasible(map_angles(v,sign))[0]:seeds.append(v)
  while len(seeds)<14:
   v=rng.uniform(ANGLE,np.pi,2)
   if linear(v)>=0 and feasible(map_angles(v,sign))[0]:seeds.append(v)
  bd=[]
  for seed in seeds[:16]:
   opt=minimize(lambda v:obj(v,sign),seed,jac=True,method='SLSQP',bounds=[(ANGLE,np.pi)]*2,constraints=[{'type':'ineq','fun':linear},{'type':'ineq','fun':lambda v:cf(v,sign),'jac':lambda v:cj(v,sign)}],options={'maxiter':180,'ftol':2e-13});bd.append(found('boundary2d',map_angles(opt.x,sign)[0]))
  def fun(v):
   v=np.asarray(v);single=v.ndim==1;vv=v[None]if single else v.T;points=map_angles(vv,sign);vals=residual(points)+1000*np.maximum(0,-cfun(points))+1000*np.maximum(0,-np.array([linear(z)for z in vv]))
   return float(vals[0])if single else vals
  de=differential_evolution(fun,[(ANGLE,np.pi)]*2,seed=811+component+degree,popsize=12,maxiter=100,vectorized=True,updating='deferred',tol=1e-9,polish=True)
  bd.append(found('DE2d',map_angles(de.x,sign)[0]));bounds.append({'sign':sign,'component':component,'best':sorted(bd,key=lambda a:a['residual'])[:3]})
 rows['boundary2D']=bounds
 def deobj(v):
  v=np.asarray(v);single=v.ndim==1;vv=v[None]if single else v.T;points=map_angles(vv);vals=residual(points)+1000*np.maximum(0,-cfun(points))+1000*np.maximum(0,points[:,2]-LIMIT)
  return float(vals[0])if single else vals
 rows['DE3d']=[]
 for si in range(3):
  de=differential_evolution(deobj,[(ANGLE,np.pi),(ANGLE,np.pi),(0,np.pi)],seed=991+si,popsize=14,maxiter=150,vectorized=True,updating='deferred',x0=starts[si],tol=1e-10,polish=True);rows['DE3d'].append(found('DE3d',map_angles(de.x)[0]))
 a=[np.array(a)for a in saved['solution']['A']];cc=saved['solution']['c'];test=random_cond(60,rng);rr=np.sum((2-2*test)**(-.5),axis=1)-cc-sum(np.einsum('nij,ij->n',m,aa)for m,aa in zip(design(test,degree),a))
 result={'warning':'NONRIGOROUS validator, not proof; predicate requires exact parent LP-defect theorem','model':args.model,'selected_iteration':selected,'domain':'Gram PSD intersect [-1,.56]^3 and C>=0','C_definition':'U-B-sum(h11(t)-rational_lp24(t))','C_numeric_threshold':-1e-10,'U':U,'B':float(B),'gap':float(gap),'history':rows,'independent_minimum':min(v['residual']for v in record),'worst_points':sorted(record,key=lambda a:a['residual'])[:15],'design_crosscheck_error':float(abs(comp.kernel(xx)(test)-rr).max()),'seconds':time.time()-start}
 out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
if __name__=='__main__':main()
