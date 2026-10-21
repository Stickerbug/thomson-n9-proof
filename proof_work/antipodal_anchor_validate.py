import json,numpy as np,scipy.optimize as so
from fractions import Fraction
from pathlib import Path
D=json.loads(Path('proof_work/antipodal_anchor_exact_export.json').read_text());terms=[(np.array(a),float(Fraction(v)))for a,v in D['residual_monomial']]
def r(T):
 return sum(c*np.prod(T**a,axis=-1) for a,c in terms)
def dec(q):
 z,w,alpha=q
 return np.array([z,w,z*w+np.sqrt((1-z*z)*(1-w*w))*np.cos(alpha)])
def fun(q):
 T=dec(q)
 return r(T) if T[2]<=.57 else 10+(T[2]-.57)*100
mins=[]
for seed in [83,95,157,992]:
 s=so.differential_evolution(fun,[(-.57,.57),(-.57,.57),(0,np.pi)],seed=seed,popsize=18,maxiter=400,tol=1e-10,polish=True)
 mins.append({'residual':float(s.fun),'triple':dec(s.x).tolist()})
rng=np.random.default_rng(8823);z=rng.uniform(-.57,.57,100000);w=rng.uniform(-.57,.57,100000);a=rng.uniform(0,np.pi,100000);t=z*w+np.sqrt((1-z*z)*(1-w*w))*np.cos(a);T=np.c_[z,w,t];T=T[t<=.57];R=r(T)
ans={'DE':mins,'random_count':len(T),'random_min':float(R.min()),'random_witness':T[np.argmin(R)].tolist(),'note':'floating point diagnostics on exact exported polynomial, not proof'}
Path('proof_work/antipodal_anchor_validation.json').write_text(json.dumps(ans,indent=2));print(json.dumps(ans),flush=True)
