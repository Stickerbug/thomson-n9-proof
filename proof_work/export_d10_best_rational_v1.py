"""Exact rational PSD model export; positivity of R is NOT certified here.
Use original monomial A blocks from d10 best_solution (round1), no sharp algebraic parameter.
"""
import argparse,itertools,json,time
from pathlib import Path
from fractions import Fraction as F
import numpy as np
from certify_three_point_d4 import const,add,scale,mul,mono,permute,diag,ldl
from sharp_boundary_actualf_v3 import Compiled,validate,random_cond
from three_point_sampled import design
ROOT=Path(__file__).parent

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--target',default='25.758');ap.add_argument('--out',required=True);args=ap.parse_args();out=Path(args.out);assert not out.exists();start=time.time()
 src=json.loads((ROOT/'sharp_boundary_actualf_d10_v3.json').read_text());model=src['best_solution'];degree=10;den=10**13;epsilon=F(1,10**10);A=[];pivots=[];round_errors=[]
 for raw in model['A']:
  raw=np.array(raw);n=len(raw);a=[[F(int(round(float((raw[i,j]+raw[j,i])/2)*den)),den)+epsilon*(i==j)for j in range(n)]for i in range(n)]
  assert all(a[i][j]==a[j][i]for i in range(n)for j in range(n));pivots.append(ldl(a));A.append(a)
  round_errors.append(float(np.max(np.abs(np.array([[float(z)for z in row]for row in a])-raw))))
 u,v,t=(mono(i,1)for i in range(3));aa=add(t,scale(mul(u,v),-1));bb=mul(add(const(1),scale(mul(u,u),-1)),add(const(1),scale(mul(v,v),-1)));Q=[const(1),aa]
 for k in range(1,degree):Q.append(add(scale(mul(aa,Q[-1]),2),scale(mul(bb,Q[-2]),-1)))
 kernel={}
 for k in range(degree+1):
  for i in range(degree+1-k):
   for j in range(degree+1-k):kernel=add(kernel,scale(mul(mul(mono(0,i),mono(1,j)),Q[k]),A[k][i][j]))
 polyF=scale(add(*(permute(kernel,pm)for pm in itertools.permutations(range(3)))),F(1,6));F111=sum(polyF.values());c=(F(args.target)+F(3,2)*F111)/12
 assert all(permute(polyF,pm)==polyF for pm in itertools.permutations(range(3)));assert 12*c-F(3,2)*F111==F(args.target)
 H=[F(x)for x in json.loads((ROOT/'conditional_h19_certificate.json').read_text())['h_monomial']];hp={(i,0,0):z for i,z in enumerate(H)if z};hs=add(*(permute(hp,pm)for pm in [(0,1,2),(1,0,2),(2,1,0)]));D=diag(polyF,0)
 residual=add(hs,scale(polyF,-7),*(scale(diag(polyF,j),-1)for j in range(3)),const(-c));assert all(permute(residual,pm)==residual for pm in itertools.permutations(range(3)))
 def serialize(poly):return [[list(k),str(z)]for k,z in sorted(poly.items())]
 result={'status':'exact_components_prepared_global_positivity_UNPROVED','target':args.target,'source_model':'sharp_boundary_actualf_d10_v3.json best_solution','source_iteration':model['iteration'],'degree':degree,'domain':'Gram PSD intersection [-1,14/25]^3','alternate_competitive_domain':'Gram PSD intersection [-499999/500000,14/25]^3; requires parent antipodal exclusion','minorant_dependency':'conditional_h19_certificate.json','rounding_denominator':str(den),'added_diagonal_epsilon':str(epsilon),'A':[[[str(z)for z in row]for row in a]for a in A],'psd_exact_ldl_pivots':pivots,'max_entry_changes':round_errors,'c':str(c),'F111':str(F111),'h_monomial':[str(z)for z in H],'F_monomial':serialize(polyF),'d_monomial':serialize(D),'residual_monomial':serialize(residual),'normalization_exact':'12*c-3/2*F111=target; R=sum(h)-7F-sum(d)-c','F_monomial_count':len(polyF),'residual_monomial_count':len(residual),'proof_status':'All A strictly positive definite by Fraction LDL, F/R reconstructed exactly and symmetric, normalization exact. NO Bernstein or other global R>=0 certification performed.'}
 out.write_text(json.dumps(result,indent=2)+'\n');print('EXACT_EXPORT',out,'Fterms',len(polyF),'Rterms',len(residual),'seconds',time.time()-start,flush=True)
 # Independent floating validation of the exact rational polynomial, not a proof.
 comp=Compiled([residual]);co=np.asarray(comp.M.toarray()[:,0]);der=[]
 for axis in range(3):
  pw=comp.powers.copy();coef=co*pw[:,axis];pw[:,axis]=np.maximum(0,pw[:,axis]-1);der.append((pw,coef))
 def residual_numeric(points,grad=False):
  points=np.atleast_2d(points);value=comp.monomials(points)@co
  if not grad:return value
  return value,np.column_stack([comp.monomials(points,pw)@cc for pw,cc in der])
 class Adapter:
  def kernel(self,unused):return residual_numeric
 rows,_=validate(Adapter(),None,np.random.default_rng(272921),0,degree)
 test=random_cond(60,np.random.default_rng(44559));nA=[np.array([[float(z)for z in row]for row in a])for a in A];rhs=np.sum(np.polynomial.polynomial.polyval(test,np.array([float(z)for z in H])),axis=1)-float(c)-sum(np.einsum('nij,ij->n',m,a)for m,a in zip(design(test,degree),nA))
 rows['original_kernel_vs_exact_polynomial_max_error']=float(np.max(np.abs(rhs-residual_numeric(test))));result['numeric_validation']=rows;result['seconds']=time.time()-start
 out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':result['status'],'numeric_minimum':rows['independent_minimum'],'worst_points':rows['worst_points'][:4],'kernel_crosscheck':rows['original_kernel_vs_exact_polynomial_max_error'],'seconds':result['seconds']}),flush=True)
if __name__=='__main__':main()
