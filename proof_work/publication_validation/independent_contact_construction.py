"""Independent rational-polynomial kernel complement, explicit minors, no RREF."""
from fractions import Fraction as Q
from math import comb
from itertools import combinations
from pathlib import Path
from hashlib import sha256
from time import monotonic
import json
from independent_candidate_bounds import Box, BITS, InvalidMath
DIMENSIONS=(9,9,7,7,5,5,3,3,1,1,0)
def need(ok,msg):
    if not ok:raise InvalidMath(msg)
class Poly:
    def __init__(self,c):
        if not isinstance(c,(tuple,list)):c=[Q(c)]
        c=list(map(Q,c))
        while len(c)>1 and c[-1]==0:c.pop()
        self.c=tuple(c)
    @staticmethod
    def cast(x):return x if isinstance(x,Poly)else Poly(x)
    def __add__(self,x):
        x=self.cast(x);n=max(len(self.c),len(x.c));return Poly([(self.c[i]if i<len(self.c)else 0)+(x.c[i]if i<len(x.c)else 0)for i in range(n)])
    __radd__=__add__
    def __neg__(self):return Poly([-x for x in self.c])
    def __sub__(self,x):return self+-self.cast(x)
    def __rsub__(self,x):return self.cast(x)+-self
    def __mul__(self,x):
        x=self.cast(x);c=[Q(0)]*(len(self.c)+len(x.c)-1)
        for i,a in enumerate(self.c):
            for j,b in enumerate(x.c):c[i+j]+=a*b
        return Poly(c)
    __rmul__=__mul__
    def __truediv__(self,x):return self*Q(1,Q(x))
    def __pow__(self,n):
        result=Poly(1)
        for _ in range(n):result=result*self
        return result
    def zero(self):return self.c==(Q(0),)
    def evaluate(self,x):
        acc=x*0
        for c in reversed(self.c):acc=acc*x+c
        return acc
    def serial(self):return list(map(str,self.c))
def feature_polynomials(k,m):
    r=Poly([0,1]);H=1-r*r
    def realpart(alpha,beta2):
        return sum(((-1)**j)*comb(k,2*j)*alpha**(k-2*j)*H**((k-2*j)//2)*beta2**j for j in range(k//2+1))
    A=1-Q(3,2)*r*r;B=2*r*r-1;C=r*r/2-1
    upper=2*realpart(-Q(3,2)*r,Q(3,4)*r*r);same=(2*r)**k*H**(k//2);other=2*realpart(r/2,Q(3,4)*r*r)
    opposite=(-1)**k*H**(k//2);adjacent=2*realpart(Poly(Q(1,2)),Poly(Q(3,4)))
    p=[(1 if k==0 else 0)+upper*A**i+same*B**i+other*C**i+opposite*(-r)**i+adjacent*(r/2)**i for i in range(m)]
    if k%2:c=[Poly(0)for _ in range(m)]
    else:
        capsum=sum((-1)**j*comb(k,2*j)*(Q(3,4)*r*r)**((k-2*j)//2)*H**j for j in range(k//2+1))
        c=[Poly((1 if k==0 else 0)+2*(-Q(1,2))**i*Q(3,4)**(k//2))+2*(-r)**i*(-1)**(k//2)*H**(k//2)+4*(r/2)**i*capsum for i in range(m)]
    return p,c
def exact_det(A):
    n=len(A);need(all(len(row)==n for row in A),'basis transform must be square');A=[row.copy()for row in A];det=Q(1)
    for j in range(n):
        q=next((i for i in range(j,n)if A[i][j]),None);need(q is not None,'singular rational basis transform')
        if q!=j:A[j],A[q]=A[q],A[j];det=-det
        d=A[j][j];det*=d
        for i in range(j+1,n):
            scale=A[i][j]/d
            for h in range(j+1,n):A[i][h]-=scale*A[j][h]
    return det
def construct(data):
    lo,hi=map(Q,data['root_interval']);need(0<lo<hi<1,'invalid radius bracket');mid=(lo+hi)/2;r=Box(lo,hi);records=[];NN=[]
    for k in range(11):
        m=11-k;p,c=feature_polynomials(k,m);pf=[v.evaluate(mid)for v in p];cf=[v.evaluate(mid)for v in c]
        expected_rank=2 if k%2==0 and k<10 else 1
        skipped=[]
        if expected_rank==2:
            pivot=None
            for a,b in combinations(range(m),2):
                determinant=p[a]*c[b]-p[b]*c[a]
                if determinant.evaluate(mid)!=0:pivot=(a,b);break
                need(determinant.zero(),'earlier minor only vanishes at midpoint');skipped.append([a,b])
            need(pivot is not None,'no nonzero rank2 minor');a,b=pivot;den=determinant
        else:
            need(k==10 or all(v.zero()for v in c),'rank1 cap must vanish identically')
            a=next((j for j in range(m)if pf[j]!=0),None);need(a is not None,'no nonzero rank1 feature')
            need(all(p[j].zero()for j in range(a)),'earlier rank1 coordinate only vanishes at midpoint');pivot=(a,);den=p[a]
        di=den.evaluate(r);need(di.lo>0 or di.hi<0,'pivot minor interval includes zero')
        free=[j for j in range(m)if j not in pivot];need(len(free)==DIMENSIONS[k],'wrong complement dimension')
        raw=[]
        for j in free:
            v=[Poly(0)for _ in range(m)];v[j]=den
            if len(pivot)==2:v[a]=p[b]*c[j]-c[b]*p[j];v[b]=c[a]*p[j]-p[a]*c[j]
            else:v[a]=-p[j]
            need(sum((p[i]*v[i]for i in range(m)),Poly(0)).zero(),'prism kernel syzygy failed')
            need(sum((c[i]*v[i]for i in range(m)),Poly(0)).zero(),'cap kernel syzygy failed');raw.append(v)
        T=[[Q(x)for x in row]for row in data['rational_basis_transforms'][k]];need(len(T)==len(free),'wrong basis transform dimension');tdet=exact_det(T)
        transformed=[[sum((raw[j][i]*T[j][q]for j in range(len(free))),Poly(0))for i in range(m)]for q in range(len(free))]
        for v in transformed:
            need(sum((p[i]*v[i]for i in range(m)),Poly(0)).zero()and sum((c[i]*v[i]for i in range(m)),Poly(0)).zero(),'transformed kernel syzygy failed')
        N=[[v.evaluate(r)/di for v in col]for col in transformed];NN.append(N)
        records.append({'k':k,'ambient_dimension':m,'reduced_dimension':len(free),'rank':expected_rank,'pivot_columns':list(pivot),'free_columns':free,'earlier_lex_minors_identically_zero':skipped,'denominator_polynomial':den.serial(),'denominator_enclosure':di.serial(),'p_polynomials':[v.serial()for v in p],'c_polynomials':[v.serial()for v in c],'exact_kernel_syzygies_verified':True,'rational_transform_determinant':str(tdet),'rational_basis_transform':[[str(x)for x in row]for row in T],'transformed_numerator_columns':[[v.serial()for v in col]for col in transformed],'N_columns_enclosures':[[v.serial()for v in col]for col in N]})
    return NN,records
def main():
    start=monotonic();out=Path(__file__).resolve().parent;source=out.parent/'d10_relative_normal_exact2026_certificate.json';raw=source.read_bytes();data=json.loads(raw);NN,records=construct(data)
    indices=[[k,i,j]for k,N in enumerate(NN)for i in range(len(N))for j in range(i,len(N))];need(indices==data['indices'],'reconstructed N index order differs')
    result={'status':'INDEPENDENT_KERNEL_COMPLEMENTS_PASS_CONTACT_SOLVE_PENDING','bits':BITS,'root_interval':data['root_interval'],'indices':indices,'blocks':records,'source_sha256':sha256(raw).hexdigest(),'checker_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'interval_module_sha256':sha256((out/'independent_candidate_bounds.py').read_bytes()).hexdigest(),'elapsed_seconds':monotonic()-start,'remaining':['Build contact M/rhs independently using automatic differentiation','Solve33 and prove membership in supplied reduced_solution_enclosures','45contact exactness requires rank33/W compatibility premise','Connect constructed solution to coefficient-model enclosure']}
    with (out/'independent_kernel_complements_result.json').open('x')as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps({k:v for k,v in result.items()if k not in ['blocks','indices']}),flush=True)
if __name__=='__main__':main()
