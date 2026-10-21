"""Independent forward-AD contact equations and strict interval Gauss solve."""
from pathlib import Path
from fractions import Fraction as Q
from itertools import permutations
from hashlib import sha256
from time import monotonic
import json
from independent_integer_interval import Box, BITS, InvalidMath
def decode(x):
    return Box(Q(int(x["lo_numerator"]),1<<384),Q(int(x["hi_numerator"]),1<<384))
ZERO=Box(0)
SIXTH=Box(Q(1,6))
def need(ok,msg):
    if not ok:raise InvalidMath(msg)
def mul(a,b):
    if a.l==a.h==0 or b.l==b.h==0:return ZERO
    return a*b
class Dual4:
    def __init__(self,v,d=None):self.v=Box.cast(v);self.d=[ZERO]*3 if d is None else d
    @staticmethod
    def cast(x):return x if isinstance(x,Dual4)else Dual4(x)
    def __add__(self,x):
        x=self.cast(x);return Dual4(self.v+x.v,[a+b for a,b in zip(self.d,x.d)])
    __radd__=__add__
    def __neg__(self):return Dual4(-self.v,[-a for a in self.d])
    def __sub__(self,x):return self+-self.cast(x)
    def __rsub__(self,x):return self.cast(x)+-self
    def __mul__(self,x):
        x=self.cast(x);return Dual4(mul(self.v,x.v),[mul(a,x.v)+mul(self.v,b)for a,b in zip(self.d,x.d)])
    __rmul__=__mul__
    def lanes(self):return [self.v]+self.d
def dotpoly(col,x):
    ans=Dual4(0)
    for c in reversed(col):ans=ans*x+c
    return ans
def build_jet(point,NN,indices):
    xyz=[Dual4(point[j],[Box(int(i==j))for i in range(3)])for j in range(3)];out=[Dual4(0)for _ in indices]
    for perm in permutations(range(3)):
        u,v,t=[xyz[j]for j in perm];a=t-u*v;b=(1-u*u)*(1-v*v);q=[Dual4(1),a]
        for k in range(1,10):q.append(2*a*q[-1]-b*q[-2])
        pu=[[dotpoly(col,u)for col in N]for N in NN];pv=[[dotpoly(col,v)for col in N]for N in NN]
        for h,(k,i,j)in enumerate(indices):
            basis=pu[k][i]*pv[k][j]
            if i!=j:basis=basis+pu[k][j]*pv[k][i]
            out[h]=out[h]+q[k]*basis*SIXTH
    return [[x.lanes()[lane]for x in out]for lane in range(4)]
def solve(A,b):
    n=len(b);need(len(A)==n and all(len(row)==n for row in A),'nonsquare system');C=[row.copy()+[rhs]for row,rhs in zip(A,b)];piv=[]
    for k in range(n):
        choices=[i for i in range(k,n)if C[i][k].lo>0 or C[i][k].hi<0];need(bool(choices),f'no strict nonzero Gauss pivot at {k}')
        q=max(choices,key=lambda i:abs(C[i][k].lo+C[i][k].hi));C[k],C[q]=C[q],C[k];d=C[k][k];piv.append({'step':k,'row_swap_with':q,'interval':d.serial()})
        for i in range(k+1,n):
            scale=C[i][k]/d
            for j in range(k+1,n+1):C[i][j]=C[i][j]-scale*C[k][j]
            C[i][k]=ZERO
    x=[ZERO]*n
    for i in reversed(range(n)):x[i]=(C[i][n]-sum((C[i][j]*x[j]for j in range(i+1,n)),ZERO))/C[i][i]
    return x,piv
def main():
    start=monotonic();out=Path(__file__).resolve().parent;certpath=out.parent/'d10_relative_normal_exact2026_certificate.json';raw=certpath.read_bytes();data=json.loads(raw);npath=out/'independent_kernel_refined_result.json';nraw=npath.read_bytes();ndata=json.loads(nraw)
    NN=[[[Box(*entry)for entry in col]for col in block['N_columns_enclosures']]for block in ndata['blocks']];indices=[tuple(x)for x in ndata['indices']];need([list(x)for x in indices]==data['indices'],'N indices mismatch')
    lo,hi=map(Q,ndata['root_interval']);r=Box(lo,hi);nodes=[1-Q(3,2)*r*r,2*r*r-1,r*r/2-1,Box(Q(-1,2)),r/2,-r];names='ABCDFG';meta=data['row_meta'];need(len(meta)==45,'expected45 equations')
    cache={}
    def jet(point):
        key=tuple(tuple(x.serial())for x in point)
        if key not in cache:
            cache[key]=build_jet(point,NN,indices)
            cp=out/('contact_jet640_'+sha256(repr(key).encode()).hexdigest()[:20]+'.json')
            if not cp.exists():
                with cp.open('x')as stream:json.dump({'point':key,'jet':[[x.serial()for x in row]for row in cache[key]]},stream)
            print(json.dumps({'jets_built':len(cache),'elapsed_seconds':monotonic()-start}),flush=True)
        return cache[key]
    diag=[jet([Box(1),x,x])for x in nodes];f111=jet([Box(1)]*3)[0];M=[];rhs=[]
    f=[1/(2-2*x).sqrt()for x in nodes];fp=[f[j]/(2-2*x)for j,x in enumerate(nodes)];E=sum((w*v for w,v in zip([6,3,6,3,12,6],f)),ZERO)
    for kind,labels,*axis in meta:
        lab=[names.index(x)for x in labels];pt=[nodes[j]for j in lab];J=jet(pt)
        if kind=='value':
            M.append([7*J[0][h]+sum((diag[j][0][h]for j in lab),ZERO)+f111[h]/8 for h in range(190)]);rhs.append(sum((f[j]for j in lab),ZERO)-E/12)
        else:
            grad=[[7*J[j+1][h]+diag[lab[j]][2][h]+diag[lab[j]][3][h]for h in range(190)]for j in range(3)]
            ax=axis[0]
            if kind=='gradient':M.append(grad[ax]);rhs.append(fp[lab[ax]])
            else:
                need(kind=='tangent'and ax in (1,2),'unrecognized contact row');u,v,t=pt;g=[2*(v*t-u),2*(u*t-v),2*(u*v-t)]
                M.append([g[0]*grad[ax][h]-g[ax]*grad[0][h]for h in range(190)]);rhs.append(g[0]*fp[lab[ax]]-g[ax]*fp[lab[0]])
    print(json.dumps({'phase':'contact_system_built','elapsed_seconds':monotonic()-start}),flush=True)
    rows=data['selected_rows'];cols=data['selected_columns'];need(len(rows)==len(set(rows))==33 and len(cols)==len(set(cols))==33,'selected system dimensions invalid')
    need(all(type(x)is int and 0<=x<45 for x in rows)and all(type(x)is int and 0<=x<190 for x in cols),'selected index out of range')
    seed=list(map(Q,data['seed']));need(len(seed)==190,'wrong seed size');res=[rhs[i]-sum((M[i][j]*seed[j]for j in range(190)),ZERO)for i in rows];A=[[M[i][j]for j in cols]for i in rows]
    delta,piv=solve(A,res);xx=[Box(x)for x in seed]
    for j,d in zip(cols,delta):xx[j]=xx[j]+d
    original=[decode(x)for x in data['reduced_solution_enclosures']];outside=[{'index':i,'new':x.serial(),'old':o.serial()}for i,(x,o)in enumerate(zip(xx,original))if not(o.lo<=x.lo<=x.hi<=o.hi)]
    result={'status':'INDEPENDENT_CONTACT33_SOLVE_AND_ENCLOSURE_MEMBERSHIP_PASS'if not outside else'INDEPENDENT_CONTACT33_SOLVED_ENCLOSURE_INCLUSION_FAILED','bits':BITS,'row_meta':meta,'selected_rows':rows,'selected_columns':cols,'A33_enclosures':[[x.serial()for x in row]for row in A],'rhs_residual33_enclosures':[x.serial()for x in res],'gauss_pivots':piv,'delta33_enclosures':[x.serial()for x in delta],'solution190_enclosures':[x.serial()for x in xx],'outside_original_enclosures':outside,'all190_new_enclosures_inside_original':not outside,'source_sha256':sha256(raw).hexdigest(),'N_result_sha256':sha256(nraw).hexdigest(),'checker_sha256':'recorded_separately_in_completion_manifest','elapsed_seconds':monotonic()-start,'scope':'Independent Dual4 chain-rule AD and interval Gauss establish exact33 selected solution enclosure for every r in bracket; exact45 still assumes rank33/W compatibility. No zero-containing residual is used as exact equality proof. No coefficient-model connection yet.'}
    with (out/'independent_contact_solve_refined_result.json').open('x')as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps({k:v for k,v in result.items()if k not in ['A33_enclosures','rhs_residual33_enclosures','gauss_pivots','delta33_enclosures','solution190_enclosures','outside_original_enclosures','row_meta']}),flush=True)
if __name__=='__main__':main()
