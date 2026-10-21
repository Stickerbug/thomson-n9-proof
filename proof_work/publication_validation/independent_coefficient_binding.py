"""Independent sparse Q expansion, congruence, F/c enclosure containment."""
from pathlib import Path
from fractions import Fraction as Rat
from itertools import permutations
from hashlib import sha256
from time import monotonic
import json
from independent_integer_interval import Box,InvalidMath
Z=(0,0,0)
ZERO=Box(0)
def need(ok,msg):
    if not ok:raise InvalidMath(msg)
def decode(x):return Box(Rat(int(x['lo_numerator']),1<<int(x['denominator_power_of_two'])),Rat(int(x['hi_numerator']),1<<int(x['denominator_power_of_two'])))
def sparse_add(a,b):
    c=a.copy()
    for e,v in b.items():
        c[e]=c.get(e,0)+v
        if c[e]==0:del c[e]
    return c
def sparse_scale(a,k):return {e:v*k for e,v in a.items()if v*k}
def sparse_mul(a,b):
    c={}
    for e,v in a.items():
        for f,w in b.items():
            key=tuple(e[i]+f[i]for i in range(3));c[key]=c.get(key,0)+v*w
    return {e:v for e,v in c.items()if v}
def qpolys():
    a={(0,0,1):1,(1,1,0):-1};b={Z:1,(2,0,0):-1,(0,2,0):-1,(2,2,0):1};out=[{Z:1},a]
    for k in range(1,10):out.append(sparse_add(sparse_scale(sparse_mul(a,out[k]),2),sparse_scale(sparse_mul(b,out[k-1]),-1)))
    return out
def construct(NN,xx,indices):
    lookup={tuple(t):j for j,t in enumerate(indices)};As=[]
    for k,N in enumerate(NN):
        n=len(N)
        if not n:As.append([]);continue
        m=len(N[0]);B=[[xx[lookup[k,min(i,j),max(i,j)]]for j in range(n)]for i in range(n)]
        BN=[[sum((B[i][j]*N[j][a]for j in range(n)),ZERO)for a in range(m)]for i in range(n)]
        A=[[sum((N[i][a]*BN[i][b]for i in range(n)),ZERO)for b in range(m)]for a in range(m)];As.append(A)
    qs=qpolys();F={};sixth=Box(Rat(1,6))
    for k,A in enumerate(As):
        for i,row in enumerate(A):
            for j,value in enumerate(row):
                for e,c in qs[k].items():
                    raw=(e[0]+i,e[1]+j,e[2]);v=value*c*sixth
                    for permutation in permutations(range(3)):
                        target=[0]*3
                        for axis in range(3):target[permutation[axis]]=raw[axis]
                        key=tuple(target);F[key]=F.get(key,ZERO)+v
    return F,As,qs
def main():
    t=monotonic();out=Path(__file__).resolve().parent;rawN=(out/'independent_kernel_refined_result.json').read_bytes();rawX=(out/'independent_contact_solve_refined_result.json').read_bytes();rawC=(out.parent/'d10_relative_normal_exact2026_coefficients.json').read_bytes();ndata=json.loads(rawN);xdata=json.loads(rawX);co=json.loads(rawC)
    need(xdata['all190_new_enclosures_inside_original'],'33solve enclosure inclusion prerequisite failed');need(xdata['N_result_sha256']==sha256(rawN).hexdigest(),'N/solve input binding mismatch')
    NN=[[[Box(*entry)for entry in col]for col in block['N_columns_enclosures']]for block in ndata['blocks']];xx=[Box(*entry)for entry in xdata['solution190_enclosures']];F,As,qs=construct(NN,xx,ndata['indices']);expected={tuple(e):decode(c)for e,c in co['F_coefficients']};missing=sorted(set(expected)-set(F));extra=sorted(set(F)-set(expected));outside=[]
    for e,v in F.items():
        if e not in expected:continue
        old=expected[e]
        if not old.lo<=v.lo<=v.hi<=old.hi:outside.append({'exponent':list(e),'new':v.serial(),'original':old.serial()})
    r=Box(*ndata['root_interval']);nodes=[1-Rat(3,2)*r*r,2*r*r-1,r*r/2-1,Box(Rat(-1,2)),r/2,-r];energy=sum((w/(2-2*x).sqrt()for w,x in zip([6,3,6,3,12,6],nodes)),ZERO);F111=sum(F.values(),ZERO);constant=energy/12+F111/8;oldc=decode(co['c']);oldE=decode(co['E_star']);old111=decode(co['F111']);cinside=oldc.lo<=constant.lo<=constant.hi<=oldc.hi;Einside=oldE.lo<=energy.lo<=energy.hi<=oldE.hi;F111inside=old111.lo<=F111.lo<=F111.hi<=old111.hi;passed=not missing and not extra and not outside and cinside and Einside and F111inside
    result={'status':'INDEPENDENT_N_CONTACT33_F_C_BINDING_PASS'if passed else'INDEPENDENT_F_C_CONTAINMENT_FAILED','bits':640,'root_interval':ndata['root_interval'],'F_coefficients':[[list(e),v.serial()]for e,v in sorted(F.items())],'F_count':len(F),'expected_F_count':len(expected),'missing_exponents':missing,'extra_exponents':extra,'F_outside_original':outside,'all_F_enclosures_inside_original':not outside and not missing and not extra,'E_star':energy.serial(),'F111':F111.serial(),'c':constant.serial(),'c_inside_original':cinside,'E_inside_original':Einside,'F111_inside_original':F111inside,'A_blocks_enclosures':[[[v.serial()for v in row]for row in A]for A in As],'Q_polynomials':[[[list(e),c]for e,c in sorted(q.items())]for q in qs],'source_sha256':{'independent_kernel_refined_result.json':sha256(rawN).hexdigest(),'independent_contact_solve_refined_result.json':sha256(rawX).hexdigest(),'d10_relative_normal_exact2026_coefficients.json':sha256(rawC).hexdigest()},'elapsed_seconds':monotonic()-t,'scope':'N is independently proven exact kernel basis; exact selected33 contact system has independently enclosed solution; F constructed via A=N B Ntranspose and six-permutation sparse Q expansion, all756 F plus c contained in original coefficient model. PSD follows from original B enclosure PSD check plus new190 containment. Exact45 needs prior rank33/W compatibility. 12local and main tree leaf verifier remain separate.'}
    with (out/'independent_coefficient_binding_result.json').open('x')as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps({k:v for k,v in result.items()if k not in ['F_coefficients','A_blocks_enclosures','Q_polynomials','F_outside_original']}),flush=True)
if __name__=='__main__':main()
