"""Discovery-only numeric probe of the unrestricted physical Gram domain."""
from pathlib import Path
from itertools import permutations
from decimal import Decimal,localcontext
from hashlib import sha256
from time import monotonic
import random,math,json
PERMS=list(permutations(range(3)))
def kernel(A,point,zero,one):
    total=zero
    for perm in PERMS:
        u,v,t=[point[i]for i in perm];uv=t-u*v;product=(one-u*u)*(one-v*v);qs=[one,uv]
        for k in range(1,len(A)-1):qs.append(2*uv*qs[-1]-product*qs[-2])
        up=[one];vp=[one]
        for _ in range(len(A)-1):up.append(up[-1]*u);vp.append(vp[-1]*v)
        for k,block in enumerate(A):
            value=zero
            for a,row in enumerate(block):
                for b,entry in enumerate(row):value+=entry*up[a]*vp[b]
            total+=value*qs[k]
    return total/6

def residual(A,c,point,zero,one,sqrt):
    F=kernel(A,point,zero,one);diagonal=[kernel(A,[one,t,t],zero,one)for t in point];energies=[one/sqrt(2-2*t)for t in point];return sum(energies,zero)-sum(diagonal,zero)-7*F-c,{'F':F,'diagonal_F':diagonal,'pair_energies':energies,'c':c}

def exact_gram(point):
    u,v,t=point;return 1+2*u*v*t-u*u-v*v-t*t

def confirm(A,c,point,family):
    with localcontext()as ctx:
        ctx.prec=90;zero=Decimal(0);one=Decimal(1);AA=[[[Decimal(str(v))for v in row]for row in block]for block in A];cc=Decimal(str(c));pp=list(map(lambda x:Decimal(str(x)),point))
        if family.startswith('boundary_'):
            sign=-1 if family.endswith('lower')else 1;v,t=pp[1:];pp[0]=v*t+sign*((one-v*v)*(one-t*t)).sqrt()
        value,details=residual(AA,cc,pp,zero,one,lambda v:v.sqrt());return {'decimal_precision':90,'point_decimal':list(map(str,pp)),'Rf_decimal':str(value),'gram_determinant_decimal':str(exact_gram(pp)),'F_decimal':str(details['F']),'diagonal_F_decimal':list(map(str,details['diagonal_F'])),'pair_energies_decimal':list(map(str,details['pair_energies'])),'c_decimal':str(cc),'physical_justification':'equilateral determinant=(1-s)^2*(1+2s)>0'if family=='equilateral'else'exact radical Gram parameterization u=vt+rho*sqrt((1-v^2)*(1-t^2)); rho in[-1,1]','boundary_expression_recomputed':family.startswith('boundary_')}

def main():
    begin=monotonic();p=Path(__file__).resolve().parent;source=p.parent/'d10_relative_normal2026_results.json';raw=source.read_bytes();data=json.loads(raw)['solution'];A=data['A'];c=data['c'];assert isinstance(A,list)and len(A)==11 and all(len(block)==11-k and all(len(row)==11-k for row in block)for k,block in enumerate(A));rng=random.Random(20260807);counts={'equilateral':0,'random_gram':0,'boundary_lower':0,'boundary_upper':0};minimum=None;negative=None;positive_max=None;planned=[.5600001,.58,.6,.65,.7,.75,.8,.85,.9,.95,.98,.99,.999,.9999,.99999]
    def samples():
        i=0
        while True:
            s=planned[i]if i<len(planned)else .56+(.99999-.56)*rng.random();yield 'equilateral',[s]*3
            v=rng.uniform(-.9999,.9999);t=rng.uniform(-.9999,.9999);rho=rng.uniform(-1,1);rad=math.sqrt((1-v*v)*(1-t*t));yield 'random_gram',[v*t+rho*rad,v,t]
            v=rng.uniform(-.9999,.9999);t=rng.uniform(-.9999,.9999);rad=math.sqrt((1-v*v)*(1-t*t));yield 'boundary_lower',[v*t-rad,v,t];yield 'boundary_upper',[v*t+rad,v,t];i+=1
    for family,point in samples():
        if monotonic()-begin>=55:break
        if max(point)>=1 or min(point)<-1:continue
        value,details=residual(A,c,point,0.0,1.0,math.sqrt);counts[family]+=1;record={'family':family,'point':point,'Rf_float':value,'gram_determinant_float':exact_gram(point),'max_dot':max(point),'outside_sharp_domain':max(point)>.56}
        if minimum is None or value<minimum['Rf_float']:minimum=record
        positive_max=value if positive_max is None else max(positive_max,value)
        if value<-.0001:
            check=confirm(A,c,point,family)
            if Decimal(check['Rf_decimal'])<Decimal('-.0001'):negative={**record,'confirmation':check};break
    result={'status':'DISCOVERY_EXPLICIT_NEGATIVE_VALLEY'if negative else'DISCOVERY_NO_CLEAR_NEGATIVE_FOUND_NO_PROOF','formula':'Rf=sum_i(1/sqrt(2-2dot_i)-F(1,dot_i,dot_i))-7F(u,v,t)-c; F=average over six coordinate permutations of sum_kab A[k][a][b]u^a v^b Qk','Q_recurrence':'Q0=1; Q1=t-uv; Qnext=2(t-uv)Q-(1-u^2)(1-v^2)Qprev','source_file':str(source),'source_sha256':sha256(raw).hexdigest(),'random_seed':20260807,'clear_negative_threshold':-.0001,'counts':counts,'total_samples':sum(counts.values()),'minimum_seen':minimum,'maximum_seen':positive_max,'negative_witness':negative,'elapsed_seconds':monotonic()-begin,'time_cap_seconds':60,'scope':'Discovery only using saved numerical original A/c with 90decimal confirmation of those numerical coefficients. Not an interval proof for the exact sharp kernel. If clear negative appears, do not attempt unrestricted certification; preserve the existing pair reduction.'}
    with (p/'unrestricted_domain_probe_result.json').open('x')as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps(result),flush=True)
if __name__=='__main__':main()
