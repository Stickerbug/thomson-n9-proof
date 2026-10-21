"""Independent 14-node confluent Hermite minorant and R_H coefficient binding."""
from pathlib import Path
from fractions import Fraction as Q
from hashlib import sha256
from time import monotonic
import json
from independent_integer_interval import Box,InvalidMath
ZERO=Box(0)
def need(ok,msg):
    if not ok:raise InvalidMath(msg)
def decode(x):return Box(Q(int(x['lo_numerator']),1<<int(x['denominator_power_of_two'])),Q(int(x['hi_numerator']),1<<int(x['denominator_power_of_two'])))
def f(x):return 1/(2-2*x).sqrt()
def fp(x):return f(x)/(2-2*x)
def hermite(nodes):
    need(len(nodes)==14,'expected14 distinct nodes');need(all(a.h<b.l for a,b in zip(nodes,nodes[1:])),'nodes must have disjoint ordered intervals');need(nodes[0].lo>=-1 and nodes[-1].hi<1,'node outside smooth domain')
    z=[x for x in nodes for _ in range(2)];rows=[];coeff=[];divisors=[]
    for i,x in enumerate(z):
        row=[f(x)]
        for order in range(1,i+1):
            if order==1 and i%2==1:row.append(fp(x))
            else:
                divisor=x-z[i-order];need(divisor.l>0,'different-node divided-difference denominator not strictly positive');row.append((row[order-1]-rows[i-1][order-1])/divisor);divisors.append({'i':i,'order':order,'interval':divisor.serial()})
        rows.append(row);coeff.append(row[i])
    power=[coeff[-1]]
    for j in reversed(range(len(coeff)-1)):
        new=[ZERO]*(len(power)+1)
        for degree,value in enumerate(power):new[degree]=new[degree]-z[j]*value;new[degree+1]=new[degree+1]+value
        new[0]=new[0]+coeff[j];power=new
    return z,rows,coeff,power,divisors
def main():
    start=monotonic();out=Path(__file__).resolve().parent;nraw=(out/'independent_kernel_refined_result.json').read_bytes();braw=(out/'independent_coefficient_binding_result.json').read_bytes();craw=(out.parent/'d10_relative_normal_exact2026_coefficients.json').read_bytes();ndata=json.loads(nraw);binding=json.loads(braw);co=json.loads(craw);need(binding['status']=='INDEPENDENT_N_CONTACT33_F_C_BINDING_PASS','F/c binding prerequisite failed');r=Box(*ndata['root_interval'])
    candidate=[r*r/2-1,-r,Box(Q(-1,2)),2*r*r-1,1-Q(3,2)*r*r,r/2];extra=[Q(-1),Q(-9,10),Q(-2,5),Q(-1,5),Q(1,10),Q(9,20),Q(13,25),Q(14,25)];nodes=sorted(candidate+[Box(x)for x in extra],key=lambda x:x.l);z,table,newton,H,denoms=hermite(nodes);need(len(H)==28,'wrong Hermite degree bound');Hexpected=[decode(v)for v in co['H_coefficients_ascending']];need(len(Hexpected)==28,'wrong original H coefficient count');Houtside=[{'degree':j,'new':v.serial(),'old':w.serial()}for j,(v,w)in enumerate(zip(H,Hexpected))if not(w.lo<=v.lo<=v.hi<=w.hi)]
    F={tuple(e):Box(*v)for e,v in binding['F_coefficients']};constant=Box(*binding['c']);R={}
    def add(e,v):R[e]=R.get(e,ZERO)+v
    for axis in range(3):
        for degree,v in enumerate(H):e=[0]*3;e[axis]=degree;add(tuple(e),v)
    for e,v in F.items():
        add(e,-7*v)
        for axis in range(3):target=[0]*3;target[axis]=e[1]+e[2];add(tuple(target),-v)
    add((0,0,0),-constant);expected={tuple(e):decode(v)for e,v in co['R_coefficients']};missing=sorted(set(expected)-set(R));extraR=sorted(set(R)-set(expected));Routside=[]
    for e,v in R.items():
        if e in expected:
            w=expected[e]
            if not(w.lo<=v.lo<=v.hi<=w.hi):Routside.append({'exponent':list(e),'new':v.serial(),'old':w.serial()})
    passed=not Houtside and not Routside and not missing and not extraR
    result={'status':'INDEPENDENT_H27_RH_BINDING_PASS'if passed else'INDEPENDENT_H27_RH_ENCLOSURE_INCLUSION_FAILED','bits':640,'root_interval':ndata['root_interval'],'supplementary_nodes':list(map(str,extra)),'distinct_nodes':[v.serial()for v in nodes],'newton_nodes':[v.serial()for v in z],'newton_coefficients':[v.serial()for v in newton],'full_confluent_table':[[v.serial()for v in row]for row in table],'strict_different_node_divisors':denoms,'H_coefficients_ascending':[v.serial()for v in H],'H_outside_original':Houtside,'all28_H_inside_original':not Houtside,'R_coefficients':[[list(e),v.serial()]for e,v in sorted(R.items())],'R_count':len(R),'expected_R_count':len(expected),'R_outside_original':Routside,'missing_exponents':missing,'extra_exponents':extraR,'all_R_inside_original':not Routside and not missing and not extraR,'interpolation_exactness':'For each fixed true r, distinct nodes and their repeated f/fprime data uniquely define Hermite H of degree at most27. Confluent divided-difference theorem proves exact H(node)=f(node), Hprime(node)=fprime(node); no zero-containing interval residual is promoted to equality.','minorant_lemma':'For any t in [-1,1), Hermite remainder f(t)-H(t)=f^(28)(xi)/28! * product14(t-node_i)^2, with xi in hull of t and nodes. f^(28)(xi)=55!!*(2-2*xi)^(-57/2)>0, so H(t)<=f(t). All nodes lie in [-1,1). This real-calculus theorem is stated, not Lean formalized.','R_definition':'sum_axes H(x_axis)-7F(u,v,t)-F(1,u,u)-F(1,v,v)-F(1,t,t)-c','source_sha256':{'independent_kernel_refined_result.json':sha256(nraw).hexdigest(),'independent_coefficient_binding_result.json':sha256(braw).hexdigest(),'d10_relative_normal_exact2026_coefficients.json':sha256(craw).hexdigest()},'elapsed_seconds':monotonic()-start,'scope':'Independent H27 and R_H coefficient construction with enclosure containment; no uniform error bound or K-factor check, no local nonnegativity or global tree witness proof.'}
    with (out/'independent_hermite_RH_result.json').open('x')as stream:json.dump(result,stream,indent=2);stream.write('\n')
    print(json.dumps({k:v for k,v in result.items()if k not in ['distinct_nodes','newton_nodes','newton_coefficients','full_confluent_table','strict_different_node_divisors','H_coefficients_ascending','R_coefficients','H_outside_original','R_outside_original']}),flush=True)
if __name__=='__main__':main()
