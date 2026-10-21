"""Independent rational pair reduction; standard library only, no legacy imports."""
from fractions import Fraction as Q
from math import factorial, comb
from pathlib import Path
from hashlib import sha256
from copy import deepcopy
from time import monotonic
import json
U=Q('25.75998653126983156407570227376049402866')
THRESHOLD=Q(14,25)
class InvalidMath(ValueError):pass
def require(test,msg):
    if not test:raise InvalidMath(msg)
def legendre(n):
    out=[Q(0)]*(n+1)
    for k in range(n//2+1):
        out[n-2*k]=Q((-1)**k*factorial(2*n-2*k),2**n*factorial(k)*factorial(n-k)*factorial(n-2*k))
    return out
def polynomial(a):
    out=[Q(0)]*len(a)
    for n,v in enumerate(a):
        if v:
            for j,c in enumerate(legendre(n)):out[j]+=v*c
    while len(out)>1 and out[-1]==0:out.pop()
    return out
def squared_condition(p):
    out=[Q(0)]*(2*len(p));out[0]=1
    for i,x in enumerate(p):
        for j,y in enumerate(p):out[i+j]-=2*x*y;out[i+j+1]+=2*x*y
    while len(out)>1 and out[-1]==0:out.pop()
    return out
def bernstein(poly,lo,hi):
    # Direct coefficient formula after x=lo+(hi-lo)s; no recurrence.
    n=len(poly)-1
    power=[sum((poly[j]*comb(j,k)*lo**(j-k)*(hi-lo)**k for j in range(k,n+1)),Q(0))for k in range(n+1)]
    return [sum((power[k]*Q(comb(i,k),comb(n,k))for k in range(i+1)),Q(0))for i in range(n+1)]
def halves(b):
    # Closed binomial midpoint restriction; no de Casteljau iteration.
    n=len(b)-1
    left=[sum((comb(i,j)*b[j]for j in range(i+1)),Q(0))/2**i for i in range(n+1)]
    right=[sum((comb(n-i,j)*b[i+j]for j in range(n-i+1)),Q(0))/2**(n-i)for i in range(n+1)]
    return left,right
def value(poly,x):
    return sum((c*x**j for j,c in enumerate(poly)),Q(0))
def make_tree(poly,lo,hi,strict):
    nodes=[];stack=[('',lo,hi,bernstein(poly,lo,hi))]
    while stack:
        path,l,h,b=stack.pop();m=min(b)
        require(value(poly,l)>=0 and value(poly,h)>=0,'exact polynomial endpoint is negative')
        if m>0 if strict else m>=0:
            nodes.append({'type':'leaf','path':path,'box':[str(l),str(h)],'minimum':str(m)});continue
        require(len(path)<40 and len(nodes)<200000,'unproved pending frontier: refusing incomplete certificate')
        nodes.append({'type':'split','path':path,'box':[str(l),str(h)],'axis':0})
        left,right=halves(b);mid=(l+h)/2
        stack.extend([(path+'1',mid,h,right),(path+'0',l,mid,left)])
    return {'domain':[str(lo),str(hi)],'strict':strict,'polynomial':list(map(str,poly)),'root_bernstein':list(map(str,bernstein(poly,lo,hi))),'nodes':nodes}
def verify_tree(tree):
    poly=list(map(Q,tree['polynomial']));lo,hi=map(Q,tree['domain']);strict=tree['strict']
    require(type(strict)is bool,'strict flag must be boolean')
    root=bernstein(poly,lo,hi);require(list(map(str,root))==tree['root_bernstein'],'wrong root Bernstein coefficients')
    by={}
    for n in tree['nodes']:
        require(n['path'] not in by,'duplicate path');by[n['path']]=n
    stack=[('',lo,hi,root)];seen=set();leaves=0
    while stack:
        path,l,h,b=stack.pop();require(path in by,'missing child: coverage invalid');n=by[path];seen.add(path)
        require(list(map(Q,n['box']))==[l,h],'wrong exact node box')
        if n['type']=='leaf':
            m=min(b);require(Q(n['minimum'])==m,'wrong leaf witness');require(m>0 if strict else m>=0,'Bernstein sign condition invalid');leaves+=1
        else:
            require(n['type']=='split','pending or unknown node cannot prove coverage');require(n['axis']==0,'wrong split axis')
            left,right=halves(b);mid=(l+h)/2;stack.extend([(path+'1',mid,h,right),(path+'0',l,mid,left)])
    require(seen==set(by),'unreachable nodes');return {'nodes':len(seen),'leaves':leaves,'maxdepth':max(map(len,seen)),'pending':0}
def check_inputs(data,delta=Q(0),threshold=THRESHOLD):
    require(type(delta)is Q and delta==0,'nonsharp delta rejected');require(type(threshold)is Q and threshold==THRESHOLD,'wrong sharp domain threshold')
    a=[Q(x)for x in data['legendre_coefficients']]
    require(len(a)>0 and all(x>=0 for x in a[1:]),'negative Legendre LP coefficient')
    B=36*a[0]-Q(9,2)*sum(a[1:]);gap=U-B
    require(Q(data['U'])==U,'candidate upper U must equal fixed rational literal')
    require(Q(data['LP_bound'])==B,'LP bound inconsistent with rational coefficients')
    require(gap>0,'candidate gap is not positive');require(Q(data['gap'])==gap,'gap differs from fixed U minus recomputed B')
    return a,B,gap
def main():
    start=monotonic();out=Path(__file__).resolve().parent;source=out.parent/'pair056_optimized_certificate.json';raw=source.read_bytes();d=json.loads(raw)
    a,B,gap=check_inputs(d);p=polynomial(a);q=p.copy();q[0]+=gap
    minorant=make_tree(squared_condition(p),Q(-1),Q(1),False);exclusion=make_tree(squared_condition(q),THRESHOLD,Q(1),True)
    checks={'minorant':verify_tree(minorant),'exclusion':verify_tree(exclusion)};negative=[]
    def reject(name,fn):
        try:fn()
        except InvalidMath as e:negative.append({'case':name,'status':'REJECTED_MATHEMATICALLY','reason':str(e)});return
        raise AssertionError('invalid case accepted: '+name)
    bad=deepcopy(d);bad['legendre_coefficients'][1]='-1';reject('negative_LP_coefficient',lambda:check_inputs(bad))
    broken=polynomial(a);broken[0]+=2
    reject('corrupted_polynomial_exact_endpoint',lambda:make_tree(squared_condition(broken),Q(-1),Q(1),False))
    badgap=deepcopy(d);badgap['gap']=str(gap/2);reject('wrong_positive_gap',lambda:check_inputs(badgap))
    missing=deepcopy(minorant);missing['nodes']=[n for n in missing['nodes']if n['path']!=next(x['path']for x in missing['nodes']if x['type']=='leaf')];reject('missing_coverage_leaf',lambda:verify_tree(missing))
    pending=deepcopy(exclusion);pending['nodes'][0]['type']='pending';reject('pending_frontier',lambda:verify_tree(pending))
    reject('nonsharp_delta',lambda:check_inputs(d,delta=Q(1,1000)))
    reject('wrong_threshold',lambda:check_inputs(d,threshold=Q(1,2)))
    result={'status':'INDEPENDENT_PAIR_REDUCTION_PASS','conditional_only':True,'premises':['Legendre addition theorem: M_l=sum_ij P_l(dot_ij)>=0','fixed rational U is a rigorous strict upper bound for an admissible nine-point candidate','nine distinct unit vectors, E=sum_i<j (2-2dot_ij)^(-1/2)'],'fixed_U':str(U),'B':str(B),'gap':str(gap),'threshold':str(THRESHOLD),'delta':'0','legendre_coefficients':list(map(str,a)),'monomial_p':list(map(str,p)),'coverage':checks,'negative_tests':negative,'source_sha256':sha256(raw).hexdigest(),'checker_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'elapsed_seconds':monotonic()-start}
    for name,obj in [('independent_pair_reduction_trees.json',{'minorant':minorant,'exclusion':exclusion}),('independent_pair_reduction_result.json',result)]:
        with (out/name).open('x')as f:json.dump(obj,f,indent=2);f.write('\n')
    print(json.dumps(result,default=str),flush=True)
if __name__=='__main__':main()
