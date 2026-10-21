"""Exact pair exclusion for all candidate-competitive N9 configurations."""
from certify_rational_lp import F,add,scale,mul,comb
from pathlib import Path
import json

def run():
    base=Path(__file__).parent
    a=list(map(F,json.loads((base/'rational_lp24.json').read_text())['legendre_coefficients']))
    Ps=[[F(1)],[F(0),F(1)]]
    for k in range(2,len(a)):
        Ps.append(scale(add(scale([F(0)]+Ps[-1],2*k-1),scale(Ps[-2],1-k)),F(1,k)))
    p=[F(0)]
    for c,P in zip(a,Ps):p=add(p,scale(P,c))
    B=36*a[0]-F(9,2)*sum(a[1:])
    upper=F('25.75998653126983156407570227376049402866')
    gap=upper-B
    q=add(p,[gap])
    R=add([F(1)],scale(mul([F(2),F(-2)],mul(q,q)),-1))
    lo=F(57,100);width=1-lo;n=len(R)-1
    power=[F(0)]*(n+1)
    for j,c in enumerate(R):
        for k in range(j+1):power[k]+=c*comb(j,k)*width**k*lo**(j-k)
    b=[sum((power[j]*F(comb(k,j),comb(n,j)) for j in range(k+1)),F(0))for k in range(n+1)]
    stack=[(b,0)];leaves=0;depthmax=0
    while stack:
        b,depth=stack.pop()
        if min(b)>0:
            leaves+=1;depthmax=max(depthmax,depth);continue
        assert max(b)>0 and depth<30
        rows=[b]
        for k in range(n):rows.append([(x+y)/2 for x,y in zip(rows[-1],rows[-1][1:])])
        stack.extend([([row[0]for row in rows],depth+1),([row[-1]for row in rows][::-1],depth+1)])
    result={'claim':'If E <= candidate energy upper enclosure, every off-diagonal dot product is <57/100; hence every pair distance is >sqrt(86/100).','candidate_energy_upper':str(upper),'global_bound':str(B),'gap_upper':str(gap),'proof':'Exact Bernstein R=1-(2-2t)(p+gap)^2>0 on [57/100,1]. Thus f-p>gap there. Defect sum is at most gap for a competitive configuration.','leaves':leaves,'max_depth':depthmax}
    out=base/'pair_exclusion_certificate.json'
    if out.exists():assert json.loads(out.read_text())==result
    else:out.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: strict polynomial inequality for all t in [0.57,1],',leaves,'Bernstein leaves; maxdepth',depthmax)
    print(result['claim'])

if __name__=='__main__':run()
