"""Independent 640-bit outward intervals and exact symbolic nine-point enumeration."""
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
from hashlib import sha256
from collections import Counter
from time import monotonic
import json
BITS=640
S=1<<BITS
FIXED_U=Q('25.75998653126983156407570227376049402866')
AUDIT=[]
class InvalidMath(ValueError):pass
def need(ok,msg):
    if not ok:raise InvalidMath(msg)
def floorq(x):return x.numerator//x.denominator
def ceilq(x):return -((-x.numerator)//x.denominator)
class Box:
    def __init__(self,lo,hi=None):
        lo=Q(lo);hi=lo if hi is None else Q(hi);need(lo<=hi,'reversed interval')
        self.lo=Q(floorq(lo*S),S);self.hi=Q(ceilq(hi*S),S)
        need(self.lo<=lo<=hi<=self.hi,'outward rounding failed')
    @staticmethod
    def cast(x):return x if isinstance(x,Box)else Box(x)
    def __add__(self,x):
        x=self.cast(x);return Box(self.lo+x.lo,self.hi+x.hi)
    __radd__=__add__
    def __neg__(self):return Box(-self.hi,-self.lo)
    def __sub__(self,x):return self+-self.cast(x)
    def __rsub__(self,x):return self.cast(x)+-self
    def __mul__(self,x):
        x=self.cast(x);v=[a*b for a in (self.lo,self.hi)for b in (x.lo,x.hi)];return Box(min(v),max(v))
    __rmul__=__mul__
    def reciprocal(self):
        need(not self.lo<=0<=self.hi,'reciprocal interval crosses zero');return Box(1/self.hi,1/self.lo)
    def __truediv__(self,x):return self*self.cast(x).reciprocal()
    def __rtruediv__(self,x):return self.cast(x)*self.reciprocal()
    def __pow__(self,n):
        need(type(n)is int and n>=0,'nonnegative integer power required');v=Box(1)
        for _ in range(n):v=v*self
        return v
    def sqrt(self):
        need(self.lo>=0,'sqrt input negative')
        l=isqrt(floorq(self.lo*S*S));h=isqrt(floorq(self.hi*S*S))
        if Q(h*h,S*S)<self.hi:h+=1
        ans=Box(Q(l,S),Q(h,S));validate_sqrt(self,ans)
        AUDIT.append({'input':self.serial(),'sqrt':ans.serial()});return ans
    def serial(self):return [str(self.lo),str(self.hi)]
def validate_sqrt(x,y):
    need(0<=y.lo<=y.hi and y.lo*y.lo<=x.lo and y.hi*y.hi>=x.hi,'sqrt enclosure fails exact squared endpoint inequalities')
def energy(r):
    return Box(3).sqrt()+2*Box(3).sqrt()/r+Q(3,2)/(1-r*r).sqrt()+6/(4-r*r).sqrt()+12/(2-r).sqrt()+6/(2+2*r).sqrt()
def derivative(r):
    return -2*Box(3).sqrt()/(r*r)+Q(3,2)*r/((1-r*r)*(1-r*r).sqrt())+6*r/((4-r*r)*(4-r*r).sqrt())+6/((2-r)*(2-r).sqrt())-6/((2+2*r)*(2+2*r).sqrt())
def verify_candidate(lo,hi,upper=FIXED_U):
    need(Q(0)<lo<hi<Q(1),'root bracket must be strictly ordered inside (0,1)')
    left=derivative(Box(lo));right=derivative(Box(hi));E=energy(Box(lo,hi))
    need(left.hi<0,'left derivative is not strictly negative');need(right.lo>0,'right derivative is not strictly positive');need(E.hi<upper,'candidate energy upper bound is not below U')
    return {'left_derivative':left.serial(),'right_derivative':right.serial(),'energy':E.serial(),'U_minus_energy_upper':str(upper-E.hi)}
def algmul(x,y):return (x[0]*y[0]+3*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def enumerate_pairs():
    # planar coordinates are rational + rational*sqrt(3); radial exponent 0 or 1.
    Z=Q(0);H=Q(1,2)
    triangle=[((Q(1),Z),(Z,Z)),((-H,Z),(Z,H)),((-H,Z),(Z,-H))]
    equator=[((H,Z),(Z,H)),((Q(-1),Z),(Z,Z)),((H,Z),(Z,-H))]
    points=[{'id':f'{name}{k}','xy':xy,'radial_power':power,'height_sign':sign}for name,plan,power,sign in [('upper',triangle,1,1),('lower',triangle,1,-1),('equator',equator,0,0)]for k,xy in enumerate(plan)]
    def dot(a,b):
        ax=algmul(a['xy'][0],b['xy'][0]);ay=algmul(a['xy'][1],b['xy'][1]);need(ax[1]+ay[1]==0,'uncancelled sqrt3 coefficient')
        poly=[Z,Z,Z];poly[a['radial_power']+b['radial_power']]+=ax[0]+ay[0]
        z=a['height_sign']*b['height_sign'];poly[0]+=z;poly[2]-=z;return tuple(poly)
    for a in points:need(dot(a,a)==(Q(1),Z,Z),'symbolic point is not unit')
    labels={(Q(1),Z,-Q(3,2)):'1-3r^2/2',(Q(-1),Z,Q(2)):'2r^2-1',(Q(-1),Z,H):'r^2/2-1',(-H,Z,Z):'-1/2',(Z,H,Z):'r/2',(Z,Q(-1),Z):'-r'}
    pairs=[];counts=Counter()
    for i,a in enumerate(points):
        for b in points[i+1:]:
            v=dot(a,b);need(v in labels,'unexpected symbolic dot');name=labels[v];counts[name]+=1;pairs.append({'i':a['id'],'j':b['id'],'dot':name,'coefficients_constant_r_r2':list(map(str,v))})
    expected={'1-3r^2/2':6,'2r^2-1':3,'r^2/2-1':6,'-1/2':3,'r/2':12,'-r':6}
    need(dict(counts)==expected and len(pairs)==36,'wrong exact pair counts')
    terms=[{'dot':name,'count':counts[name],'distance_squared_coefficients':list(map(str,(2-2*v[0],-2*v[1],-2*v[2])))}for v,name in labels.items()]
    # Positive radical prefactors are fixed by these exact square identities.
    normalizations=[('1-3r^2/2',(Q(0),Q(0),Q(3)),Q(3),Q(12)),('2r^2-1',(Q(4),Q(0),Q(-4)),Q(4),Q(9,4)),('r^2/2-1',(Q(4),Q(0),Q(-1)),Q(1),Q(36)),('-1/2',(Q(3),Q(0),Q(0)),Q(3),Q(3)),('r/2',(Q(2),Q(-1),Q(0)),Q(1),Q(144)),('-r',(Q(2),Q(2),Q(0)),Q(1),Q(36))]
    for name,distance,scale,prefactor_squared in normalizations:
        term=next(t for t in terms if t['dot']==name)
        need(tuple(map(Q,term['distance_squared_coefficients']))==distance,'wrong family distance polynomial')
        need(prefactor_squared*scale==counts[name]**2,'family energy prefactor does not match pair count')
    return {'points':[{'id':a['id'],'xy_Qsqrt3':[[str(c)for c in x]for x in a['xy']],'radial_power':a['radial_power'],'height_sign':a['height_sign']}for a in points],'pairs':pairs,'counts':dict(counts),'energy_terms':terms,'all_norms_symbolically_one':True,'energy_closed_form':'sqrt(3)+2sqrt(3)/r+(3/2)/sqrt(1-r^2)+6/sqrt(4-r^2)+12/sqrt(2-r)+6/sqrt(2+2r)'}
def main():
    start=monotonic();out=Path(__file__).resolve().parent;source=out.parent/'d10_relative_normal_exact2026_certificate.json';raw=source.read_bytes();lo,hi=map(Q,json.loads(raw)['root_interval'])
    proof=verify_candidate(lo,hi);pairs=enumerate_pairs();positive_audit=len(AUDIT);negative=[]
    def reject(name,fn):
        try:fn()
        except InvalidMath as e:negative.append({'case':name,'status':'REJECTED_MATHEMATICALLY','reason':str(e)});return
        raise AssertionError('invalid case accepted '+name)
    reject('reversed_root_interval',lambda:verify_candidate(hi,lo));reject('reciprocal_crosses_zero',lambda:Box(-1,1).reciprocal())
    x=Box(2);bad=isqrt(2*S*S);reject('sqrt_upper_rounded_down',lambda:validate_sqrt(x,Box(Q(bad,S),Q(bad,S))))
    reject('wrong_U_below_energy',lambda:verify_candidate(lo,hi,Q(25)))
    result={'status':'INDEPENDENT_CANDIDATE_BOUNDS_PASS','bits':BITS,'root_interval':list(map(str,[lo,hi])),'fixed_U':str(FIXED_U),**proof,'positive_sqrt_operations':positive_audit,'sqrt_audit':AUDIT[:positive_audit],'pair_enumeration':pairs,'negative_tests':negative,'source_sha256':sha256(raw).hexdigest(),'checker_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'calculus_premise':'Esecond strictly positive on (0,1), IVT and strict convexity imply exactly one stationary r_star in bracket; not Lean formalized','elapsed_seconds':monotonic()-start}
    with (out/'independent_candidate_bounds_result.json').open('x')as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps({k:v for k,v in result.items()if k not in ['sqrt_audit','pair_enumeration']}),flush=True)
if __name__=='__main__':main()
