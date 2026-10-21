"""Independent arbitrary precision conditional coverage checker; standard library only."""
from fractions import Fraction as Q
from math import comb,isqrt
from itertools import product,permutations
from functools import lru_cache
from pathlib import Path
from hashlib import sha256
import json,time,argparse
ROOT=((Q(-1),Q(14,25)),)*3
GRAM={(0,0,0):Q(1),(1,1,1):Q(2),(2,0,0):Q(-1),(0,2,0):Q(-1),(0,0,2):Q(-1)}
class Invalid(ValueError):pass
def need(ok,msg):
    if not ok:raise Invalid(msg)
def rat(v):
    need(type(v) in (str,int,Q),'exact rational required');return Q(v)
def fl(v):return v.numerator//v.denominator
def ce(v):return -((-v.numerator)//v.denominator)
def bern(poly,box,degree):
    data=dict(poly)
    for axis,n in enumerate(degree):
        l,r=box[axis];w=r-l
        mat=[[sum((Q(comb(k,j)*comb(i,j),comb(n,j))*l**(k-j)*w**j for j in range(min(i,k)+1)),Q(0)) for k in range(n+1)] for i in range(n+1)]
        out={}
        for p,v in data.items():
            need(p[axis]<=n,'degree overflow')
            for i in range(n+1):
                a=mat[i][p[axis]]
                if a:
                    pp=p[:axis]+(i,)+p[axis+1:];out[pp]=out.get(pp,Q(0))+v*a
        data=out
    return tuple(data.get(p,Q(0)) for p in product(*(range(n+1) for n in degree)))
@lru_cache(None)
def weights(n):return tuple(tuple(comb(i,j) for j in range(i+1)) for i in range(n+1)),tuple(tuple(comb(n-i,j-i) for j in range(i,n+1)) for i in range(n+1))
def split_line(line,upper=False):
    n=len(line)-1;a,b=weights(n);rnd=(lambda x,d:-((-x)//d)) if upper else (lambda x,d:x//d)
    return tuple(rnd(sum(c*line[j] for j,c in enumerate(a[i])),1<<i) for i in range(n+1)),tuple(rnd(sum(c*line[i+j] for j,c in enumerate(b[i])),1<<(n-i)) for i in range(n+1))
def split_tensor(v,axis,degree=(10,10,10),upper=False):
    shape=tuple(n+1 for n in degree);stride=1
    for s in shape[axis+1:]:stride*=s
    block=stride*shape[axis];aa=[0]*len(v);bb=[0]*len(v)
    for base in range(0,len(v),block):
        for off in range(stride):
            pos=range(base+off,base+off+block,stride);a,b=split_line(tuple(v[p] for p in pos),upper)
            for p,x,y in zip(pos,a,b):aa[p]=x;bb[p]=y
    return tuple(aa),tuple(bb)
class Math:
    def __init__(self,inp):
        need(type(inp['bits']) is int and 1<=inp['bits']<=4096,'invalid bits');self.S=1<<inp['bits'];need(rat(inp['delta'])==0,'sharp certificate requires delta = 0');self.fm={}
        for p,v in inp['F_mid_sym']:
            need(len(p)==3 and all(type(k) is int and 0<=k<=10 for k in p),'invalid exponent');need(tuple(p) not in self.fm,'duplicate F exponent');self.fm[tuple(p)]=rat(v)
        for p,v in self.fm.items():need(all(self.fm.get(tuple(p[i] for i in pm),Q(0))==v for pm in permutations(range(3))),'F not symmetric')
        eps=rat(inp['epsF']);need(eps>=0,'negative epsF');clo,chi=map(rat,inp['c_interval']);need(clo<=chi,'reversed c interval');self.k={p:-7*v for p,v in self.fm.items()};self.k[(0,0,0)]=self.k.get((0,0,0),Q(0))-chi-10*eps;self.dm={}
        for (i,j,k),v in self.fm.items():self.dm[j+k]=self.dm.get(j+k,Q(0))+v
        self.root=tuple(fl(v*self.S) for v in bern(self.k,ROOT,(10,10,10)))
        for key,actual in [('K_monomial',self.k),('d_mid',self.dm)]:
            if key in inp:
                got={(tuple(p) if key=='K_monomial' else int(p)):rat(v) for p,v in inp[key]};need(all(got.get(p,0)==actual.get(p,0) for p in got.keys()|actual.keys()),'root polynomial mismatch: '+key)
        for name,actual in [('K_root_floor',self.root),('D_root_ceil',self.D(0,0)),('Gram_root_ceil',tuple(ce(v*self.S) for v in bern(GRAM,ROOT,(2,2,2))))]:
            if name in inp:need(tuple(map(int,inp[name]))==actual,'root input mismatch: '+name)
        if 'K_shape' in inp:need(inp['K_shape']==[11]*3,'K shape')
        if 'Gram_shape' in inp:need(inp['Gram_shape']==[3]*3,'Gram shape')
        self.local={};self.boundary={}
        for reg in inp['local_regions']:
            ident=str(reg['id']);need(ident not in self.local,'duplicate local id');center=self.center(reg['center']);w=rat(reg['halfwidth']);need(w>=0,'negative local width');core=tuple((hi-w,lo+w) for lo,hi in center)
            if 'core' in reg:need(tuple(tuple(map(rat,z)) for z in reg['core'])==core,'local core mismatch')
            self.local[ident]=core
        for reg in inp['boundary_multipliers']:
            ident=str(reg['id']);need(ident not in self.boundary,'duplicate boundary id');self.center(reg['centerI']);lam=rat(reg['lambda']);need(lam>=0,'negative lambda');self.boundary[ident]=lam
    @staticmethod
    def center(c):
        need(len(c)==3,'center dimension');out=tuple(tuple(map(rat,p)) for p in c);need(all(len(p)==2 and p[0]<=p[1] for p in out),'invalid center');return out
    @lru_cache(None)
    def D(self,lev,idx):
        l=Q(-1)+Q(39,25)*Q(idx,1<<lev);r=l+Q(39,25*(1<<lev));return tuple(ce(v*self.S) for v in bern({(k,):v for k,v in self.dm.items()},((l,r),),(20,)))
    @lru_cache(None)
    def H(self,lev,idx):
        l=Q(-1)+Q(39,25)*Q(idx,1<<lev);r=l+Q(39,25*(1<<lev));a=(r-l)/(1-l);need(0<a<1,'Taylor domain');v=2-2*l;n=isqrt((v.denominator*self.S*self.S)//v.numerator);af=[n*comb(2*k,k)*a.numerator**k//(4**k*a.denominator**k) for k in range(11)];d=self.D(lev,idx);ad=[comb(20,k)*sum((-1)**(k-j)*comb(k,j)*d[j] for j in range(k+1)) for k in range(21)];q=[af[k]-ad[k] for k in range(11)];q[0]-=sum(max(v,0) for v in ad[11:]);return tuple(sum(q[k]*comb(i,k)*(2520//comb(10,k)) for k in range(i+1))//2520 for i in range(11))
    def positive(self,tensor,levels,indices,box,lam=Q(0)):
        hh=[self.H(l,i) for l,i in zip(levels,indices)];cor=tuple(ce(lam*self.S*v) for v in bern(GRAM,box,(10,10,10))) if lam else (0,)*1331;lo=min(v-c+hh[0][i]+hh[1][j]+hh[2][k] for (i,j,k),v,c in zip(product(range(11),repeat=3),tensor,cor))
        if lo<0:
            poly=dict(self.k)
            for p,v in GRAM.items():poly[p]=poly.get(p,Q(0))-lam*v
            direct=tuple(fl(v*self.S) for v in bern(poly,box,(10,10,10)));lo=min(v+hh[0][i]+hh[1][j]+hh[2][k] for (i,j,k),v in zip(product(range(11),repeat=3),direct))
        return lo

def verify(inputs,tree,expected_input_sha256=None,progress=5000):
    start=time.monotonic();raw=Path(inputs).read_bytes()
    if expected_input_sha256:need(sha256(raw).hexdigest()==expected_input_sha256,'input digest mismatch')
    m=Math(json.loads(raw));stack=[('',ROOT,(0,0,0),(0,0,0),m.root)];counts={};nodes=splits=0;th=sha256()
    with Path(tree).open('rb') as f:
        for line in f:
            th.update(line);need(bool(stack),'extra node after closed root');node=json.loads(line);path,box,lv,ix,tensor=stack.pop();nodes+=1;need(node['path']==path,'tree gap duplicate or non-preorder');need(node['levels']==list(lv) and node['indices']==list(ix),'incorrect dyadic geometry');need(tuple(tuple(map(rat,p)) for p in node['box'])==box,'incorrect box geometry')
            if node['type']=='split':
                axis=node['axis'];need(type(axis) is int and 0<=axis<3,'split axis');halves=split_tensor(tensor,axis);nl=list(lv);nl[axis]+=1
                for side in (1,0):
                    bb=list(box);l,r=box[axis];mid=(l+r)/2;bb[axis]=(l,mid) if side==0 else (mid,r);ni=list(ix);ni[axis]=2*ni[axis]+side;stack.append((path+str(side),tuple(bb),tuple(nl),tuple(ni),halves[side]))
                splits+=1
            else:
                need(node['type']=='leaf','illegal termination: '+str(node['type']));kind=node['kind'];ident=node.get('ident');ok=False
                if kind=='ordered_disjoint':ok=any(box[i][0]>box[j][1] for i in range(3) for j in range(i+1,3))
                elif kind=='gram_negative':ok=max(bern(GRAM,box,(2,2,2)))<0
                elif kind=='local_region':need(ident in m.local,'unknown local');ok=all(a<=l<=r<=b for (l,r),(a,b) in zip(box,m.local[ident]))
                elif kind in ('positive','boundary_multiplier'):
                    lam=Q(0)
                    if kind=='boundary_multiplier':need(ident in m.boundary,'unknown boundary');lam=m.boundary[ident]
                    ok=m.positive(tensor,lv,ix,box,lam)>=0
                need(ok,'invalid leaf reason '+str(kind)+' at '+path);counts[kind]=counts.get(kind,0)+1
            if progress and nodes%progress==0:print(json.dumps({'nodes':nodes,'pending':len(stack),'seconds':time.monotonic()-start}),flush=True)
    need(not stack,'uncovered pending domains');need(nodes==2*splits+1,'binary tree identity')
    return {'status':'VERIFIED_CONDITIONAL_COVERAGE','conditional_only':True,'nodes':nodes,'splits':splits,'leaves':sum(counts.values()),'leaf_counts':counts,'input_sha256':sha256(raw).hexdigest(),'tree_sha256':th.hexdigest(),'checker_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'elapsed_seconds':time.monotonic()-start,'premises':['symmetric F/c coefficient enclosures valid for intended model','same-model local nonnegativity: assumed, not independently checked','PSD and pair reduction: assumed, not independently checked'],'claim':'Conditional coverage, NOT a complete independent proof of the nine-point Thomson minimum.'}
def main():
    p=argparse.ArgumentParser();p.add_argument('--inputs',required=True);p.add_argument('--tree',required=True);p.add_argument('--output',required=True);p.add_argument('--expected-input-sha256');a=p.parse_args()
    try:r=verify(a.inputs,a.tree,a.expected_input_sha256)
    except (Invalid,KeyError,TypeError,ValueError,ZeroDivisionError) as e:
        r={'status':'REJECTED','error':str(e)};Path(a.output).write_text(json.dumps(r,indent=2)+chr(10));print(json.dumps(r),flush=True);raise SystemExit(1)
    Path(a.output).write_text(json.dumps(r,indent=2)+chr(10));print(json.dumps(r),flush=True)
if __name__=='__main__':main()
