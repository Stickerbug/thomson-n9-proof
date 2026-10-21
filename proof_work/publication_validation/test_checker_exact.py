"""Deterministic mathematical and deliberately invalid-certificate tests."""
import copy,json,tempfile
from pathlib import Path
from fractions import Fraction as Q
from math import comb
import checker_exact as C

def evaluate(b,u):
    n=len(b)-1
    return sum(v*comb(n,i)*u**i*(1-u)**(n-i) for i,v in enumerate(b))
def fixture():
    return dict(bits=32,delta='0',F_mid_sym=[[[0,0,0],'0']],epsF='0',c_interval=['-100','-100'],local_regions=[],boundary_multipliers=[])
def node(path='',side=None):
    box=C.ROOT;lv=[0,0,0];ix=[0,0,0]
    if side is not None:
        bb=list(box);l,r=bb[0];mid=(l+r)/2;bb[0]=(l,mid) if side==0 else (mid,r);box=tuple(bb);lv[0]=1;ix[0]=side
    return dict(type='leaf',path=path,box=[[str(l),str(r)] for l,r in box],levels=lv,indices=ix,kind='positive',ident=None,witness=None)
def main():
    tests=[]
    def record(name,fn):fn();tests.append(name)
    def algebra():
        for degree in range(1,8):
            poly={(k,):Q((-1)**k*(k+2),k+1) for k in range(degree+1)};box=((Q(-3,4),Q(2,3)),);b=C.bern(poly,box,(degree,))
            for u in (Q(0),Q(1,7),Q(1,2),Q(1)):
                x=box[0][0]+u*(box[0][1]-box[0][0]);assert evaluate(b,u)==sum(v*x**k for (k,),v in poly.items())
        for n in range(1,12):
            line=tuple((-1)**i*((1<<170)+i*i+3) for i in range(n+1));lo=C.split_line(line);hi=C.split_line(line,True)
            for side in (0,1):
                exact=C.bern({(k,):comb(n,k)*sum((-1)**(k-j)*comb(k,j)*line[j] for j in range(k+1)) for k in range(n+1)},((Q(side,2),Q(side+1,2)),),(n,))
                assert all(a<=v<=b for a,v,b in zip(lo[side],exact,hi[side]))
                assert all(b-a<=1 for a,b in zip(lo[side],hi[side]))
        poly={(2,0,0):Q(2,3),(0,1,1):Q(-7,5),(0,0,0):Q(1)};box=((Q(-1),Q(1)),)*3;b=C.bern(poly,box,(2,2,2))
        for axis in range(3):
            lo=C.split_tensor(tuple(C.fl(v*1024) for v in b),axis,(2,2,2));hi=C.split_tensor(tuple(C.ce(v*1024) for v in b),axis,(2,2,2),True)
            for side in (0,1):
                bb=list(box);bb[axis]=(Q(-1),Q(0)) if side==0 else (Q(0),Q(1));direct=C.bern(poly,tuple(bb),(2,2,2));assert all(a<=v*1024<=z for a,v,z in zip(lo[side],direct,hi[side]))
    record('exact affine transform and closed subdivisions including 170-bit integers',algebra)
    def hbounds():
        inp=fixture();inp['F_mid_sym']=[[[10,10,0],'1/1000'],[[10,0,10],'1/1000'],[[0,10,10],'1/1000']];m=C.Math(inp)
        for lev,idx in ((0,0),(1,0),(1,1),(4,9),(8,255)):
            h=m.H(lev,idx);l=Q(-1)+Q(39,25)*Q(idx,1<<lev);r=l+Q(39,25*(1<<lev))
            for u in (Q(0),Q(1,7),Q(1,2),Q(1)):
                t=l+(r-l)*u;d=sum(v*t**k for k,v in m.dm.items());bound=evaluate(h,u)/m.S+d
                assert bound<0 or bound*bound*(2-2*t)<=1
    record('rigorous f-minus-d bounds with degree20 positive-tail handling',hbounds)
    with tempfile.TemporaryDirectory() as td:
        a=Path(td)/'inputs.json';b=Path(td)/'tree.jsonl'
        def check(inp,nodes):
            a.write_text(json.dumps(inp));b.write_text(''.join(json.dumps(n)+chr(10) for n in nodes));return C.verify(a,b,progress=0)
        good=fixture();root=node();split=copy.deepcopy(root);split.pop('kind');split['type']='split';split['axis']=0;full=[split,node('0',0),node('1',1)]
        assert check(good,[root])['nodes']==1;assert check(good,full)['nodes']==3;tests.append('valid root and full binary fixtures')
        def reject(name,inp,nodes,fragment):
            try:check(inp,nodes)
            except C.Invalid as e:assert fragment in str(e),(name,str(e));tests.append(name);return
            raise AssertionError('accepted known invalid fixture: '+name)
        reject('missing right child',good,full[:-1],'uncovered')
        reject('missing interior child',good,[split,node('1',1)],'tree gap')
        reject('duplicate root',good,[root,root],'extra node')
        n=copy.deepcopy(root);n['type']='pending';reject('illegal pending termination',good,[n],'illegal termination')
        n=copy.deepcopy(root);n['kind']='invented';reject('unknown leaf reason',good,[n],'invalid leaf')
        inp=copy.deepcopy(good);inp['delta']='1/12';reject('wrong nonzero delta',inp,[root],'delta')
        n=copy.deepcopy(root);n['box'][0][1]='1/2';reject('wrong root domain',good,[n],'box geometry')
        n=copy.deepcopy(full);n[1]['indices'][0]=1;reject('wrong dyadic index',good,n,'dyadic geometry')
        inp=copy.deepcopy(good);inp['K_root_floor']=['0']*1331;reject('known inconsistent root tensor',inp,[root],'K_root_floor')
        inp=copy.deepcopy(good);inp['c_interval']=['100','100'];reject('known false positive leaf',inp,[root],'invalid leaf')
        n=copy.deepcopy(root);n['kind']='gram_negative';reject('known false Gram exclusion',good,[n],'invalid leaf')
        inp=copy.deepcopy(good);inp['local_regions']=[dict(id='L',center=[['0','0']]*3,halfwidth='2',core=[['-2','2']]*3)];n=copy.deepcopy(root);n['kind']='local_region';n['ident']='L';assert check(inp,[n])['nodes']==1;tests.append('explicit conditional local core')
        inp['local_regions'][0]['core'][0][1]='3';reject('forged local core',inp,[n],'core mismatch')
        inp['local_regions'][0]['core']=[['-1/10','1/10']]*3;inp['local_regions'][0]['halfwidth']='1/10';reject('local leaf outside core',inp,[n],'invalid leaf')
        inp=copy.deepcopy(good);inp['epsF']='-1';reject('negative enclosure radius',inp,[root],'negative epsF')
    result={'status':'PASS','test_groups':tests,'count':len(tests),'mutation_policy':'All negative cases have known structural or mathematical invalidity; arbitrary integer changes are not presumed invalid.'}
    Path(__file__).with_name('independent_selftests.json').write_text(json.dumps(result,indent=2)+chr(10));print(json.dumps(result))
if __name__=='__main__':main()
