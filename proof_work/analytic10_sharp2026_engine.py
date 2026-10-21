"""Prepared SHARP conditional engine; no root is invoked on import.
Bits 80/96/104. Coarse H range overflow skips only a sufficient positive test;
physical boxes remain and split normally, or are covered by another sound terminal.
F/c/local/PSD inputs must belong to the SAME new model. Never reuse old local boxes.
"""
"""Conditional native signed128 Bernstein coverage of the symmetric Gram domain.

This module verifies only a polynomial interval and geometric coverage statement.
It does not establish coefficient enclosures, symmetry of the unknown true R,
local nonnegativity certificates, PSD, pair reduction, or any Thomson bound.
No CLI or resume interface is supplied.
"""
if not __debug__:
    raise RuntimeError('Conditional away replay requires assertions; do not use python -O.')
from fractions import Fraction
from hashlib import sha256
from itertools import permutations
from math import isfinite
from pathlib import Path
from time import monotonic
import json
import numpy as np
from exact_tensor_bernstein import coefficients
import exact128_2026 as native_backend
from exact128_2026 import NativeTensor

ROOT_BOX = ((Fraction(-1), Fraction(14, 25)),) * 3
GRAM = {(0, 0, 0): Fraction(1), (1, 1, 1): Fraction(2),
        (2, 0, 0): Fraction(-1), (0, 2, 0): Fraction(-1),
        (0, 0, 2): Fraction(-1)}


def _rational(value):
    if isinstance(value, (float, np.floating, bool)):
        raise TypeError('Exact rational input required; floating-point and bool inputs are rejected.')
    return Fraction(value)


def _center(value):
    if len(value) != 3:
        raise ValueError('center must contain three rational intervals')
    ans = tuple(tuple(_rational(z) for z in pair) for pair in value)
    if any(len(p) != 2 or p[0] > p[1] for p in ans):
        raise ValueError('invalid center interval')
    return ans


def split_outward(tensor, axis, upper=False):
    """Split same-scale signed128 tensor with EACH average rounded outward.

    The backend first checks strict abs(value)<2^124. Every average preserves
    that bound; the sum plus rounding flag safely fits signed128. Stepwise
    floor/ceil gives valid enclosures, potentially wider than rounding only the
    final exact binomial sum. No scale conversion or floating arithmetic occurs.
    """
    assert isinstance(tensor, NativeTensor)
    return tensor.split(axis, upper=upper)


def _normalize(poly_intervals, local_regions, boundary_multipliers):
    poly = {}
    for powers, interval in poly_intervals.items():
        if len(powers) != 3 or any(type(n) is not int or n < 0 for n in powers):
            raise ValueError('powers must be triples of nonnegative Python integers')
        if len(interval) != 2:
            raise ValueError('each coefficient requires a lower and an upper endpoint')
        lo, hi = map(_rational, interval)
        if lo > hi:
            raise ValueError('coefficient interval is reversed')
        poly[tuple(powers)] = (lo, hi)
    local = []
    for i, region in enumerate(local_regions):
        center = _center(region['center'])
        width = _rational(region['halfwidth'])
        if width < 0:
            raise ValueError('local halfwidth must be nonnegative')
        # Intersection of the cubes for ALL possible exact centers; never midpoint +/- delta.
        core = tuple((hi - width, lo + width) for lo, hi in center)
        local.append({'id': str(region.get('id', i)), 'center': center,
                      'halfwidth': width, 'core': core})
    boundary = []
    for i, item in enumerate(boundary_multipliers):
        center = _center(item['centerI'])
        lam = _rational(item['lambda'])
        assert lam >= 0, 'boundary lambda must be nonnegative'
        radius = _rational(item.get('activation_radius', Fraction(1, 20)))
        if radius < 0:
            raise ValueError('activation radius must be nonnegative')
        activation = tuple((lo - radius, hi + radius) for lo, hi in center)
        boundary.append({'id': str(item.get('id', i)), 'centerI': center,
                         'lambda': lam, 'activation_radius': radius,
                         'activation': activation})
    return poly, local, boundary


def _serial(obj):
    if isinstance(obj, Fraction):
        return str(obj)
    if isinstance(obj, dict):
        return {str(k): _serial(v) for k, v in obj.items()}
    if isinstance(obj, (tuple, list)):
        return [_serial(x) for x in obj]
    return obj


def _hash(obj):
    return sha256(json.dumps(_serial(obj), sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def _intersects(box, other):
    return all(lo <= oh and ol <= hi for (lo, hi), (ol, oh) in zip(box, other))


def _contained(box, other):
    return all(ol <= lo <= hi <= oh for (lo, hi), (ol, oh) in zip(box, other))


import ctypes as C
from math import comb,isqrt
from functools import lru_cache
from exact128_2026 import pointer,decode
DEFAULT_BITS=96
LIB=C.CDLL(str(Path(__file__).with_name('analytic10_2026_sum.so').resolve()))
LIB.analytic10_min.argtypes=[C.POINTER(C.c_uint64)]*5;LIB.analytic10_min.restype=C.c_int

def words(v):
    raw=bytearray()
    for x in v:
        assert type(x)is int and -(1<<124)<x<(1<<124)
        raw.extend(x.to_bytes(16,'little',signed=True))
    return np.frombuffer(raw,dtype=np.uint64).reshape(11,2)

def minimum(b,hh):
    assert b.shape==(11,11,11) and all(h.shape==(11,2)for h in hh)
    out=np.empty(2,dtype=np.uint64);code=LIB.analytic10_min(pointer(b._words),*[pointer(h)for h in hh],pointer(out))
    if code:raise OverflowError('analytic10 sum range guard '+str(code))
    return decode(out)

def upper_split(v):
    row=list(v);left=[row[0]];right=[row[-1]]
    while len(row)>1:
        row=[(row[j]+row[j+1]+1)//2 for j in range(len(row)-1)]
        left.append(row[0]);right.append(row[-1])
    return tuple(left),tuple(reversed(right))

class AxisCache:
    def __init__(self,dm,bits=96):
        assert bits in (80,96,104)
        self.bits=bits;self.scale=1<<bits;self.dm=dm;self.root=tuple(int(x)for x in coefficients({(k,):v for k,v in dm.items()},(ROOT_BOX[0],),degrees=(20,),bits=self.bits,upper=True).flat)
    @lru_cache(None)
    def D(self,level,index):
        assert 0<=index<(1<<level)
        if level==0:return self.root
        return upper_split(self.D(level-1,index//2))[index%2]
    @lru_cache(None)
    def H(self,level,index):
        l=Fraction(-1)+Fraction(39,25)*Fraction(index,1<<level);r=l+Fraction(39,25*(1<<level));lam=(r-l)/(1-l);assert 0<lam<1
        vv=2-2*l;n=isqrt((vv.denominator*(1<<(2*self.bits)))//vv.numerator)
        af=[n*comb(2*k,k)*lam.numerator**k//(4**k*lam.denominator**k)for k in range(11)]
        d=self.D(level,index);ad=[comb(20,k)*sum((-1)**(k-j)*comb(k,j)*d[j]for j in range(k+1))for k in range(21)]
        tail=sum(max(v,0)for v in ad[11:]);q=[af[k]-ad[k]for k in range(11)];q[0]-=tail
        h=[sum(q[k]*(2520//comb(10,k))*comb(i,k)for k in range(i+1))//2520 for i in range(11)]
        return (words(h) if all(-(1<<124)<v<(1<<124)for v in h)else None),tuple(h),tuple(q)

def check_analytic(F_intervals,c_interval,local_regions,boundary_multipliers,budget,seconds,delta=Fraction(0),bits=96):
    start=monotonic();assert bits in (80,96,104)
    assert type(budget)is int and budget>=0 and 0<=seconds<=180
    delta=_rational(delta);assert delta>=0
    poly,local,boundary=_normalize(F_intervals,local_regions,boundary_multipliers)
    clo,chi=map(_rational,c_interval);assert clo<=chi
    fm={p:(lo+hi)/2 for p,(lo,hi)in poly.items()};eps=sum((hi-lo)/2 for lo,hi in poly.values())
    degree=tuple(max(p[i]for p in fm)for i in range(3));assert all(n<=10 for n in degree)
    # Symmetrization is allowed ONLY under the true F symmetry premise; error remains eps.
    sym={}
    for pm in permutations(range(3)):
        for p,v in fm.items():
            pp=tuple(p[i]for i in pm);sym[pp]=sym.get(pp,Fraction(0))+v/6
    fm=sym;dm={}
    for (i,j,k),v in fm.items():dm[j+k]=dm.get(j+k,Fraction(0))+v
    ddegree=max(dm);assert ddegree<=20
    lower={p:-7*v for p,v in fm.items()};lower[(0,0,0)]=lower.get((0,0,0),0)-chi+delta/12-10*eps
    B0=coefficients(lower,ROOT_BOX,degrees=(10,10,10),bits=bits);G0=coefficients(GRAM,ROOT_BOX,bits=bits,upper=True)
    cache=AxisCache(dm,bits);b=NativeTensor(B0);g=NativeTensor(G0);active={}
    for i,item in enumerate(boundary):
        ss=lower.copy()
        for p,v in GRAM.items():ss[p]=ss.get(p,0)-item['lambda']*v
        active[i]=NativeTensor(coefficients(ss,ROOT_BOX,degrees=(10,10,10),bits=bits))
    rootinputs={'bits':bits,'F_mid_sym':[[list(p),str(v)]for p,v in sorted(fm.items())],'epsF':str(eps),'d_mid':[[k,str(v)]for k,v in sorted(dm.items())],'c_interval':list(map(str,[clo,chi])),'delta':str(delta),'K_monomial':[[list(p),str(v)]for p,v in sorted(lower.items())],'K_root_floor':[str(int(v))for v in B0.flat],'K_shape':[11]*3,'D_root_ceil':list(map(str,cache.root)),'Gram_root_ceil':[str(int(v))for v in G0.flat],'Gram_shape':list(G0.shape),'local_regions':_serial(local),'boundary_multipliers':_serial(boundary)}
    stack=[(b,g,active,ROOT_BOX,(0,0,0),(0,0,0),'')];counts={x:0 for x in ['positive','gram_negative','ordered_disjoint','local_region','boundary_multiplier']};visited=splits=maxdepth=0;h_range_skipped_nodes=0;reason=None;transcript=sha256();localcounts={x['id']:0 for x in local};bc={x['id']:0 for x in boundary}
    while stack and visited<budget and monotonic()-start<seconds:
        if len(stack)>256:reason='pending_stack_exceeds256';break
        if len(stack[-1][-1])>150:reason='next_path_depth_exceeds150';break
        b,g,act,box,levels,indices,path=stack.pop();visited+=1;maxdepth=max(maxdepth,len(path));kind=None;ident=None;witness=None
        if any(box[i][0]>box[j][1]for i in range(3)for j in range(i+1,3)):kind='ordered_disjoint'
        elif g.max()<0:kind='gram_negative'
        else:
            hh=[cache.H(lev,idx)[0]for lev,idx in zip(levels,indices)];v=None if any(h is None for h in hh)else minimum(b,hh)
            if v is None:h_range_skipped_nodes+=1
            if v is not None and v>=0:kind='positive';witness=v
            else:
                for reg in local:
                    if _contained(box,reg['core']):kind='local_region';ident=reg['id'];localcounts[ident]+=1;break
                if kind is None:
                    for i,sb in act.items():
                        v=None if any(h is None for h in hh)else minimum(sb,hh)
                        if v is not None and v>=0:kind='boundary_multiplier';ident=boundary[i]['id'];bc[ident]+=1;witness=v;break
        if kind:
            counts[kind]+=1;transcript.update(json.dumps([path,kind,ident,witness]).encode());continue
        axis=min(range(3),key=lambda i:levels[i]);lv=list(levels);lv[axis]+=1;lv=tuple(lv);mid=sum(box[axis])/2;boxes=[list(box),list(box)];boxes[0][axis]=(box[axis][0],mid);boxes[1][axis]=(mid,box[axis][1]);boxes=list(map(tuple,boxes));bs=b.split(axis);gs=g.split(axis,upper=True);acs=[{},{}]
        for i,sb in act.items():
            yes=[_intersects(bb,boundary[i]['activation'])for bb in boxes]
            if any(yes):
                ss=sb.split(axis)
                for side in range(2):
                    if yes[side]:acs[side][i]=ss[side]
        for side in [1,0]:
            ix=list(indices);ix[axis]=2*ix[axis]+side;stack.append((bs[side],gs[side],acs[side],boxes[side],lv,tuple(ix),path+str(side)))
        splits+=1
        if visited%5000==0:print(json.dumps({'stage':'analytic10_sharp_progress','visited':visited,'seconds':monotonic()-start,'pending':len(stack),'counts':counts}),flush=True)
    terminals=sum(counts.values());assert visited==terminals+splits and terminals+len(stack)==splits+1
    pending=[{'box':_serial(box),'path':path,'levels':lv,'indices':ix,'active_boundary_ids':[boundary[i]['id']for i in ac]}for _,_,ac,box,lv,ix,path in reversed(stack)]
    return {'status':('CONDITIONAL_SHARP_CLOSED'if delta==0 else'CONDITIONAL_NONSHARP_CLOSED')if not stack else'INCOMPLETE','conditional_only':True,'premises':['true symmetric F coefficient enclosures and c enclosure','same input model PSD and pair reduction','every supplied local certificate belongs to this SAME input F/c model; no old-model local transfer'],'bits':bits,'h_range_skipped_nodes':h_range_skipped_nodes,'delta':str(delta),'energy_target':'E_star-'+str(delta),'F_degree':degree,'d_degree':ddegree,'epsF':str(eps),'rootinputs':rootinputs,'guard_reason':reason,'visited_nodes':visited,'split_nodes':splits,'counts':counts,'local_counts':localcounts,'boundary_counts':bc,'maxdepth':maxdepth,'pending_count':len(pending),'pending':pending,'coverage':{'visited_equals_terminal_plus_splits':visited==terminals+splits,'terminal_plus_pending_equals_splits_plus_one':terminals+len(pending)==splits+1,'full_pending_saved':True},'cache_H':list(cache.H.cache_info()),'cache_D':list(cache.D.cache_info()),'elapsed_seconds':monotonic()-start,'transcript_sha256':transcript.hexdigest(),'engine_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'native_sum_sha256':sha256(Path(__file__).with_name('analytic10_2026_sum.c').read_bytes()).hexdigest(),'native_sum_so_sha256':sha256(Path(__file__).with_name('analytic10_2026_sum.so').read_bytes()).hexdigest(),'tensor_wrapper_sha256':sha256(Path(native_backend.__file__).read_bytes()).hexdigest(),'tensor_C_sha256':sha256(Path(native_backend.__file__).with_suffix('.c').read_bytes()).hexdigest(),'root_inputs_sha256':_hash(rootinputs),'restart_from_full_root':True,'frontier_resumed':False}
