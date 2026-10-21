import json,random,time,hashlib,ctypes as C
from pathlib import Path
from fractions import Fraction as F
import numpy as np
from exact128_2026 import NativeTensor,LIMIT,library,pointer,decode
from certify_three_point_d4 import split as object_split
start=time.time();rng=random.Random(20261017);cases=[]
for z in range(120):
 shape=tuple(rng.randrange(1,9)for _ in range(3));a=np.empty(shape,dtype=object)
 for ix in np.ndindex(shape):a[ix]=rng.randrange(-LIMIT+1,LIMIT)
 cases.append(a)
edges=[-LIMIT+1,-LIMIT+2,-LIMIT+3,-(1<<100)-1,-3,-2,-1,0,1,2,3,(1<<100)+1,LIMIT-3,LIMIT-2,LIMIT-1]
for shape in [(1,1,1),(2,3,7),(64,1,2),(1,64,1),(2,1,64)]:
 a=np.empty(shape,dtype=object)
 for j,ix in enumerate(np.ndindex(shape)):a[ix]=edges[j%len(edges)]
 cases.append(a)
checks=0
for a in cases:
 native=NativeTensor(a);assert native.shape==a.shape;assert native.min()==min(a.flat)and native.max()==max(a.flat)
 for axis in range(3):
  for upper in [False,True]:
   L,R=native.split(axis,upper);l,r=object_split(a,axis,upper)
   assert np.array_equal(L.to_object(),l)and np.array_equal(R.to_object(),r)
   assert L.min()==min(l.flat)and L.max()==max(l.flat)and R.min()==min(r.flat)and R.max()==max(r.flat)
   checks+=1
# Explicit Fraction floor/ceil averages cover odd negative values independently.
for x in edges:
 for y in edges:
  a=np.array([x,y],dtype=object).reshape(2,1,1)
  for upper in [0,1]:
   left,right=NativeTensor(a).split(0,upper);q=F(x+y,2);expected=-((-q.numerator)//q.denominator)if upper else q.numerator//q.denominator
   assert left.to_object()[1,0,0]==right.to_object()[0,0,0]==expected
rejected=0
for x in [LIMIT,-LIMIT,(1<<127),-(1<<127)-1,1<<200]:
 try:NativeTensor(np.array([x],dtype=object).reshape(1,1,1))
 except OverflowError:rejected+=1
 else:raise AssertionError('accepted forbidden magnitude')
for shape in [(1,2),(1,1,65),(0,1,1)]:
 try:NativeTensor(np.zeros(shape,dtype=object))
 except ValueError:rejected+=1
 else:raise AssertionError('accepted bad shape')
lib=library()
for x in [LIMIT,-LIMIT]:
 words=np.frombuffer(x.to_bytes(16,'little',signed=True),dtype=np.uint64).copy();lo=np.zeros(2,dtype=np.uint64);hi=lo.copy();assert lib.exact128_minmax(pointer(words),1,pointer(lo),pointer(hi))==2
 left=np.full(2,77,dtype=np.uint64);right=left.copy();dims=np.ones(3,dtype=np.uint64);assert lib.exact128_split(pointer(words),pointer(left),pointer(right),pointer(dims),1,0,0)==2;assert np.all(left==77)and np.all(right==77);rejected+=2
one=np.zeros(2,dtype=np.uint64);dims=np.array([1,1,1],dtype=np.uint64)
for axis,upper,count in [(3,0,1),(0,2,1),(0,0,2)]:assert lib.exact128_split(pointer(one),pointer(one),pointer(one),pointer(dims),count,axis,upper)==1;rejected+=1
out={'status':'PASSED_GUARDED_SIGNED128_BACKEND_CROSSCHECK_NOT_GLOBAL_PROOF','random_tensors':120,'edge_tensors':5,'object_split_comparisons':checks,'independent_Fraction_average_comparisons':len(edges)**2*2,'rejection_checks':rejected,'strict_range':'abs(value)<2^124','scale':'unchanged; input and output integers preserve caller scale','seconds':time.time()-start,'sources_sha256':{n:hashlib.sha256((Path(__file__).parent/n).read_bytes()).hexdigest()for n in ['exact128_2026.c','exact128_2026.py',Path(__file__).name]}}
p=Path(__file__).with_name('exact128_2026_test_results.json');assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
