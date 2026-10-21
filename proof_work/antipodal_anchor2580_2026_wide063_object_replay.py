if not __debug__:
 raise RuntimeError('Run certificate without -O or PYTHONOPTIMIZE')
"""Independent object-integer replay: no int64 and no symmetry pruning."""
from pathlib import Path
from fractions import Fraction as F
from math import comb
import itertools,json,time
from certify_three_point_d4 import add,mul,const,scale,mono,power,ldl,bernstein,split
start=time.time();base=Path(__file__).parent;src=json.loads((base/'antipodal_anchor2580_2026_export.json').read_text())
z,w,t=[mono(j,1)for j in range(3)];Q=[const(1),add(t,scale(mul(z,w),-1))];Hprod=mul(add(const(1),scale(power(z,2),-1)),add(const(1),scale(power(w,2),-1)))
for k in [1,2]:Q.append(add(scale(mul(Q[1],Q[k]),2),scale(mul(Hprod,Q[k-1]),-1)))
kernel={};D={};psd=[]
for b in src['blocks']:
 A=[[F(v)for v in row]for row in b['A']];ps=b['powers'];psd.append(ldl(A));assert all(A[i][j]==A[j][i]for i in range(len(A))for j in range(len(A)))
 for i,p in enumerate(ps):
  for j,q in enumerate(ps):
   kernel=add(kernel,scale(mul(mul(mono(0,p),mono(1,q)),Q[b['k']]),A[i][j]))
   D=add(D,scale(mul(mono(0,p+q),power(add(const(1),scale(power(z,2),-1)),b['k'])),A[i][j]))
saved=lambda key:{tuple(a):F(v)for a,v in src[key]}
assert kernel==saved('kernel_monomial');assert D==saved('diag_z_monomial')
h=list(map(F,src['h']));fields={}
for j,c in enumerate(h):
 fields=add(fields,{(0,0,j):c})
 for ax in [0,1]:fields=add(fields,scale(mono(ax,j),c*F(1+(-1)**j,6)))
Dw={(0,a[0],0):v for a,v in D.items()};cc=F(src['c']);target=F(src['target']);assert F(1,2)+21*cc==target
R=add(fields,scale(kernel,-1),scale(add(D,Dw),-F(1,12)),const(-cc));assert R==saved('residual_monomial')
# exact affine substitution all three variables to [-1,1]
def subst(p):
 out={};scale_axis=[F(63,100),F(63,100),F(157,200)];offset=[F(0),F(0),F(-43,200)]
 for a,c in p.items():
  for b in itertools.product(*(range(i+1) for i in a)):
   val=c
   for ax in range(3):val*=comb(a[ax],b[ax])*scale_axis[ax]**b[ax]*offset[ax]**(a[ax]-b[ax])
   if val:out=add(out,{b:val})
 return out
Gram=add(const(1),scale(mul(mul(z,w),t),2),scale(power(z,2),-1),scale(power(w,2),-1),scale(power(t,2),-1))
B=bernstein(subst(R),bits=70);G=bernstein(subst(Gram),bits=70,upper=True)
stack=[(B,G,0)];nodes=pos=out=depth=0
while stack:
 b,g,d=stack.pop();nodes+=1;depth=max(depth,d);assert nodes<100000 and d<100
 if min(b.flat)>=0:pos+=1;continue
 if max(g.flat)<0:out+=1;continue
 axis=d%3;bl,br=split(b,axis);gl,gr=split(g,axis,upper=True);stack.extend([(br,gr,d+1),(bl,gl,d+1)])
# Minorant checked separately, exact integer outward univariate Bernstein
h0={ (j,0,0):c for j,c in enumerate(h)};assert min(bernstein(h0,degrees=(11,0,0),bits=70).flat)>0
qq=add(const(1),scale(mul(add(const(2),scale(z,-2)),mul(h0,h0)),-1));todo=[bernstein(qq,degrees=(23,0,0),bits=70)];hn=0
while todo:
 bb=todo.pop();hn+=1;assert hn<10000
 if min(bb.flat)>=0:continue
 todo.extend(split(bb,0))
H=lambda d:2/d**3-F(1,4)/d
d0=F(469,500);theta=F(9,100);assert F(4,499)<theta**2
assert d0**2<F(22,25) and d0-theta/2>F(89,100)
assert F(3992,1000)>F(199,100)**2
assert H(F(89,100))<F(11,4) and H(F(199,100))<F(1,4)
M=F(14,4)*F(11,4)+F(1,4);assert M==F(79,8)
cost=M*theta**2/2;assert cost==F(6399,160000)
assert F(56,100)+theta/2==F(121,200)<F(61,100)<F(63,100)
near=target-cost;assert near==F(4121601,160000)>F('25.76')>F('25.759986531269832')
# Also retain the earlier one-point .998 variant on the same wider25.80 box.
th1=F(8,125);assert F(4,999)<th1**2 and d0-th1>F(87,100)
assert H(F(87,100))<F(11,4);cost1=F(39,4)*th1**2;assert cost1==F(624,15625)
assert target-cost1==F(402501,15625)>F('25.76');assert F(56,100)+th1<F(63,100)
ans={'status':'certified','target':str(target),'axial_box':'[-63/100,63/100]^2','remaining_dot_interval':'[-1,57/100]','object_integer_bits':70,'symmetry_pruning':False,'nodes':nodes,'positive_leaves':pos,'gram_excluded_leaves':out,'pending_boxes':0,'maxdepth':depth,'minorant_nodes':hn,'psd_pivots':psd,'symmetric_stationary_minimizer_dot_lower':'-249/250','total_arc_upper':str(theta),'each_point_arc_upper':str(theta/2),'arc_squared_bound':'4/499','combined_Hessian_upper':str(M),'energy_movement_cost':str(cost),'implied_original_energy_lower':str(near),'onepoint_alternative_dot_lower':'-499/500','onepoint_cost':str(cost1),'scope':'stationary global-minimizer exclusion only, not arbitrary competitive configurations','seconds':time.time()-start}
p=base/'antipodal_anchor2580_2026_wide063_object_replay.json';assert not p.exists();p.write_text(json.dumps(ans,indent=2)+'\n');print(json.dumps(ans),flush=True)
