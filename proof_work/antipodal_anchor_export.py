from fractions import Fraction as F
from pathlib import Path
import json,itertools
from certify_three_point_d4 import add,mul,scale,const,mono,ldl,power
src=json.loads(Path('proof_work/antipodal_anchor_results.json').read_text())
m=[v for v in src if v['degree']==3][-1]
cert=json.loads(Path('proof_work/three_point_d4_exact_25_745.json').read_text())
h=[F(v) for v in cert['h_monomial']]
A=[];piv=[]
for raw in m['matrices']:
 a=[[F(str(round((x+y)/2,9)))+F(i==j,10**7) for j,(x,y) in enumerate(zip(row,col))] for i,(row,col) in enumerate(zip(raw,zip(*raw)))]
 piv.append(ldl(a));A.append(a)
z,w,t=[mono(i,1) for i in range(3)];one=const(1);a=add(t,scale(mul(z,w),-1));b=mul(add(one,scale(mul(z,z),-1)),add(one,scale(mul(w,w),-1)))
Q=[one,a]
for k in range(1,3):Q.append(add(scale(mul(a,Q[-1]),2),scale(mul(b,Q[-2]),-1)))
kernel={};diagz={};diagw={};idx=0;blocks=[]
for k in range(4):
 for parity in [0,1]:
  ii=list(range(parity,4-k,2))
  if not ii:continue
  aa=A[idx];idx+=1;blocks.append({'k':k,'powers':ii,'A':[[str(v)for v in row]for row in aa]})
  for i,p in enumerate(ii):
   for j,q in enumerate(ii):
    kernel=add(kernel,scale(mul(mul(mono(0,p),mono(1,q)),Q[k]),aa[i][j]))
    diagz=add(diagz,scale(mul(mono(0,p+q),power(add(one,scale(mul(z,z),-1)),k)),aa[i][j]))
    diagw=add(diagw,scale(mul(mono(1,p+q),power(add(one,scale(mul(w,w),-1)),k)),aa[i][j]))
H=lambda axis,sgn=1:{tuple(i if j==axis else 0 for j in range(3)):x*sgn**i for i,x in enumerate(h) if x}
rhs=add(H(2),scale(add(H(0),H(0,-1),H(1),H(1,-1)),F(1,6)))
target=F('25.78');c=(target-F(1,2))/21
R=add(rhs,scale(kernel,-1),scale(add(diagz,diagw),-F(1,12)),const(-c))
export={'target':str(target),'c':str(c),'degree':3,'blocks':blocks,'h':list(map(str,h)),'psd_ldl_pivots':piv,'residual_monomial':[[list(a),str(v)]for a,v in R.items()],'kernel_monomial':[[list(a),str(v)]for a,v in kernel.items()],'diag_z_monomial':[[list(a),str(v)]for a,v in diagz.items()],'identity':'R=h(t)+(h(z)+h(-z)+h(w)+h(-w))/6-F(z,w,t)-(F(z,z,1)+F(w,w,1))/12-c','domain':'|z|,|w|<=.57,-1<=t<=.57,Gram>=0; no permutation pruning besides z<->w'}
Path('proof_work/antipodal_anchor_exact_export.json').write_text(json.dumps(export,indent=2))
print('exported',len(R),'terms;exact PSD verified;target',target)
