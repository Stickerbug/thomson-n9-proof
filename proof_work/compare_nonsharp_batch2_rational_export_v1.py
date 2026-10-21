import json,time
from pathlib import Path
from fractions import Fraction
import numpy as np
from three_point_sampled import design
from sharp_three_point import ENERGY
ROOT=Path(__file__).parent;start=time.time();src=json.loads((ROOT/'nonsharp_nullspace_actualf_d10_run2.json').read_text());best=src['best_solution'];rat=json.loads((ROOT/'nonsharp_d10_batch2_h27_target25_75995_v1.json').read_text());pts=np.array(src['training_points']);N=[np.array(n)for n in src['nullspace_bases']];x=np.array(best['x']);idx=0;sourceA=[]
for k,n in enumerate(N):
 b=np.zeros((n.shape[1],n.shape[1]))
 for i in range(len(b)):
  for j in range(i,len(b)):b[i,j]=b[j,i]=x[idx];idx+=1
 sourceA.append(n@b@n.T)
ratA=[np.array([[float(Fraction(z))for z in row]for row in a])for a in rat['A']];cs=(ENERGY+1.5*sourceA[0].sum())/12;cr=(ENERGY+1.5*ratA[0].sum())/12;source_res=[];rat_res=[]
for lo in range(0,len(pts),500):
 pp=pts[lo:lo+500];D=design(pp,10);rhs=np.sum((2-2*pp)**(-.5),axis=1)
 source_res.extend(rhs-cs-sum(np.einsum('nij,ij->n',m,a)for m,a in zip(D,sourceA)))
 rat_res.extend(rhs-cr-sum(np.einsum('nij,ij->n',m,a)for m,a in zip(D,ratA)))
a=np.array(source_res);b=np.array(rat_res);ia=int(a.argmin());ib=int(b.argmin());idiff=int(abs(a-b).argmax());result={'warning':'Numerical export comparison only','points':len(pts),'source_iteration':best['iteration'],'x_reconstructed_A_vs_saved_max':float(max(abs(aa-np.array(old)).max()for aa,old in zip(sourceA,best['A']))),'A_rounding_max_change':float(max(abs(a-b).max()for a,b in zip(sourceA,ratA))),'cstar_source':float(cs),'cstar_rational':float(cr),'cstar_change':float(cr-cs),'source_min_R':float(a[ia]),'source_worst':pts[ia].tolist(),'rational_min_R':float(b[ib]),'rational_worst':pts[ib].tolist(),'residual_max_difference':float(abs(a-b).max()),'max_difference_point':pts[idiff].tolist(),'max_difference_source_R':float(a[idiff]),'max_difference_rational_R':float(b[idiff]),'seconds':time.time()-start};out=ROOT/'compare_nonsharp_batch2_rational_export_v1.json';assert not out.exists();out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)
