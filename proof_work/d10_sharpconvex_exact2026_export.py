if not __debug__:
 raise RuntimeError('Run without -O')
import json,itertools,hashlib,argparse,time
from pathlib import Path
from fractions import Fraction as F
from dyadic_interval import I,S,BITS
from d10_sharpconvex_exact2026_kernel import run as kernel
from certify_three_point_d4 import mul as qmul,add as qadd,scale as qscale,mono,const
Z=(0,0,0)
def raw(v):
 assert v['denominator_power_of_two']==BITS
 return I(int(v['lo_numerator']),int(v['hi_numerator']),raw=True)
def add(p,key,c):p[key]=p.get(key,I(0))+c
def export(cert,output,ctx=None):
 start=time.time();ctx=ctx or kernel(None,cert,True);Ns=ctx['N'];xx=ctx['x'];lookup={tuple(t):j for j,t in enumerate(ctx['indices'])};A=[]
 for k,N in enumerate(Ns):
  n=len(N)
  if not n:A.append([]);continue
  B=[[xx[lookup[k,min(i,j),max(i,j)]]for j in range(n)]for i in range(n)];m=len(N[0]);A.append([[sum((N[a][i]*sum((B[a][b]*N[b][j]for b in range(n)),I(0))for a in range(n)),I(0))for j in range(m)]for i in range(m)])
 a=qadd(mono(2,1),qscale(qmul(mono(0,1),mono(1,1)),-1));b=qmul(qadd(const(1),qscale(mono(0,2),-1)),qadd(const(1),qscale(mono(1,2),-1)));Q=[const(1),a]
 for k in range(1,10):Q.append(qadd(qscale(qmul(a,Q[-1]),2),qscale(qmul(b,Q[-2]),-1)))
 fp={}
 for k,Ak in enumerate(A):
  for i,row in enumerate(Ak):
   for j,c in enumerate(row):
    for e,q in Q[k].items():
     es=(e[0]+i,e[1]+j,e[2])
     for perm in itertools.permutations(range(3)):
      key=[0]*3
      for ax in range(3):key[perm[ax]]=es[ax]
      add(fp,tuple(key),c*(q/6))
 src=Path('proof_work/contact_minorant_factor_v1.json');hcert=json.loads(src.read_text());assert hcert['status']=='certified_contact_minorant_and_error_bound';case=hcert['cases'][1];assert case['degree']==27
 newton=[raw(v)for v in case['newton_coefficients']];zs=[raw(v)for v in case['newton_nodes']];hp=[newton[-1]]
 for j in reversed(range(len(newton)-1)):
  out=[I(0)]*(len(hp)+1)
  for i,v in enumerate(hp):out[i]-=zs[j]*v;out[i+1]+=v
  out[0]+=newton[j];hp=out
 nodes=ctx['nodes'];E=sum((w/(2-2*x).sqrt()for w,x in zip([6,3,6,3,12,6],nodes)),I(0));F111=sum(fp.values(),I(0));c=E/12+F111/8;rp={}
 for axis in range(3):
  for degree,v in enumerate(hp):key=[0]*3;key[axis]=degree;add(rp,tuple(key),v)
 for key,v in fp.items():
  add(rp,key,-7*v)
  for axis in range(3):es=[0]*3;es[axis]=key[1]+key[2];add(rp,tuple(es),-v)
 add(rp,Z,-c)
 geom=json.loads(Path('proof_work/candidate_triple_types_v1.json').read_text())['triangle_types'];names='ABCDFG';centers=[]
 for row in geom:
  labels=sorted(row['labels'],key=lambda a:nodes[names.index(a)].lo);centers.append({'labels':labels,'kind':row['status'],'center_intervals':[nodes[names.index(a)].bounds()for a in labels]})
 deps=[Path(cert),src,Path('proof_work/d10_contact_left_geometry_v1.json')];out={'status':'TRUE_ALGEBRAIC_COEFFICIENT_ENCLOSURES_NOT_RATIONAL_SUBSTITUTE','bits':BITS,'algebraic_definition':'r is actual stationary root; 157 fixed rationalseed coordinates and33 exactcontact equations define B; analyticNtilde rationalT1 gives A; h is true HermiteH27; c=E_star/12+F111/8, target exactly E_star','source_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest()for p in deps},'R_coefficients':[[list(key),v.bounds()]for key,v in sorted(rp.items())],'F_coefficients':[[list(key),v.bounds()]for key,v in sorted(fp.items())],'H_coefficients_ascending':[v.bounds()for v in hp],'E_star':E.bounds(),'c':c.bounds(),'F111':F111.bounds(),'local_centers':centers,'seconds':time.time()-start}
 p=Path(output);assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');print('PASS exported',len(rp),'R terms seconds',time.time()-start,flush=True);return out
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--certificate',default='proof_work/d10_sharpconvex_exact2026_certificate.json');p.add_argument('--output',default='proof_work/d10_sharpconvex_exact2026_coefficients.json');a=p.parse_args();export(a.certificate,a.output)
