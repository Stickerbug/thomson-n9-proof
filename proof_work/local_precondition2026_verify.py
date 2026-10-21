if not __debug__:
 raise RuntimeError('Run without -O')
import json,time,hashlib,argparse
from pathlib import Path
from fractions import Fraction as F
from dyadic_interval import I,S,BITS
import d10_sharpconvex_exact2026_local as old
from d10_sharpconvex_exact2026_export import raw
from d10_exact_contact_jets_v1 import ldl as strict_ldl
BASE=Path(__file__).resolve().parent

def center_transform(H):
 n=len(H);A=[[F(v.lo+v.hi,2*S)for v in row]for row in H];L=[[F(i==j)for j in range(n)]for i in range(n)];D=[]
 for i in range(n):
  d=A[i][i]-sum((L[i][j]**2*D[j]for j in range(i)),F(0));assert d>0;D.append(d)
  for j in range(i+1,n):L[j][i]=(A[j][i]-sum((L[j][k]*L[i][k]*D[k]for k in range(i)),F(0)))/d
 W=[[F(i==j)for j in range(n)]for i in range(n)]
 for i in range(n):
  for j in range(i):W[i][j]=-sum((L[i][k]*W[k][j]for k in range(j,i)),F(0))
 assert all(W[i][j]==int(i==j)for i in range(n)for j in range(i,n))
 assert all(sum((W[i][k]*L[k][j]for k in range(n)),F(0))==int(i==j)for i in range(n)for j in range(n))
 return W

def transform(H,W):
 n=len(W);WI=[[I(v)for v in row]for row in W]
 return [[sum((WI[i][a]*H[a][b]*WI[j][b]for a in range(n)for b in range(n)),I(0))for j in range(n)]for i in range(n)]

def evaluate_box(poly,center,width,kind,W=None):
 captured=[]
 def callback(H):
  captured.append(H)
  return strict_ldl(transform(H,W))if W is not None else []
 original=old.ldl;old.ldl=callback
 try:result=old.try_box(poly,center,width,kind)
 finally:old.ldl=original
 assert len(captured)==1
 return result,captured[0]

def run(source_path,output_path,ctx=None):
 start=time.time();src=Path(source_path);source=ctx if ctx is not None else json.loads(src.read_text());assert source['bits']==BITS
 poly={tuple(a):raw(c)for a,c in source['R_coefficients']};previous=json.loads((BASE/'d10_sharpconvex_exact2026_local.json').read_text());prior={tuple(row['labels']):F(row['halfwidth'])for row in previous['rows']};rows=[];wider=0
 for item in source['local_centers']:
  center=[raw(c)for c in item['center_intervals']];mid=[I((c.lo+c.hi)//2,raw=True)for c in center];q=old.shift(poly,mid)
  _,Hcenter=evaluate_box(q,center,'0',item['kind']);W=center_transform(Hcenter);failures=[]
  choices=sorted(set(map(F,['.003','.001','.0003','.0001','.00003','.00001']) )|{prior[tuple(item['labels'])]},reverse=True)
  for width in choices:
   try:result,H=evaluate_box(q,center,width,item['kind'],W);break
   except AssertionError as e:failures.append({'halfwidth':str(width),'failure':str(e)})
  else:raise RuntimeError(('no width passed',item['labels'],failures))
  increased=width>prior[tuple(item['labels'])];wider+=int(increased)
  result.update({'labels':item['labels'],'center_intervals':item['center_intervals'],'congruence_W':[[str(v)for v in row]for row in W],'W_determinant':'1','W_invertibility_proof':'exact unit lower triangular rational matrix; W L=I verified over Fraction','Hessian_before_congruence':[[v.bounds()for v in row]for row in H],'preconditioned_Hessian':[[v.bounds()for v in row]for row in transform(H,W)],'prior_halfwidth':str(prior[tuple(item['labels'])]),'strictly_wider':increased,'failed_larger_widths':failures});rows.append(result);print('PASS',item['labels'],str(width),'wider',increased,'seconds',time.time()-start,flush=True)
 names=['dyadic_interval.py','d10_sharpconvex_exact2026_local.py','d10_sharpconvex_exact2026_export.py','d10_exact_contact_jets_v1.py',Path(__file__).name]
 out={'status':'CERTIFIED_PRECONDITIONED_POSITIVE_WIDTH_LOCAL_BOXES_NOT_GLOBAL','scope':'same true-root exact contact theorem and graph proof as original; full box interval Hessian congruence with fixed rational invertible W; no away coverage','source':str(src),'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'sources_sha256':{n:hashlib.sha256((BASE/n).read_bytes()).hexdigest()for n in names},'prior_local_sha256':hashlib.sha256((BASE/'d10_sharpconvex_exact2026_local.json').read_bytes()).hexdigest(),'bits':BITS,'rows':rows,'wider_only_count':wider,'total_rows':len(rows),'seconds':time.time()-start}
 p=Path(output_path);assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');print(out['status'],'wider',wider,'seconds',time.time()-start,flush=True);return out
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--source',default=str(BASE/'d10_sharpconvex_exact2026_coefficients.json'));p.add_argument('--output',required=True);a=p.parse_args();run(a.source,a.output)
