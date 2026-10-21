"""High precision discovery, then exact rational certification of a Coulomb minorant."""
if not __debug__:raise RuntimeError('Assertions must be active')
from decimal import Decimal as D,localcontext,ROUND_HALF_EVEN
from fractions import Fraction as F
from pathlib import Path
from math import comb
import argparse,json,time
from certify_conditional_h19 import plus,times,check
PI=D('3.1415926535897932384626433832795028841971693993751058209749445923078164062862089986280348253421170679')
def cosine(x):
 term=D(1);total=term;k=0
 while abs(term)>D('1e-94'):
  k+=1;term*=-x*x/D((2*k-1)*(2*k));total+=term
 return total
def build(degree):
 with localcontext()as ctx:
  ctx.prec=100;n=degree+1;center=D(-11)/50;width=D(39)/50;values=[];zz=[]
  for j in range(n):
   z=cosine(PI*(D(j)+D('.5'))/n);t=center+width*z;zz.append(z);values.append(1/(2-2*t).sqrt())
  ck=[D(0)]*n
  for z,f in zip(zz,values):
   tm=D(1);tp=z;ck[0]+=f
   if n>1:ck[1]+=f*z
   for k in range(2,n):tn=2*z*tp-tm;ck[k]+=f*tn;tm,tp=tp,tn
  ck=[x*2/n for x in ck];ck[0]/=2
  z0=D(11)/39;z1=D(50)/39;T=[[D(1)],[z0,z1]]
  for k in range(2,n):
   a=[D(0)]*(k+1)
   for i,v in enumerate(T[-1]):a[i]+=2*z0*v;a[i+1]+=2*z1*v
   for i,v in enumerate(T[-2]):a[i]-=v
   T.append(a)
  h=[D(0)]*n
  for c,tp in zip(ck,T):
   for i,v in enumerate(tp):h[i]+=c*v
  den=10**55;h=[F(int((v*den).to_integral_value(rounding=ROUND_HALF_EVEN)),den)for v in h]
  h[0]-=F(1,200000000000);return h,ck

def verify(h,eps,lo=F(-1),hi=F(14,25)):
 pos=check(h,lo,hi);minor=check(plus([F(1)],[-x for x in times([F(2),F(-2)],times(h,h))]),lo,hi)
 q=plus(h,[eps]);upper=check(plus(times([F(2),F(-2)],times(q,q)),[F(-1)]),lo,hi)
 return pos,minor,upper

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--degree',type=int,choices=[27,31],default=27);args=ap.parse_args();start=time.time();h,ck=build(args.degree);eps=F(1,100000000000);nodes=verify(h,eps)
 out=Path(__file__).with_name('conditional_h'+str(args.degree)+'_certificate.json');assert not out.exists()
 result={'status':'certified','degree':args.degree,'claim':'0<=f(t)-h(t)<'+str(eps)+' for all -1<=t<=14/25','domain':['-1','14/25'],'error_upper':str(eps),'h_monomial':[str(x)for x in h],'positive_nodes':nodes[0],'minorant_nodes':nodes[1],'error_nodes':nodes[2],'discovery':'100-digit Decimal Chebyshev interpolation; cosine Taylor; Decimal monomial conversion; coefficients quantized to denominator 1e55; downward shift 5e-12','downward_shift':'1/200000000000','logic':'Exact rational Bernstein h>0, 1-(2-2t)h^2>0, (2-2t)(h+eps)^2-1>0. Hence h<f<h+eps throughout the closed domain. Decimal discovery is not trusted by the proof.','seconds':time.time()-start}
 out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='h_monomial'}),flush=True)
if __name__=='__main__':main()
