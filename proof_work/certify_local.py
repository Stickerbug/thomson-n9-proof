"""Strict rational interval local certificate, standard Python 3 only.
Run from workspace: python3 proof_work/certify_local.py
All assertions use integers. Floats are for display only.
"""
from math import isqrt
S=10**55
class I:
    def __init__(self,a,b=None,raw=False):
        if isinstance(a,I): self.a,self.b=a.a,a.b; return
        if raw: self.a,self.b=a,b; return
        self.a=a*S; self.b=(a if b is None else b)*S
    def __add__(x,y):
        y=I(y); return I(x.a+y.a,x.b+y.b,True)
    __radd__=__add__
    def __neg__(x): return I(-x.b,-x.a,True)
    def __sub__(x,y): return x+-I(y)
    def __rsub__(x,y): return I(y)+-x
    def __mul__(x,y):
        y=I(y); p=[x.a*y.a,x.a*y.b,x.b*y.a,x.b*y.b]
        return I(min(p)//S,-((-max(p))//S),True)
    __rmul__=__mul__
    def inv(x):
        assert not x.a<=0<=x.b
        return I(S*S//x.b,-((-S*S)//x.a),True)
    def __truediv__(x,y): return x*I(y).inv()
    def __rtruediv__(x,y): return I(y)*x.inv()
    def sqrt(x):
        assert x.a>=0
        a=isqrt(x.a*S); b=isqrt(x.b*S)
        return I(a,b+(b*b<x.b*S),True)
    def approx(x): return (x.a/S,x.b/S)
def dot(x,y): return sum((a*b for a,b in zip(x,y)),I(0))
def cross(x,y): return [x[1]*y[2]-x[2]*y[1],x[2]*y[0]-x[0]*y[2],x[0]*y[1]-x[1]*y[0]]
def df(r):
    a=1-r*r;b=4-r*r;c=2-r;d=2+2*r
    return -2*I(3).sqrt()/(r*r)+3*r/(2*a*a.sqrt())+6*r/(b*b.sqrt())+6/(c*c.sqrt())-6/(d*d.sqrt())
def decimal_integer(s):
    a,b=s.split('.');return int(a)*S+int(b)*10**(55-len(b))
lo=decimal_integer('0.71054833409295381132770417927279124')
hi=decimal_integer('0.71054833409295381132770417927279125')
assert df(I(lo,lo,True)).b<0 and df(I(hi,hi,True)).a>0
r=I(lo,hi,True);h=(1-r*r).sqrt();rt3=I(3).sqrt();half=I(1)/2
cs=[I(1),-half,-half];sn=[I(0),rt3/2,-rt3/2]
X=[[r*c,r*s,sgn*h] for sgn in [1,-1] for c,s in zip(cs,sn)]
X += [[half,rt3/2,I(0)],[-I(1),I(0),I(0)],[half,-rt3/2,I(0)]]
V=[[]for _ in range(9)]
a=dot(X[0],X[1]);V[1]=[[u-a*v for u,v in zip(X[0],X[1])]]
for i in range(2,9):
    v=cross(X[i],[I(0),I(0),I(1)]);V[i]=[v,cross(X[i],v)]
indices=[];n=0
for vv in V:
    indices.append(list(range(n,n+len(vv))));n+=len(vv)
assert n==15

def chart_hessian(epsilon_denominator):
    # Rational normalized tangent charts, exact candidate as chart centre.
    eps=I(0) if epsilon_denominator==0 else I(1)/epsilon_denominator
    z=I(-eps.b,eps.b,True)
    Y=[];J=[];K=[]
    for x,vv in zip(X,V):
        m=len(vv);G=[[dot(a,b)for b in vv]for a in vv]
        w=[sum((G[a][b]*z for b in range(m)),I(0))for a in range(m)]
        ss=1+sum((z*G[a][b]*z for a in range(m)for b in range(m)),I(0))
        s=ss.sqrt(); inv=1/s;inv3=inv/ss;inv5=inv3/ss
        y=[x[k]+sum((v[k]*z for v in vv),I(0))for k in range(3)]
        Y.append([t*inv for t in y])
        J.append([[vv[a][k]*inv-y[k]*w[a]*inv3 for k in range(3)]for a in range(m)])
        K.append([[[-(vv[a][k]*w[b]+vv[b][k]*w[a]+y[k]*G[a][b])*inv3+3*y[k]*w[a]*w[b]*inv5 for k in range(3)]for b in range(m)]for a in range(m)])
    M=[[I(0)for _ in range(n)]for _ in range(n)]
    for i in range(9):
        for j in range(i):
            d=[a-b for a,b in zip(Y[i],Y[j])];q2=dot(d,d);q=q2.sqrt();iq3=1/(q2*q);iq5=iq3/q2
            A=[[3*d[k]*d[l]*iq5-(iq3 if k==l else 0)for l in range(3)]for k in range(3)]
            active=[(indices[i][a],J[i][a])for a in range(len(V[i]))]+[(indices[j][a],[-t for t in J[j][a]])for a in range(len(V[j]))]
            for a,v in active:
                for b,w in active:
                    M[a][b]=M[a][b]+sum((v[k]*A[k][l]*w[l]for k in range(3)for l in range(3)),I(0))
            for point,sign in [(i,-1),(j,1)]:
                for a,ia in enumerate(indices[point]):
                    for b,ib in enumerate(indices[point]):
                        M[ia][ib]=M[ia][ib]+sign*dot(d,K[point][a][b])*iq3
    return M

def ldl(M):
    L=[[I(int(i==j))for j in range(n)]for i in range(n)];D=[]
    for i in range(n):
        p=M[i][i]-sum((L[i][k]*L[i][k]*D[k]for k in range(i)),I(0))
        assert p.a>0,(i,p.approx())
        D.append(p)
        for j in range(i+1,n):
            L[j][i]=(M[j][i]-sum((L[j][k]*L[i][k]*D[k]for k in range(i)),I(0)))/p
    return D

if __name__=='__main__':
    print('root numerator bounds:',lo,hi,'denominator',S)
    print('strict derivative signs:',df(I(lo,lo,True)).approx(),df(I(hi,hi,True)).approx())
    for den in [0,10**10,10**8,10**6]:
        D=ldl(chart_hessian(den))
        assert all(p.a*5>S for p in D)
        print('box halfwidth:', '0'if den==0 else '1/'+str(den))
        print('pivot intervals:',[p.approx()for p in D])
        print('all 15 pivots > 1/5: CERTIFIED')
