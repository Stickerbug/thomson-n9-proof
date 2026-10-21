"""Reproducible exploratory calculations for classical Thomson N=9.
Python 3 standard library only. Floating-point calculations are not certificates.
"""
import decimal, math, random, json
from pathlib import Path
from collections import Counter
D = decimal.Decimal
decimal.getcontext().prec = 70

def family_energy(r):
    return 2*D(3).sqrt()/r+D(3).sqrt()+3/(2*(1-r*r).sqrt())+6/(4-r*r).sqrt()+12/(2-r).sqrt()+6/(2+2*r).sqrt()

def family_derivative(r):
    return -2*D(3).sqrt()/r**2+D('1.5')*r/((1-r*r)*(1-r*r).sqrt())+6*r/((4-r*r)*(4-r*r).sqrt())+6/((2-r)*(2-r).sqrt())-6/((2+2*r)*(2+2*r).sqrt())

def dot(a,b): return sum(x*y for x,y in zip(a,b))
def norm(a): return math.sqrt(dot(a,a))
def cross(a,b): return [a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0]]

def energy_gradient(points):
    g=[[0.0]*3 for _ in points]; energy=0.0
    for i in range(len(points)):
        for j in range(i):
            d=[points[i][k]-points[j][k] for k in range(3)]
            d2=dot(d,d)
            if d2 < 1e-28: return float('inf'),g
            inv=1/math.sqrt(d2); energy+=inv
            for k in range(3):
                q=-d[k]*inv**3; g[i][k]+=q; g[j][k]-=q
    return energy,g

def angle_objective(a):
    points=[]; tangents=[]
    for i in range(9):
        t,p=a[2*i:2*i+2]; st,ct,sp,cp=math.sin(t),math.cos(t),math.sin(p),math.cos(p)
        points.append([st*cp,st*sp,ct])
        tangents.append(([ct*cp,ct*sp,-st],[-st*sp,st*cp,0]))
    e,g=energy_gradient(points)
    return e,[dot(g[i],tangents[i][k]) for i in range(9) for k in range(2)]

def bfgs(a, maxiter=800):
    n=len(a); H=[[float(i==j) for j in range(n)] for i in range(n)]
    e,g=angle_objective(a)
    for it in range(maxiter):
        if norm(g)<2e-8: break
        p=[-dot(row,g) for row in H]; slope=dot(p,g)
        if slope>=0:
            H=[[float(i==j) for j in range(n)] for i in range(n)]
            p=[-x for x in g]; slope=-dot(g,g)
        alpha=1.0
        for _ in range(45):
            b=[x+alpha*y for x,y in zip(a,p)]; en,gn=angle_objective(b)
            if en<=e+1e-4*alpha*slope: break
            alpha*=0.5
        else: break
        s=[y-x for x,y in zip(a,b)]; y=[v-u for u,v in zip(g,gn)]; sy=dot(s,y)
        if sy>1e-14*max(1,norm(s)*norm(y)):
            Hy=[dot(row,y) for row in H]; coeff=(sy+dot(y,Hy))/(sy*sy)
            H=[[H[i][j]+coeff*s[i]*s[j]-(Hy[i]*s[j]+s[i]*Hy[j])/sy for j in range(n)] for i in range(n)]
        a,e,g=b,en,gn
    return {'energy':e,'gradient_norm':norm(g),'iterations':it+1}

def jacobi_eigenvalues(A):
    A=[r[:] for r in A]; n=len(A)
    for _ in range(100*n*n):
        p,q=max(((i,j) for i in range(n) for j in range(i)),key=lambda ij:abs(A[ij[0]][ij[1]]))
        if abs(A[p][q])<1e-13: break
        theta=0.5*math.atan2(2*A[p][q],A[q][q]-A[p][p]); c,s=math.cos(theta),math.sin(theta)
        app,aqq,apq=A[p][p],A[q][q],A[p][q]
        for k in range(n):
            if k!=p and k!=q:
                kp,kq=A[k][p],A[k][q]
                A[k][p]=A[p][k]=c*kp-s*kq
                A[k][q]=A[q][k]=s*kp+c*kq
        A[p][p]=c*c*app+s*s*aqq-2*s*c*apq
        A[q][q]=s*s*app+c*c*aqq+2*s*c*apq
        A[p][q]=A[q][p]=0.0
    return sorted(A[i][i] for i in range(n))

def tangent_hessian(points):
    n=len(points); H=[[0.0]*(3*n) for _ in range(3*n)]
    _,g=energy_gradient(points)
    for i in range(n):
        for j in range(i):
            d=[points[i][k]-points[j][k] for k in range(3)]; r=norm(d)
            for k in range(3):
                for l in range(3):
                    a=3*d[k]*d[l]/r**5-float(k==l)/r**3
                    H[3*i+k][3*i+l]+=a; H[3*j+k][3*j+l]+=a
                    H[3*i+k][3*j+l]-=a; H[3*j+k][3*i+l]-=a
    B=[]
    for i,x in enumerate(points):
        lam=dot(g[i],x)
        for k in range(3): H[3*i+k][3*i+k]-=lam
        v=cross(x,[0,0,1] if abs(x[2])<0.9 else [1,0,0]); v=[a/norm(v) for a in v]; w=cross(x,v)
        for t in (v,w): B.append([0.0]*(3*i)+t+[0.0]*(3*(n-i-1)))
    return [[sum(B[i][k]*sum(H[k][l]*B[j][l] for l in range(3*n)) for k in range(3*n)) for j in range(2*n)] for i in range(2*n)]

if __name__=='__main__':
    lo,hi=D('0.01'),D('0.99')
    for _ in range(210):
        mid=(lo+hi)/2
        if family_derivative(mid)>0: hi=mid
        else: lo=mid
    r=(lo+hi)/2; h=(1-r*r).sqrt(); rf,hf=float(r),float(h)
    points=[[rf*math.cos(2*math.pi*k/3),rf*math.sin(2*math.pi*k/3),s*hf] for s in (1,-1) for k in range(3)]
    points += [[math.cos((2*k+1)*math.pi/3),math.sin((2*k+1)*math.pi/3),0] for k in range(3)]
    e,g=energy_gradient(points)
    tg=[[v-dot(v,x)*z for v,z in zip(gi,x)] for gi,x in zip(g,points)]
    # Independently check the analytic tangent Hessian by a geodesic second difference.
    A=tangent_hessian(points); eig=jacobi_eigenvalues(A)
    rng=random.Random(202610); runs=[]
    for _ in range(100):
        a=[v for i in range(9) for v in (math.acos(rng.uniform(-1,1)),rng.uniform(0,2*math.pi))]
        runs.append(bfgs(a))
    result={'definition':'unit S2, E=sum(i<j) 1/distance; numerical exploration, not rigorous interval proof',
        'r':str(r),'h':str(h),'energy':str(family_energy(r)),'decimal_stationary_residual':str(family_derivative(r)),
        'cartesian_energy':e,'tangent_gradient_norm':math.sqrt(sum(dot(v,v) for v in tg)),
        'tangent_hessian_eigenvalues':eig,'points':points,'seed':202610,'random_start_count':len(runs),
        'energy_bins_8_decimals':dict(Counter(f'{x["energy"]:.8f}' for x in runs)),
        'max_random_final_gradient':max(x['gradient_norm'] for x in runs),'runs':runs}
    Path('n9_numerics.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('runs','points')},indent=2))
