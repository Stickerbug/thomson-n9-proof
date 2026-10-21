"""Exact candidate anchor features over Q(r), using only rational operations.
Pass Fraction r for rational checks, or an interval class supporting +,-,*,/,**.
Returns p_hat,c so G_k=6*(1-r*r)^(k%2)*p_hat*p_hat^T+3*c*c^T.
No square roots are needed; candidate r can be isolated algebraically.
"""
from fractions import Fraction as F
from math import comb

def reduced_real_power(alpha,beta_squared,H,k):
    # Re((alpha*h+i*beta)^k)/h^(k mod 2), H=h².
    return sum(((-1)**j)*comb(k,2*j)*alpha**(k-2*j)*H**((k-2*j)//2)*beta_squared**j for j in range(k//2+1))

def features(r,k,m):
    H=1-r*r;A=1-F(3,2)*r*r;B=2*r*r-1;C=F(1,2)*r*r-1
    cap=[];prism=[];parity=k%2
    upper=2*reduced_real_power(-F(3,2)*r,F(3,4)*r*r,H,k)
    lower_same=(2*r)**k*H**(k//2)
    lower_other=2*reduced_real_power(F(1,2)*r,F(3,4)*r*r,H,k)
    opposite_cap=(-1)**k*H**(k//2)
    adjacent_caps=2*reduced_real_power(F(1,2),F(3,4),H,k)
    for i in range(m):
        prism.append((1 if k==0 else 0)+upper*A**i+lower_same*B**i+lower_other*C**i+opposite_cap*(-r)**i+adjacent_caps*(r/2)**i)
    if parity:
        cap=[r*0 for _ in range(m)]
    else:
        q=sum((-1)**j*comb(k,2*j)*(F(3,4)*r*r)**((k-2*j)//2)*H**j for j in range(k//2+1))
        cap=[(1 if k==0 else 0)+2*(-F(1,2))**i*F(3,4)**(k//2)+2*(-r)**i*(-1)**(k//2)*H**(k//2)+4*(r/2)**i*q for i in range(m)]
    return prism,cap

def nullspace_two_rows(p,c):
    """Return exact basis columns for {v:p.v=c.v=0}, with exact field comparisons.
    For rigorous algebraic/interval use, choose and certify pivot minors separately.
    """
    rows=[list(p),list(c)];n=len(p);pivots=[];row=0
    for j in range(n):
        pivot=next((i for i in range(row,len(rows))if rows[i][j]!=0),None)
        if pivot is None:continue
        rows[row],rows[pivot]=rows[pivot],rows[row];a=rows[row][j];rows[row]=[v/a for v in rows[row]]
        for i in range(len(rows)):
            if i!=row:
                a=rows[i][j];rows[i]=[v-a*w for v,w in zip(rows[i],rows[row])]
        pivots.append(j);row+=1
        if row==len(rows):break
    result=[]
    for j in range(n):
        if j in pivots:continue
        v=[F(0)for _ in range(n)];v[j]=F(1)
        for i,pivot in enumerate(pivots):v[pivot]=-rows[i][j]
        assert sum(a*b for a,b in zip(p,v))==0 and sum(a*b for a,b in zip(c,v))==0
        result.append(v)
    return result
