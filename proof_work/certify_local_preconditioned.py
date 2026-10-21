"""Rational congruence preconditioning extends the local certificate to 1e-4.
Run from workspace: python3 proof_work/certify_local_preconditioned.py
Optional --json prints exact integer interval certificate and preconditioner.
"""
import json,sys
from certify_local import I,S,n,chart_hessian,ldl

def preconditioner():
    H0=chart_hessian(0)
    L=[[I(int(i==j))for j in range(n)]for i in range(n)];D=[]
    for i in range(n):
        d=H0[i][i]-sum((L[i][k]*L[i][k]*D[k]for k in range(i)),I(0));D.append(d)
        assert d.a>0
        for j in range(i+1,n):
            t=(H0[j][i]-sum((L[j][k]*L[i][k]*D[k]for k in range(i)),I(0)))/d
            L[j][i]=I((t.a+t.b)//2,(t.a+t.b)//2,True)
    W=[[I(int(i==j))for j in range(n)]for i in range(n)]
    for i in range(n):
        for j in range(i):
            t=-sum((L[i][k]*W[k][j]for k in range(j,i)),I(0))
            W[i][j]=I((t.a+t.b)//2,(t.a+t.b)//2,True)
    # W is an exact rational unit lower triangular matrix; no claim that
    # this rounded W is the exact inverse of L is needed for congruence.
    assert all(W[i][i].a==W[i][i].b==S for i in range(n))
    return W

def congruence(W,H):
    T=[[sum((W[i][k]*H[k][j]for k in range(i+1)),I(0))for j in range(n)]for i in range(n)]
    return [[sum((T[i][k]*W[j][k]for k in range(j+1)),I(0))for j in range(n)]for i in range(n)]

def certificate():
    W=preconditioner();N=congruence(W,chart_hessian(10**4));D=ldl(N)
    assert all(5*d.a>S for d in D)
    return {'claim':'chart Hessian positive definite for every |z_a| <= 1/10000',
      'arithmetic':'exact integers with outward rounding to denominator 10^55',
      'grid_denominator':str(S),'dimension':15,'chart_halfwidth':'1/10000',
      'preconditioner_numerators':[[str(w.a)for w in row]for row in W],
      'ldl_pivot_numerators':[[str(d.a),str(d.b)]for d in D],
      'all_pivots_greater_than':'1/5',
      'minimum_lower_pivot_numerator':str(min(d.a for d in D))}

if __name__=='__main__':
    c=certificate()
    if '--json'in sys.argv: print(json.dumps(c,indent=2))
    else:
        print(c['claim'])
        print('All 15 preconditioned LDL pivots > 1/5: CERTIFIED')
        print('Minimum lower pivot =',c['minimum_lower_pivot_numerator'],'/',S)
