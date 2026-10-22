#!/usr/bin/env python3
"""Reproduce actual Hermite coefficient and full-domain algebraic minorant certificates.

All interval memberships and polynomial identities are checked in Lean. Rational
generation and candidate square roots carry no mathematical trust.
"""
from pathlib import Path
from fractions import Fraction as F
from math import isqrt,comb
import argparse,copy,hashlib,json
from export_semantic_inputs import rounded,mul,sub,neg

PV=Path(__file__).resolve().parent
T=PV/'hermite_inputs';OUT=PV/'formal/ThomsonNine'
MANIFEST=PV/'hermite_coefficients_manifest.json'
INPUTS=['semantic_inputs/radius_inputs.json','independent_hermite_RH_result.json']

def rational(q):
    q=F(q);return f'({q.numerator} / {q.denominator} : ℚ)'
def interval(I):return '⟨'+', '.join(map(rational,I))+', by decide +kernel⟩'
def vector(xs):return '!['+',\n'.join(xs)+']'
def bounds(I,s):
    return '⟨'+', '.join(str(n) if n>=0 else f'({n})' for n in ((I[0]*s).__floor__(),(I[1]*s).__ceil__()))+'⟩'
def checked(cfg,archive):
    r=tuple(map(F,cfg['tight_root_interval']))
    if len(r)!=2 or not 0<r[0]<r[1]<1 or r[1]-r[0]!=F(1,1<<800):raise ValueError('invalid root bracket')
    if cfg['tight_bits']!=800 or cfg['tight_sqrt_bits']!=1024:raise ValueError('invalid precision')
    H=[tuple(map(F,I)) for I in archive['H_coefficients_ascending']]
    if len(H)!=28 or any(len(I)!=2 or I[0]>I[1] for I in H):raise ValueError('invalid H interval data')
    return r,H
def template(name,values):
    text=(T/(name+'.lean.in')).read_text()
    for key,value in values.items():
        marker='@@'+key+'@@'
        if marker not in text:raise ValueError('missing marker: '+marker)
        text=text.replace(marker,value)
    if '@@' in text:raise ValueError('unfilled marker')
    return text
def render(cfg,archive):
    r,H=checked(cfg,archive);bits=1024;s=1<<bits
    def c(q):return F(q),F(q)
    def m(I,J):return rounded(mul(I,J),bits)
    def d(I,J):return rounded(sub(I,J),bits)
    rr=m(r,r)
    nodes=[c(-1),c(F(-9,10)),d(m(rr,c(F(1,2))),c(1)),neg(r),c(F(-1,2)),c(F(-2,5)),c(F(-1,5)),d(m(rr,c(2)),c(1)),c(F(1,10)),d(c(1),m(rr,c(F(3,2)))),m(r,c(F(1,2))),c(F(9,20)),c(F(13,25)),c(F(14,25))]
    def inv(I):
        if I[0]*I[1]<=0:raise ValueError('inverse interval crosses zero')
        return rounded((1/I[1],1/I[0]),bits)
    def sqrt_interval(I):
        if I[0]<0:raise ValueError('negative sqrt argument')
        return F(isqrt((I[0].numerator*s*s)//I[0].denominator),s),F(isqrt((I[1].numerator*s*s)//I[1].denominator)+1,s)
    inverse=[[inv(sub(I,J)) if i!=j else c(0) for j,J in enumerate(nodes)] for i,I in enumerate(nodes)]
    sq=[sqrt_interval((2-2*I[1],2-2*I[0])) for I in nodes];values=list(map(inv,sq))
    matrix=[[sum((F(comb(i,k),comb(27,k))*comb(j,k)*(-1)**(j-k)*2**k for k in range(min(i,j)+1)),F(0)) for j in range(28)] for i in range(28)]
    return {
        'ActualHermiteScalar':template('ActualHermiteScalar',{
            'INVERSE':vector([vector(list(map(interval,row))) for row in inverse])+' i j',
            'SQRT':vector(list(map(interval,sq))),'VALUE':vector(list(map(interval,values))),
            'NODE_INPUT':vector([bounds(I,s) for I in nodes]),
            'INVERSE_INPUT':vector([vector([bounds(I,s) for I in row]) for row in inverse])+' i j',
            'VALUE_INPUT':vector([bounds(I,s) for I in values])}),
        'ActualHermiteBounds':template('ActualHermiteBounds',{'H_INTERVALS':vector(list(map(interval,H)))}),
        'ActualQuotientBernstein':template('ActualQuotientBernstein',{
            'MATRIX':vector([vector(list(map(rational,row))) for row in matrix]),
            'MATRIX_INPUT':vector([vector([bounds((q,q),s) for q in row]) for row in matrix])})}
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');ap.add_argument('--self-test',action='store_true');args=ap.parse_args()
    cfg,archive=[json.loads((PV/n).read_text()) for n in INPUTS];out=render(cfg,archive)
    if args.self_test:
        for case in ['reversed','precision','missing','malformed']:
            cc,aa=copy.deepcopy(cfg),copy.deepcopy(archive)
            if case=='reversed':cc['tight_root_interval'].reverse()
            elif case=='precision':cc['tight_sqrt_bits']=1023
            elif case=='missing':aa['H_coefficients_ascending'].pop()
            else:aa['H_coefficients_ascending'][0]=['1','0']
            try:checked(cc,aa)
            except ValueError:continue
            raise RuntimeError('negative test accepted: '+case)
    record={'schema_version':1,'hermite_coefficients':28,'quotient_degree_bound':27,'bernstein_domain':['-1','1'],'generated_modules':list(out),
        'scope':'Actual constructed H coefficient intervals and algebraic Coulomb minorant. Final global ThomsonNineClaim remains separate.',
        'inputs_sha256':{n:hashlib.sha256((PV/n).read_bytes()).hexdigest() for n in INPUTS},
        'templates_sha256':{str(q.relative_to(PV)):hashlib.sha256(q.read_bytes()).hexdigest() for q in sorted(T.glob('*.lean.in'))},
        'source_sha256':{n:hashlib.sha256(s.encode()).hexdigest() for n,s in out.items()}}
    text=json.dumps(record,indent=2)+'\n'
    if args.check:
        if MANIFEST.read_text()!=text or any((OUT/(n+'.lean')).read_text()!=s for n,s in out.items()):raise SystemExit('Hermite certificate sources or manifest are stale')
    else:
        for n,s in out.items():
            q=OUT/(n+'.lean')
            if not q.exists() or q.read_text()!=s:q.write_text(s)
        MANIFEST.write_text(text)
    print('ACTUAL_HERMITE_COEFFICIENTS_PASS: H28, Q Bernstein [-1,1]; check='+str(args.check))
if __name__=='__main__':main()
