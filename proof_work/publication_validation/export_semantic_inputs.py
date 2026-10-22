#!/usr/bin/env python3
"""Reproduce finite support, stationary-radius and actual Hermite-node certificates.
All mathematical validity is checked by Lean; generation introduces no axioms.
"""
from pathlib import Path
from fractions import Fraction as F
from math import isqrt
import argparse
import copy
import hashlib
import json

PV=Path(__file__).resolve().parent
T=PV/'semantic_inputs'
OUT=PV/'formal/ThomsonNine'
MANIFEST=PV/'semantic_inputs_manifest.json'
INPUTS=['independent_kernel_refined_result.json','independent_hermite_RH_result.json','independent_local_00_AAA.json','semantic_inputs/radius_inputs.json']


def rational(q):
    q=F(q)
    return f'({q.numerator} / {q.denominator} : ℚ)'


def interval(I):
    return '⟨'+', '.join(map(rational,I))+', by decide +kernel⟩'


def mul(I,J):
    a=[x*y for x in I for y in J]
    return min(a),max(a)


def add(I,J): return I[0]+J[0],I[1]+J[1]
def neg(I): return -I[1],-I[0]
def sub(I,J): return add(I,neg(J))


def div(I,J):
    if not J[0]>0: raise ValueError('nonpositive endpoint denominator')
    a=[x/y for x in I for y in J]
    return min(a),max(a)


def power(I,n):
    P=(F(1),F(1))
    for _ in range(n): P=mul(P,I)
    return P


def rounded(I,bits):
    s=1<<bits
    return F((I[0]*s).__floor__(),s),F((I[1]*s).__ceil__(),s)


def sqrt_point(q,bits):
    if q<=0: raise ValueError('nonpositive square-root argument')
    s=1<<bits;n=isqrt((q.numerator*s*s)//q.denominator)
    return F(n,s),F(n+1,s)


def template(name,values):
    s=(T/(name+'.lean.in')).read_text()
    for k,v in values.items():
        marker='@@'+k+'@@'
        if marker not in s: raise ValueError('missing template marker: '+marker)
        s=s.replace(marker,v)
    if '@@' in s: raise ValueError('unreplaced template marker')
    return s


def checked(root,R,J,cfg):
    from export_aaa_grouped_data import checked as checked_archive
    source,_=checked_archive(R,J)
    old=tuple(map(F,root['root_interval']));new=tuple(map(F,cfg['tight_root_interval']))
    if not 0<old[0]<new[0]<new[1]<old[1]<1: raise ValueError('invalid nested radius brackets')
    if cfg['tight_bits']!=800 or new[1]-new[0]!=F(1,1<<800): raise ValueError('invalid tight bracket precision')
    if cfg['archival_sqrt_bits']!=768 or cfg['tight_sqrt_bits']!=1024: raise ValueError('unexpected sqrt witness precision')
    return [tuple(e) for e,_ in source],old,new


def endpoint(label,q,bits):
    sq=[sqrt_point(a,bits) for a in [F(3),1-q*q,4-q*q,2-q,2+2*q]]
    nums=[mul((F(-2),F(-2)),sq[0]),(3*q,3*q),(6*q,6*q),(F(6),F(6)),(F(6),F(6))]
    dens=[(q*q,q*q),mul((F(2),F(2)),power(sq[1],3)),power(sq[2],3),power(sq[3],3),power(sq[4],3)]
    terms=[rounded(div(I,J),bits) for I,J in zip(nums,dens)]
    values={'NAMESPACE':'Radius'+label,'POINT':rational(q)}
    values.update({'SQRT'+str(i):interval(I) for i,I in enumerate(sq)})
    values.update({'TERM'+str(i):interval(I) for i,I in enumerate(terms)})
    if label.endswith('Lo'):
        values['SIGN']=''' theorem derivative_neg : familyEnergyDeriv point < 0 := by
  have hn : result.hi < 0 := by decide +kernel
  have hn' : (result.hi : ℝ) < 0 := by exact_mod_cast hn
  exact lt_of_le_of_lt result_mem.2 hn'
'''
    else:
        values['SIGN']=''' theorem derivative_pos : 0 < familyEnergyDeriv point := by
  have hp : 0 < result.lo := by decide +kernel
  have hp' : (0 : ℝ) < result.lo := by exact_mod_cast hp
  exact lt_of_lt_of_le hp' result_mem.1
'''
    return template('RadiusEndpoint',values)


def render(root,R,J,cfg):
    es,old,new=checked(root,R,J,cfg)
    codes=[u*784+v*28+t for u,v,t in es]
    mask=0
    for n in codes: mask|=1<<n
    out={'AAASupport':template('AAASupport',{
        'SUPPORT':'[\n'+',\n'.join(f'  ![{u},{v},{t}]' for u,v,t in es)+'\n]',
        'CODES':'['+', '.join(map(str,codes))+']','MASK':str(mask)})}
    for label,q,b in [('Lo',old[0],768),('Hi',old[1],768),('TightLo',new[0],1024),('TightHi',new[1],1024)]:
        out['RadiusEndpoint'+label]=endpoint(label,q,b)
    bits=1024
    def c(q): return F(q),F(q)
    def m(I,J): return rounded(mul(I,J),bits)
    def d(I,J): return rounded(sub(I,J),bits)
    r2=m(new,new)
    nodes=[c(-1),c(F(-9,10)),d(m(r2,c(F(1,2))),c(1)),neg(new),c(F(-1,2)),c(F(-2,5)),c(F(-1,5)),d(m(r2,c(2)),c(1)),c(F(1,10)),d(c(1),m(r2,c(F(3,2)))),m(new,c(F(1,2))),c(F(9,20)),c(F(13,25)),c(F(14,25))]
    out['ActualHermite']=template('ActualHermite',{'NODES':'![\n'+',\n'.join('  '+interval(I) for I in nodes)+'\n]'})
    return out


def main():
    import sys
    sys.set_int_max_str_digits(100000)
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');ap.add_argument('--self-test',action='store_true');args=ap.parse_args()
    root,R,J,cfg=[json.loads((PV/n).read_text()) for n in INPUTS]
    out=render(root,R,J,cfg)
    if args.self_test:
        for case in ['reversed','precision','source_missing','outside']:
            cc,rr=copy.deepcopy(cfg),copy.deepcopy(R)
            if case=='reversed': cc['tight_root_interval'].reverse()
            elif case=='precision': cc['tight_bits']=799
            elif case=='source_missing': rr['R_coefficients'].pop()
            else: cc['tight_root_interval']=['0','1']
            try: checked(root,rr,J,cc)
            except ValueError: continue
            raise RuntimeError('negative test accepted: '+case)
    record={'schema_version':1,'source_terms':807,'hermite_nodes':14,'tight_radius_bits':800,
            'generated_modules':list(out),'scope':'Finite Lean certificates; actual H coefficient bounds and final global claim are separate.',
            'inputs_sha256':{n:hashlib.sha256((PV/n).read_bytes()).hexdigest() for n in INPUTS},
            'templates_sha256':{str(q.relative_to(PV)):hashlib.sha256(q.read_bytes()).hexdigest() for q in sorted(T.glob('*.lean.in'))},
            'source_sha256':{n:hashlib.sha256(s.encode()).hexdigest() for n,s in out.items()}}
    text=json.dumps(record,indent=2)+'\n'
    if args.check:
        if MANIFEST.read_text()!=text or any((OUT/(n+'.lean')).read_text()!=s for n,s in out.items()): raise SystemExit('semantic certificate sources or manifest are stale')
    else:
        for n,s in out.items():
            q=OUT/(n+'.lean')
            if not q.exists() or q.read_text()!=s: q.write_text(s)
        MANIFEST.write_text(text)
    print('SEMANTIC_INPUTS_PASS: 807-support, four radius endpoints, 14 actual nodes; check='+str(args.check))


if __name__=='__main__': main()
