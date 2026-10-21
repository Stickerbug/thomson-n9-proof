"""Independently evaluate a pre-existing, known false rational residual kernel."""
from pathlib import Path
from fractions import Fraction as Q
from hashlib import sha256
import json
D=Path(__file__).resolve().parent

def evaluate(terms,point):
    result=Q(0)
    for exponents,coeff in terms:
        value=Q(coeff)
        for t,k in zip(point,exponents):value*=t**k
        result+=value
    return result

def main():
    source=D.parent/'nonsharp_d10_root25_759925_v9.json';wpath=D.parent/'nonsharp_d10_root25_759925_v9_negative_witness.json'
    raw=source.read_bytes();m=json.loads(raw);w=json.loads(wpath.read_bytes());x,y,z=point=tuple(map(Q,w['point']))
    gram=1+2*x*y*z-x*x-y*y-z*z
    residual=evaluate(m['residual_monomial'],point)
    h=lambda t:sum(Q(v)*t**k for k,v in enumerate(m['h_monomial']))
    scalar=sum(h(t)-evaluate(m['F_monomial'],(Q(1),t,t)) for t in point)-7*evaluate(m['F_monomial'],point)-Q(m['c'])
    checks={'source_digest':sha256(raw).hexdigest()=='d60570b5e9798271f25c2cd0503ab8b40cf0de4d3870bfb029a940e49f77d7c8','root_membership':all(Q(-1)<=t<=Q(14,25) for t in point),'sorted':x<=y<=z,'gram_positive':gram>0,'stored_gram_matches':gram==Q(w['gram_determinant']),'known_residual_matches':residual==Q(w['residual']),'independent_scalar_identity':residual==scalar,'strictly_negative':residual<0}
    result={'status':'PASS_KNOWN_FAILED_KERNEL_REJECTED' if all(checks.values()) else 'FAIL','checks':checks,'point':[str(t) for t in point],'gram_determinant':str(gram),'residual':str(residual),'source_sha256':sha256(raw).hexdigest(),'scope':'Falsifies only this pre-existing rational h27/d10 residual certificate; does not refute the Thomson nine-point candidate and is not the new sharp-tree certificate.'}
    out=D/'independent_known_failed_kernel.json'
    with out.open('x') as f:json.dump(result,f,indent=2);f.write(chr(10))
    print(json.dumps(result));return 0 if all(checks.values()) else 1
if __name__=='__main__':raise SystemExit(main())
