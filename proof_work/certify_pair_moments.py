"""Exact interval certificate: isolated family root and positive pair moments.
Run: python3 proof_work/certify_pair_moments.py
This is a finite-degree LP obstruction, not a global optimality proof.
"""
import json
from pathlib import Path
from dyadic_interval import I, BITS

L='0.71054833409295381132770417927279124376803'
U='0.71054833409295381132770417927279124376804'

def derivative(r):
    return (-2*I(3).sqrt()/r**2 + I('1.5')*r/((1-r*r)**3).sqrt()
            +6*r/((4-r*r)**3).sqrt()+6/((2-r)**3).sqrt()-6/((2+2*r)**3).sqrt())

def run(degree=100):
    dl,du=derivative(I(L)),derivative(I(U))
    assert dl.hi<0 and du.lo>0
    r=I(L,U)
    # Six distinct off-diagonal inner products and UNORDERED multiplicities.
    nodes=[1-I('1.5')*r*r,I('-0.5'),2*r*r-1,r*r/2-1,r/2,-r]
    weights=[6,3,3,6,12,6]
    previous=[I(1)]*6; current=nodes[:]
    moments=[]
    for k in range(2,degree+1):
        new=[((2*k-1)*x*p-(k-1)*q)/k for x,p,q in zip(nodes,current,previous)]
        moment=9+2*sum(w*p for w,p in zip(weights,new))
        assert moment.lo>0, ('moment not strictly positive',k,moment.pretty())
        moments.append({'degree':k,'bounds':moment.bounds(),'display':moment.pretty()})
        previous,current=current,new
    E=I(3).sqrt()+2*I(3).sqrt()/r+I('1.5')/(1-r*r).sqrt()+6/(4-r*r).sqrt()+12/(2-r).sqrt()+6/(2+2*r).sqrt()
    h=(1-r*r).sqrt()
    result={'arithmetic':'exact integer dyadic outward intervals','bits':BITS,'root_interval':[L,U],
        'derivative_at_left':dl.bounds(),'derivative_at_right':du.bounds(),
        'energy':E.bounds(),'energy_display':E.pretty(),'height_display':h.pretty(),
        'moment_definition':'M_k=sum_{i,j} P_k(x_i dot x_j)=9+2*sum unordered multiplicity*P_k(node)',
        'positive_moments':moments,
        'conclusion':'No standard two-point Legendre-polynomial LP certificate of degree <= '+str(degree)+' is sharp at this candidate.'}
    out=Path(__file__).with_name('pair_moments_certificate.json')
    # The command is reproducible; existing output is deliberately not overwritten.
    if not out.exists():out.write_text(json.dumps(result,indent=2)+'\n')
    print('Root derivative signs strictly certified. Energy enclosure:',E.pretty())
    print('M_k > 0 certified for every k=2,...,'+str(degree))
    weakest=min(moments,key=lambda row:int(row['bounds']['lo_numerator']))
    print('Smallest certified moment: degree',weakest['degree'],weakest['display'])
    print(result['conclusion'])
    return result

if __name__=='__main__':run()
