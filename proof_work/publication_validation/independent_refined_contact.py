"""Independent stationary-radius bisection, derivative signs, nested polynomial N."""
from pathlib import Path
from fractions import Fraction as Q
from hashlib import sha256
from time import monotonic
import json
from independent_integer_interval import Box,InvalidMath
from independent_contact_construction import construct,need
def derivative(r):
    return -2*Box(3).sqrt()/(r*r)+Q(3,2)*r/((1-r*r)*(1-r*r).sqrt())+6*r/((4-r*r)*(4-r*r).sqrt())+6/((2-r)*(2-r).sqrt())-6/((2+2*r)*(2+2*r).sqrt())
def main():
    t=monotonic();out=Path(__file__).resolve().parent;raw=(out.parent/'d10_relative_normal_exact2026_certificate.json').read_bytes();data=json.loads(raw);lo,hi=map(Q,data['root_interval']);L,U=lo,hi;dl=derivative(Box(lo));du=derivative(Box(hi));need(dl.h<0<du.l,'initial derivative signs fail');steps=[]
    while hi-lo>Q(1,1<<500):
        mid=(lo+hi)/2;dm=derivative(Box(mid));need(dm.h<0 or dm.l>0,'640-bit derivative sign unresolved')
        steps.append({'midpoint':str(mid),'derivative':dm.serial(),'side':'left_negative'if dm.h<0 else'right_positive'})
        if dm.h<0:lo=mid
        else:hi=mid
    dl=derivative(Box(lo));du=derivative(Box(hi));need(L<=lo<hi<=U and dl.h<0<du.l,'refined bracket nesting/sign failure')
    refined={'status':'INDEPENDENT_NESTED_RADIUS_BRACKET_PASS','bits':640,'source_root_interval':data['root_interval'],'root_interval':list(map(str,[lo,hi])),'width':str(hi-lo),'width_at_most_2powminus500':hi-lo<=Q(1,1<<500),'left_derivative':dl.serial(),'right_derivative':du.serial(),'bisection_steps':steps,'source_sha256':sha256(raw).hexdigest(),'calculus_premise':'strict Esecond>0 on (0,1) as in independent candidate layer; IVT and uniqueness identify same r_star','elapsed_seconds':monotonic()-t}
    with (out/'independent_refined_radius_result.json').open('x')as f:json.dump(refined,f,indent=2);f.write('\n')
    data['root_interval']=list(map(str,[lo,hi]));NN,records=construct(data);indices=[[k,i,j]for k,N in enumerate(NN)for i in range(len(N))for j in range(i,len(N))];need(indices==data['indices'],'N index order changed')
    result={'status':'INDEPENDENT_REFINED_KERNEL_COMPLEMENTS_PASS','bits':640,'root_interval':data['root_interval'],'indices':indices,'blocks':records,'source_sha256':sha256(raw).hexdigest(),'source_root_interval':[str(L),str(U)],'refined_radius_result_sha256':sha256((out/'independent_refined_radius_result.json').read_bytes()).hexdigest(),'elapsed_seconds':monotonic()-t}
    with (out/'independent_kernel_refined_result.json').open('x')as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps({'status':result['status'],'bisections':len(steps),'elapsed_seconds':monotonic()-t}),flush=True)
if __name__=='__main__':main()
