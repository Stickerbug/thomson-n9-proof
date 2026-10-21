"""Independent robust PD verification of all reduced symmetric interval blocks."""
from pathlib import Path
from fractions import Fraction as Q
from hashlib import sha256
from copy import deepcopy
from time import monotonic
import json
from independent_candidate_bounds import Box, BITS, InvalidMath
DIMENSIONS=(9,9,7,7,5,5,3,3,1,1,0)
def need(ok,msg):
    if not ok:raise InvalidMath(msg)
def decode(x):
    need(type(x['denominator_power_of_two'])is int and x['denominator_power_of_two']==384,'expected raw I384 interval')
    lo=Q(int(x['lo_numerator']),1<<384);hi=Q(int(x['hi_numerator']),1<<384)
    need(lo<=hi,'reversed raw coefficient interval');return Box(lo,hi)
def reconstruct(indices,enclosures):
    need(len(indices)==len(enclosures)==190,'coordinate count must equal 190')
    expected={(k,i,j)for k,n in enumerate(DIMENSIONS)for i in range(n)for j in range(i,n)}
    need(len(expected)==190,'internal dimension template error')
    seen=set();values={}
    for ix,raw in zip(indices,enclosures):
        need(len(ix)==3 and all(type(x)is int for x in ix),'indices must be integer triples')
        k,i,j=ix;need(i<=j,'noncanonical lower-triangle index: symmetry invalid');key=(k,i,j)
        need(key not in seen,'duplicate index');need(key in expected,'index outside fixed block dimensions');seen.add(key);values[key]=decode(raw)
    need(seen==expected,'missing upper-triangle coordinate')
    blocks=[]
    for k,n in enumerate(DIMENSIONS):
        blocks.append([[values[k,min(i,j),max(i,j)]for j in range(n)]for i in range(n)])
    return blocks
def ldl(matrix):
    n=len(matrix);need(all(len(row)==n for row in matrix),'matrix is not square')
    for i in range(n):
        for j in range(n):
            need(matrix[i][j].serial()==matrix[j][i].serial(),'matrix intervals are not symmetric')
    L=[[Box(0)for _ in range(n)]for _ in range(n)];D=[]
    for j in range(n):
        pivot=matrix[j][j]
        for k in range(j):pivot=pivot-L[j][k]*L[j][k]*D[k]
        need(pivot.lo>0,f'LDL pivot {j} lacks strictly positive lower bound');D.append(pivot);L[j][j]=Box(1)
        for i in range(j+1,n):
            v=matrix[i][j]
            for k in range(j):v=v-L[i][k]*L[j][k]*D[k]
            L[i][j]=v/pivot
    return {'dimension':n,'pivots':[d.serial()for d in D],'minimum_pivot_lower':None if not D else str(min(d.lo for d in D)),'L_enclosures':[[x.serial()for x in row]for row in L],'status':'VACUOUS_EMPTY_PSD'if n==0 else'ALL_SYMMETRIC_MATRICES_IN_ENCLOSURES_PD'}
def main():
    start=monotonic();out=Path(__file__).resolve().parent;source=out.parent/'d10_relative_normal_exact2026_certificate.json';raw=source.read_bytes();data=json.loads(raw)
    # Read mathematical coordinates only; saved PSD_LDL is deliberately not accessed.
    indices=data['indices'];enclosures=data['reduced_solution_enclosures'];blocks=reconstruct(indices,enclosures)
    positive=[{'k':k,**ldl(B),'matrix_enclosures':[[x.serial()for x in row]for row in B]}for k,B in enumerate(blocks)]
    negatives=[]
    def reject(name,fn):
        try:fn()
        except InvalidMath as e:negatives.append({'case':name,'status':'REJECTED_MATHEMATICALLY','reason':str(e)});return
        raise AssertionError('invalid test accepted: '+name)
    dup=deepcopy(indices);dup[1]=dup[0].copy();reject('duplicate_index',lambda:reconstruct(dup,enclosures))
    lower=deepcopy(indices);lower[1]=[0,1,0];reject('lower_triangle_noncanonical_index',lambda:reconstruct(lower,enclosures))
    reject('deleted_coordinate',lambda:reconstruct(indices[:-1],enclosures[:-1]))
    asym=[row.copy()for row in blocks[0]];asym[0][1]=Box(-100);reject('nonsymmetric_matrix',lambda:ldl(asym))
    neg=[row.copy()for row in blocks[0]];neg[0][0]=Box(-1);reject('negative_diagonal',lambda:ldl(neg))
    reverse=deepcopy(enclosures);reverse[0]['lo_numerator']='2';reverse[0]['hi_numerator']='1';reject('reversed_interval',lambda:reconstruct(indices,reverse))
    result={'status':'INDEPENDENT_PSD_BLOCKS_PASS','bits':BITS,'dimensions':list(DIMENSIONS),'block_count':11,'coordinate_count':190,'uppertriangle_complete_no_duplicates':True,'blocks':positive,'global_minimum_pivot_lower':str(min(Q(b['minimum_pivot_lower'])for b in positive if b['dimension'])),'negative_tests':negatives,'source_sha256':sha256(raw).hexdigest(),'checker_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'independent_interval_module_sha256':sha256((out/'independent_candidate_bounds.py').read_bytes()).hexdigest(),'claim':'Every symmetric reduced B with entries in the supplied coordinate enclosures is positive definite, with empty k=10 block vacuously PSD.','remaining_premises':['Actual constructed solution belongs to these enclosures: independent 33LU validation is still required','N B N^T PSD algebra and model reconstruction not Lean formalized here'],'elapsed_seconds':monotonic()-start}
    with (out/'independent_psd_blocks_result.json').open('x')as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps({k:v for k,v in result.items()if k!='blocks'}),flush=True)
if __name__=='__main__':main()
