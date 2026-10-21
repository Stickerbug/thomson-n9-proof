"""Independent full-source-box local Hessian and Gram-graph arithmetic."""
from pathlib import Path
from fractions import Fraction as Q
from math import comb
from hashlib import sha256
from time import monotonic
import json
from independent_integer_interval import Box,InvalidMath,S
ZERO=Box(0);ONE=Box(1)
def need(ok,msg):
    if not ok:raise InvalidMath(msg)
def decode(x):return Box(Q(int(x['lo_numerator']),1<<int(x['denominator_power_of_two'])),Q(int(x['hi_numerator']),1<<int(x['denominator_power_of_two'])))
def square(x):
    a=0 if x.l<=0<=x.h else min(x.l*x.l,x.h*x.h);b=max(x.l*x.l,x.h*x.h);return Box(a//S,-((-b)//S),True)
def powers(x,n):
    result=[ONE]
    for i in range(1,n+1):
        if i%2==0:result.append(square(result[i//2]))
        else:result.append(result[-1]*x)
    return result
def shift_axis(poly,center,axis):
    result={};cp=powers(center,max(e[axis]for e in poly))
    for ex,value in poly.items():
        for k in range(ex[axis]+1):
            target=list(ex);target[axis]=k;target=tuple(target);result[target]=result.get(target,ZERO)+value*comb(ex[axis],k)*cp[ex[axis]-k]
    return result
def shift(poly,center):
    for axis in range(3):poly=shift_axis(poly,center[axis],axis)
    return poly
def derivative(poly,axis):
    result={}
    for e,value in poly.items():
        if e[axis]:target=list(e);target[axis]-=1;result[tuple(target)]=value*e[axis]
    return result
def evaluate(poly,domain):
    if not poly:return ZERO
    cache=[powers(domain[i],max(e[i]for e in poly))for i in range(3)];total=ZERO
    for e,value in poly.items():
        for i in range(3):value=value*cache[i][e[i]]
        total=total+value
    return total
def jet(poly,domain):
    first=[derivative(poly,i)for i in range(3)];gradient=[evaluate(v,domain)for v in first];H=[[None]*3 for _ in range(3)]
    for i in range(3):
        for j in range(i,3):H[i][j]=H[j][i]=evaluate(derivative(first[i],j),domain)
    return gradient,H
def rational_unit_lower(W,n):
    need(len(W)==n and all(len(row)==n for row in W),'W dimension mismatch');W=[[Q(v)for v in row]for row in W];need(all(W[i][j]==int(i==j)for i in range(n)for j in range(i,n)),'W not exact unit lower triangular');inverse=[[Q(i==j)for j in range(n)]for i in range(n)]
    for i in range(n):
        for j in range(i):inverse[i][j]=-sum((W[i][k]*inverse[k][j]for k in range(j,i)),Q(0))
    need(all(sum((W[i][k]*inverse[k][j]for k in range(n)),Q(0))==int(i==j)for i in range(n)for j in range(n)),'W inverse product failed');return W,inverse
def transform(H,W):
    n=len(W);result=[[None]*n for _ in range(n)]
    for i in range(n):
        for j in range(i,n):result[i][j]=result[j][i]=sum((H[a][b]*W[i][a]*W[j][b]for a in range(n)for b in range(n)),ZERO)
    return result
def ldl(H):
    n=len(H);L=[[ONE if i==j else ZERO for j in range(n)]for i in range(n)];D=[]
    for i in range(n):
        pivot=H[i][i]-sum((square(L[i][j])*D[j]for j in range(i)),ZERO);need(pivot.l>0,'strict LDL pivot nonpositive at '+str(i));D.append(pivot)
        for j in range(i+1,n):L[j][i]=(H[j][i]-sum((L[j][k]*L[i][k]*D[k]for k in range(i)),ZERO))/pivot
    return L,D
def graph(v,t):
    need(-S<v.l<=v.h<S and -S<t.l<=t.h<S,'graph arguments must be strictly inside unit interval');A=ONE-square(v);B=ONE-square(t);need(A.l>0 and B.l>0,'graph radical factors not positive');s=(A*B).sqrt();b=v*t-s;bv=t+v*B/s;bt=v+t*A/s;bvv=B/(A*s);btt=A/(B*s);bvt=ONE-v*t/s;return b,[bv,bt],[[bvv,bvt],[bvt,btt]],s
def graph_hessian(Rgrad,Rh,db,ddb):
    # x(v,t)=(b(v,t),v,t); J has rows (b_v,b_t),(1,0),(0,1).
    J=[[db[0],db[1]],[ONE,ZERO],[ZERO,ONE]];result=[[None]*2 for _ in range(2)]
    for i in range(2):
        for j in range(i,2):result[i][j]=result[j][i]=sum((J[a][i]*Rh[a][b]*J[b][j]for a in range(3)for b in range(3)),ZERO)+Rgrad[0]*ddb[i][j]
    return result
def serial_matrix(M):return [[v.serial()for v in row]for row in M]
def run_row(index,row,poly,node_map,binding):
    begin=monotonic();labels=row['labels'];center=[node_map[k]for k in labels];sourcebox=[decode(v)for v in row['box']];oldcenter=[decode(v)for v in row['center_intervals']];need(all(old.lo<=new.lo<=new.hi<=old.hi for new,old in zip(center,oldcenter)),'new true-center box not contained in original center');need(all(domain.lo<=c.lo<=c.hi<=domain.hi for c,domain in zip(center,sourcebox)),'sourcebox fails to contain true center');q=shift(poly,center);relative=[x-c for x,c in zip(sourcebox,center)];kind=row['kind'];boundary=kind=='lower_Gram_graph_monotonicity_and_boundary_Hessian_PD';need(boundary or kind=='interior_Hessian_PD_on_convex_cube','unknown local kind');W,inverse=rational_unit_lower(row['congruence_W'],2 if boundary else 3)
    result={'row_index':index,'labels':labels,'kind':kind,'sourcebox':[v.serial()for v in sourcebox],'new_center_intervals':[v.serial()for v in center],'original_center_intervals':[v.serial()for v in oldcenter],'center_containment_checked':True,'original_sourcebox_preserved_exactly':True,'relative_sourcebox':[v.serial()for v in relative],'congruence_W':[[str(v)for v in rr]for rr in W],'W_inverse':[[str(v)for v in rr]for rr in inverse],'W_exact_unitlower_inverse_verified':True,'source_bindings':binding,'shifted_polynomial_term_count':len(q),'shifted_polynomial':[[list(e),v.serial()]for e,v in sorted(q.items())]}
    if boundary:
        need(tuple(labels)in [('G','G','B'),('C','F','F'),('D','D','D')],'unrecognized boundary center identity');b,db,ddb,radical=graph(sourcebox[1],sourcebox[2]);expanded=Box(min(sourcebox[0].l,b.l),max(sourcebox[0].h,b.h),True);expanded_relative=[expanded-center[0],relative[1],relative[2]];grad,H=jet(q,expanded_relative);result.update({'graph_u_interval':b.serial(),'expanded_u_hull':expanded.serial(),'expanded_domain_relative':[v.serial()for v in expanded_relative],'R_gradient_on_expanded_hull':[v.serial()for v in grad],'R_Hessian_on_expanded_hull':serial_matrix(H),'graph_sqrt_D':radical.serial(),'graph_first_derivatives':[v.serial()for v in db],'graph_second_derivatives':serial_matrix(ddb),'strict_R_u_positive':grad[0].l>0});need(grad[0].l>0,'boundary R_u not strictly positive');Htarget=graph_hessian(grad,H,db,ddb);result['boundary_center_identity']='exact algebra: GGB sqrtD=2r(1-r^2); CFF b(F,F)=2F^2-1=C; DDD b(-1/2,-1/2)=-1/2; 0<r<1'
    else:
        grad,Htarget=jet(q,relative);result['R_gradient_on_sourcebox']=[v.serial()for v in grad]
    result['target_Hessian']=serial_matrix(Htarget);pre=transform(Htarget,W);result['preconditioned_Hessian']=serial_matrix(pre)
    try:L,D=ldl(pre)
    except InvalidMath as exc:result.update({'status':'INDEPENDENT_LOCAL_ARITHMETIC_FAILED','failure':str(exc),'elapsed_seconds':monotonic()-begin});return result
    result.update({'status':'INDEPENDENT_LOCAL_FULL_SOURCEBOX_ARITHMETIC_PASS','LDL_L':serial_matrix(L),'LDL_pivots':[v.serial()for v in D],'strict_LDL_lower_bounds':[str(v.lo)for v in D],'pivot_lower_display':[float(v.lo)for v in D],'elapsed_seconds':monotonic()-begin,'exact_contact_premise':'R(center)=0 and interior gradient=0, or boundary pulledback G(center)=0 and gradient=0, follow from the separate exact45 contact/Hermite interpolation theorems; no interval zero containment is used.'});return result
def main():
    p=Path(__file__).resolve().parent;begin=monotonic();lr=(p.parent/'d10_relative_normal_exact2026_locals.json').read_bytes();hr=(p/'independent_hermite_RH_result.json').read_bytes();nr=(p/'independent_kernel_refined_result.json').read_bytes();localsdata=json.loads(lr);Hdata=json.loads(hr);Ndata=json.loads(nr);need(Hdata['status']=='INDEPENDENT_H27_RH_BINDING_PASS','independent H/R prerequisite failed');need(Hdata['root_interval']==Ndata['root_interval'],'H/N radius mismatch');poly={tuple(e):Box(*v)for e,v in Hdata['R_coefficients']};r=Box(*Ndata['root_interval']);node_map={'A':1-Q(3,2)*r*r,'B':2*r*r-1,'C':r*r/2-1,'D':Box(Q(-1,2)),'F':r/2,'G':-r};need(0<r.lo<=r.hi<1,'boundary center identity radius premise fails');binding={'d10_relative_normal_exact2026_locals.json':sha256(lr).hexdigest(),'independent_hermite_RH_result.json':sha256(hr).hexdigest(),'independent_kernel_refined_result.json':sha256(nr).hexdigest()};rows=localsdata['rows'];interior=[i for i,row in enumerate(rows)if row['kind']=='interior_Hessian_PD_on_convex_cube'];boundary=[i for i,row in enumerate(rows)if row['kind']=='lower_Gram_graph_monotonicity_and_boundary_Hessian_PD'];need(len(rows)==12 and len(interior)==9 and len(boundary)==3,'expected9interior/3boundary interleaved rows');results={};pending=interior+boundary
    try:
        for index in interior+boundary:
            result=run_row(index,rows[index],poly,node_map,binding);name='independent_local_'+str(index).zfill(2)+'_'+''.join(rows[index]['labels'])+'.json'
            with (p/name).open('x')as f:json.dump(result,f,indent=2);f.write('\n')
            results[str(index)]={'status':result['status'],'file':name,'sha256':sha256((p/name).read_bytes()).hexdigest(),'elapsed_seconds':result['elapsed_seconds'],'pivot_lower_display':result.get('pivot_lower_display'),'failure':result.get('failure')};pending.remove(index);print(json.dumps({'row_index':index,'labels':rows[index]['labels'],**results[str(index)]}),flush=True)
    finally:
        allpass=not pending and all(x['status']=='INDEPENDENT_LOCAL_FULL_SOURCEBOX_ARITHMETIC_PASS'for x in results.values());out={'status':'INDEPENDENT_TWELVE_LOCAL_ARITHMETIC_PASS_CONDITIONAL_ON_EXACT_CONTACTS'if allpass else'INDEPENDENT_LOCAL_ARITHMETIC_INCOMPLETE_OR_FAILED','bits':640,'interior_count':len(interior),'boundary_count':len(boundary),'rows':results,'pending_row_indices':pending,'source_sha256':binding,'elapsed_seconds':monotonic()-begin,'scope':'Full original source boxes; independent translated-polynomial Hessians, boundary expanded-u monotonicity and graph chain rule, exact rational W invertibility and strict interval LDL. Conditional on separate exact45 contact/Hermite interpolation theorems; no global tree proof.'}
        with (p/'independent_local_arithmetic_result.json').open('x')as f:json.dump(out,f,indent=2);f.write('\n')
        print(json.dumps(out),flush=True)
if __name__=='__main__':main()
