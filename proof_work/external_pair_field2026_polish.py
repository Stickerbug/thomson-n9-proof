"""Only polish existing W witnesses within the remaining per-T numerical budgets."""
import json,time
import numpy as np
from scipy.optimize import minimize
from external_pair_field2026_probe import ROOT,Residual,qs,tangent,Deadline
PREFIX='external_pair_field2026_'
def work(row,R):
    start=time.monotonic();limit=2.0 if row['name']=='T2' else 9.0;end=start+limit-.3;A=np.array(row['anchors_float']);u,v,t=map(float,row['triangle_decimal']);edges=[u,v,t];pairs=[(0,1),(0,2),(1,2)];best=dict(row['best']);cache={}
    def calc(x):
        nonlocal best
        if time.monotonic()>end:raise Deadline()
        x=np.asarray(x);key=x.tobytes()
        if cache.get('key')==key:return cache['value']
        q,r=qs(x[:2]),qs(x[2:]);Jq,Jr=tangent(x[:2]),tangent(x[2:]);dq,dr=A@q,A@r;s=q@r;Dq,Dr=A@Jq,A@Jr;tri=np.vstack([[[edges[k],dq[a],dq[b]]for k,(a,b)in enumerate(pairs)],[[edges[k],dr[a],dr[b]]for k,(a,b)in enumerate(pairs)],np.column_stack([dq,dr,[s]*3])]);val,gr=R(tri,True);W=float(sum(val[:6])/5+sum(val[6:]));grad=np.zeros(4)
        for k,(a,b)in enumerate(pairs):grad[:2]+=(gr[k,1]*Dq[a]+gr[k,2]*Dq[b])/5;grad[2:]+=(gr[k+3,1]*Dr[a]+gr[k+3,2]*Dr[b])/5
        grad[:2]+=gr[6:,0]@Dq+sum(gr[6:,2])*(r@Jq);grad[2:]+=gr[6:,1]@Dr+sum(gr[6:,2])*(q@Jr);c=np.r_[.56-dq,.56-dr,.56-s];J=np.zeros((7,4));J[:3,:2]=-Dq;J[3:6,2:]=-Dr;J[6,:2]=-r@Jq;J[6,2:]=-q@Jr
        if min(c)>=-1e-12 and W<best['W']:best={'W':W,'angles':x.tolist(),'q':q.tolist(),'r':r.tolist(),'phi_q':float(sum(val[:3])),'phi_r':float(sum(val[3:6])),'psi':float(sum(val[6:])),'min_pair_separation_slack':float(min(c)),'constraints':c.tolist(),'residual_terms':val.tolist()}
        ans=(W,grad,c,J);cache.update(key=key,value=ans);return ans
    try:
        op=minimize(lambda x:(1e3*calc(x)[0],1e3*calc(x)[1]),np.array(best['angles']),jac=True,method='SLSQP',bounds=[(0,np.pi),(0,2*np.pi)]*2,constraints=[{'type':'ineq','fun':lambda x:calc(x)[2],'jac':lambda x:calc(x)[3]}],options={'maxiter':200,'ftol':1e-13});status={'success':bool(op.success),'message':str(op.message),'nit':int(op.nit),'returned_W':calc(op.x)[0]}
    except Deadline:status={'success':False,'message':'remaining numerical time budget exhausted'}
    q=np.array(best['q']);r=np.array(best['r']);dq,dr=A@q,A@r;s=q@r;tri=np.vstack([[[edges[k],dq[a],dq[b]]for k,(a,b)in enumerate(pairs)],[[edges[k],dr[a],dr[b]]for k,(a,b)in enumerate(pairs)],np.column_stack([dq,dr,[s]*3])]);rv=R(tri,dtype=np.longdouble);W=sum(rv[:6])/5+sum(rv[6:]);best.update(W_longdouble=float(W),float_vs_longdouble_abs_error=float(abs(W-best['W'])),threshold_K_over_15=row['threshold_K_over_15'],gap_W_minus_K_over_15=float(W-row['threshold_K_over_15']),ratio_W_to_threshold=float(W/row['threshold_K_over_15']),fifteen_W_minus_K=float(15*W-row['K_display']));seconds=time.monotonic()-start;return {'name':row['name'],'triangle_decimal':row['triangle_decimal'],'anchors_float':row['anchors_float'],'K_exact':row['K_exact'],'K_display':row['K_display'],'best':best,'status':status,'polish_seconds':seconds,'cumulative_case_seconds_upper':row['cumulative_case_seconds_upper']+seconds,'case_total_limit_seconds':30,'no_SDP':True}
if __name__=='__main__':
    model=json.loads((ROOT/'nonsharp_d10_root25_7599205_v10.json').read_text());R=Residual(model);data=json.loads((ROOT/(PREFIX+'data.json')).read_text());rows=[work(row,R)for row in data['rows']];out=ROOT/(PREFIX+'polish.json');assert not out.exists();out.write_text(json.dumps({'status':'finite_existing_witness_polish_only','warning':'Feasible values upper-bound inf W, not certified lower bounds.','source':str(ROOT/(PREFIX+'data.json')),'rows':rows},indent=2)+'\n');print(json.dumps(rows,indent=2))
