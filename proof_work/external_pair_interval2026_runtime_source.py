#!/usr/bin/env python3
"""Single bounded I384 Horner attempt, four charts, every pending node retained."""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
from collections import deque, Counter
import json,hashlib,time
from dyadic_interval import I,S,BITS,ceildiv
BASE=Path(__file__).resolve().parent
PREFIX='external_pair_interval2026_'
MODEL=BASE/'nonsharp_d10_root25_7599205_v10.json'
REPORT=BASE/'nonsharp_d10_root25_7599205_v10_result.json'
SOURCE=BASE/'two_other_valleys2026_probe.json'
M=F(1,25000);LIMIT=F(14,25);Z=I(0);O=I(1)
def square(a):
 lo=0 if a.lo<=0<=a.hi else min(a.lo*a.lo,a.hi*a.hi)
 return I(lo//S,ceildiv(max(a.lo*a.lo,a.hi*a.hi),S),raw=True)
def chart(a,b,sign):
 aa,bb=square(a),square(b);d=O+aa+bb
 q=[(2*a)/d,(2*b)/d,sign*(O-aa-bb)/d]
 return [I(max(-S,z.lo),min(S,z.hi),raw=True) for z in q]
def dot(a,b):
 z=sum((x*y for x,y in zip(a,b)),Z)
 return I(max(-S,z.lo),min(S,z.hi),raw=True)
def anchors(u,v,t):
 u,v,t=map(I,(u,v,t));h=(O-square(u)).sqrt()
 g=O+2*u*v*t-square(u)-square(v)-square(t)
 return [[O,Z,Z],[u,h,Z],[v,(t-u*v)/h,g.sqrt()/h]]
def tree(poly,n,axis=0):
 if axis==n:return I(sum(poly.values(),F(0)))
 groups={}
 for p,c in poly.items():groups.setdefault(p[axis],{})[p]=c
 return axis,tuple((e,tree(d,n,axis+1))for e,d in sorted(groups.items(),reverse=True))
def evaluate(tr,x):
 if isinstance(tr,I):return tr
 ax,ts=tr;e0,ch=ts[0];z=evaluate(ch,x);prev=e0
 for e,ch in ts[1:]:
  for _ in range(prev-e):z=z*x[ax]
  z=z+evaluate(ch,x);prev=e
 for _ in range(prev):z=z*x[ax]
 return z
def rational_value(poly,p):
 return sum((c*p[0]**e[0]*p[1]**e[1]*p[2]**e[2]for e,c in poly.items()),F(0))
def clip(a):return I(max(-S,a.lo),min(a.hi,I(LIMIT).hi),raw=True)
def prepare():
 model=json.loads(MODEL.read_text());report=json.loads(REPORT.read_text())
 assert report['status']=='certified' and report['pending']==0 and report['domain']==['-1','14/25']
 assert hashlib.sha256(MODEL.read_bytes()).hexdigest()==report['model_sha256']
 poly={tuple(k):F(c)for k,c in model['residual_monomial']}
 row=next(r for r in json.loads(SOURCE.read_text())['results']if r['name']=='T2')
 u,v,t=map(F,row['triangle_decimal']);A=anchors(u,v,t);full=tree(poly,3);fixed=[]
 for edge in (u,v,t):
  d={}
  for (i,j,k),c in poly.items():d[(j,k)]=d.get((j,k),F(0))+c*edge**i
  fixed.append(tree({k:c for k,c in d.items()if c},2))
 checks=[]
 for p in [(F(0),F(0),F(0)),(u,v,t),(F(-3,4),F(-1,4),F(1,3))]:
  z=evaluate(full,list(map(I,p)));a=rational_value(poly,p)
  assert F(z.lo,S)<=a<=F(z.hi,S)
  checks.append({'point':list(map(str,p)),'interval':z.bounds(),'exact':str(a)})
 assert 15*M>F(row['budget_exact'])
 return full,fixed,A,row,checks

def run(seconds=59,max_nodes=5000):
 for suffix in ['result.json','trace.json','pending.json']:
  assert not(BASE/(PREFIX+suffix)).exists(),'refuse overwrite'
 start=time.monotonic();full,fixed,A,t2,sanity=prepare();deadline=start+seconds
 nodes=[];todo=deque();roots=[];cache={};counts=Counter();visited=0;hard=[]
 for signs in [(1,1),(1,-1),(-1,1),(-1,-1)]:
  n={'id':len(nodes),'parent':None,'root':len(roots),'signs':list(signs),'depth':0,'box':[[-S,S]for _ in range(4)]}
  roots.append(n['id']);todo.append(n['id']);nodes.append(n)
 caphi=I(LIMIT).hi;threshold=I(M).hi
 def qbox(sign,bb):
  key=(sign,)+tuple(v for pair in bb for v in pair)
  if key not in cache:
   q=chart(I(*bb[0],raw=True),I(*bb[1],raw=True),sign)
   cache[key]={'q':q,'dots':[dot(a,q)for a in A],'phi':None}
  return cache[key]
 def phi(data):
  if data['phi'] is None:
   ds=list(map(clip,data['dots']));ls=[];ws=[]
   for k,(a,b)in enumerate(combinations(range(3),2)):
    z=evaluate(fixed[k],[ds[a],ds[b]]);ls.append(max(0,z.lo));ws.append(z.hi-z.lo)
   data['phi']=sum(ls),ws
  return data['phi']
 while todo and visited<max_nodes and time.monotonic()<deadline:
  nid=todo.popleft();n=nodes[nid];visited+=1;bb=n['box']
  q=qbox(n['signs'][0],bb[:2]);r=qbox(n['signs'][1],bb[2:]);qr=dot(q['q'],r['q'])
  dots=q['dots']+r['dots']+[qr]
  violation=next((j for j,z in enumerate(dots)if z.lo>caphi),None)
  if violation is not None:
   n.update(action='exclude_pair_cap',dot_index=violation,dot=dots[violation].bounds());counts['excluded']+=1;continue
  qp,qw=phi(q);rp,rw=phi(r);ps=[];widths=qw+rw
  for a,b in zip(q['dots'],r['dots']):
   z=evaluate(full,[clip(a),clip(b),clip(qr)]);ps.append(max(0,z.lo));widths.append(z.hi-z.lo)
  wlo=(qp+rp)//5+sum(ps)
  n.update(W_lower_numerator=str(wlo),W_denominator_power_of_two=BITS,dot_intervals=[z.bounds()for z in dots],residual_width_max_numerator=str(max(widths)))
  if wlo>=threshold:n['action']='accept_W';counts['accepted']+=1;continue
  n['action']='split';counts['split']+=1
  ax=max(range(4),key=lambda j:bb[j][1]-bb[j][0]);mid=(bb[ax][0]+bb[ax][1])//2;assert bb[ax][0]<mid<bb[ax][1];kids=[]
  for side in (0,1):
   cb=[p[:]for p in bb];cb[ax]=[bb[ax][0],mid]if side==0 else[mid,bb[ax][1]]
   child={'id':len(nodes),'parent':nid,'root':n['root'],'signs':n['signs'],'depth':n['depth']+1,'box':cb}
   kids.append(child['id']);nodes.append(child);todo.append(child['id'])
  n.update(axis=ax,midpoint_numerator=str(mid),children=kids)
  if len(hard)<12 or n['depth']>=min(h['depth']for h in hard):
   hard.append({k:n[k]for k in ['id','depth','box','W_lower_numerator','residual_width_max_numerator','dot_intervals']})
   hard=sorted(hard,key=lambda h:(-h['depth'],int(h['W_lower_numerator'])))[:12]
 elapsed=time.monotonic()-start;pending=list(todo)
 for i in pending:nodes[i]['action']='pending'
 frontier=[n for n in nodes if n['action']in ['accept_W','exclude_pair_cap','pending']];coverage=[]
 for root in range(4):
  volumes=Counter()
  for n in frontier:
   if n['root']==root:volumes[n['action']]+=F(16,1<<n['depth'])
  assert sum(volumes.values(),F(0))==16
  coverage.append({'root':root,'volume_by_action':{k:str(v)for k,v in volumes.items()},'total':'16'})
 result={'status':'budget_exhausted'if todo else'certified','claim_proved':not todo,'stopping_reason':('node_limit'if visited>=max_nodes else'time_limit')if todo else'all_four_roots_closed',
 'claim':'Fixed rational T2 W>=1/25000 on seven pair-cap inequalities','threshold':str(M),'bits':BITS,'seconds_budget':seconds,'node_budget':max_nodes,'elapsed_seconds':elapsed,
 'T2_triangle_exact':t2['triangle_decimal'],'T2_budget_exact':t2['budget_exact'],'fifteen_threshold_minus_budget_exact':str(15*M-F(t2['budget_exact'])),
 'processed_nodes':visited,'total_tree_nodes':len(nodes),'pending':len(pending),'counts':dict(counts),'max_depth':max(n['depth']for n in nodes),'roots':roots,'coverage':coverage,
 'root_diagnostics':[{k:v for k,v in nodes[i].items()if k!='box'}for i in roots],'hardboxes':hard,'cache_pointboxes':len(cache),'sanity_checks':sanity,
 'dependencies':{str(p):hashlib.sha256(p.read_bytes()).hexdigest()for p in [MODEL,REPORT,SOURCE,BASE/'dyadic_interval.py',Path(__file__)]},
 'old_certificate_used':'Matching exact model hash with report certified/pending0: actual geometric R>=0 when every dot<=14/25. Old 202923-node verifier not rerun.',
 'chart_coverage':'For each sphere sign=sign(z), x=q_x/(1+abs(z)), y=q_y/(1+abs(z)); x^2+y^2<=1 subset [-1,1]^2. Four square-product roots cover all sphere pairs.',
 'conditional_clipping':'Unit identities imply dots in [-1,1]; on the feasible cap subset truncate high to ceil_I384(14/25). Exclude only if dot low>ceil_I384(14/25).',
 'interval_method':'I384 sparse nested Horner. Each residual lower replaced by max(0,low) using old global certificate; Wlow=floor((phiQlow+phiRlow)/5)+sum psiLow.',
 'warning':'Unresolved Horner lower bounds are not negative witnesses; all pending retained. Fixed rational T2 only, no enclosing neighborhood or true-root assertion.',
 'next_implementation':'Consider restricting existing 3D integer Bernstein R by rational de Casteljau. No new 4D tensor, no SDP, no extra run.',
 'failed_start_receipt':'bash742 exit2 no script opened, collected; fs backend said Created but file could not be executed. No interval nodes ran.'}
 (BASE/(PREFIX+'trace.json')).write_text(json.dumps({'bits':BITS,'nodes':nodes},indent=2)+'\n')
 (BASE/(PREFIX+'pending.json')).write_text(json.dumps({'bits':BITS,'nodes':[nodes[i]for i in pending]},indent=2)+'\n')
 (BASE/(PREFIX+'result.json')).write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:result[k]for k in ['status','stopping_reason','elapsed_seconds','processed_nodes','total_tree_nodes','pending','counts','max_depth','coverage']},indent=2),flush=True)
 return result
if __name__=='__main__':run()
