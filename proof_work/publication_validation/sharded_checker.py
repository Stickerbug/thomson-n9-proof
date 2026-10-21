"""Recoverable independent conditional tree verification; only own exact checker imported."""
from pathlib import Path
from fractions import Fraction as Q
from math import lcm
from functools import lru_cache
from itertools import product
from hashlib import sha256
from concurrent.futures import ProcessPoolExecutor,as_completed
from collections import Counter
import json,time,os,argparse
import checker_exact as C
D=Path(__file__).resolve().parent
INPUT=D/'sharp_root_inputs.json';TREE=D/'sharp_root_tree.jsonl'
KINDS={'positive','boundary_multiplier','gram_negative','local_region','ordered_disjoint'}
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def digest(x):return sha256(canonical(x)).hexdigest()
def filehash(p):return sha256(Path(p).read_bytes()).hexdigest()
def write_new(p,data):
    p=Path(p);tmp=p.with_name('.'+p.name+'.'+str(os.getpid())+'.tmp')
    with tmp.open('x') as f:json.dump(data,f,sort_keys=True,indent=2);f.write(chr(10));f.flush();os.fsync(f.fileno())
    os.link(tmp,p)
    C.need(tmp.resolve().parent==p.resolve().parent and tmp.name=='.'+p.name+'.'+str(os.getpid())+'.tmp','temporary cleanup target')
    tmp.unlink()
def source_bindings():
    return {name:filehash(path) for name,path in {'inputs':INPUT,'tree':TREE,'exact_checker':D/'checker_exact.py','sharded_checker':Path(__file__),'co':D.parent/'d10_relative_normal_exact2026_coefficients.json','locals':D.parent/'d10_relative_normal_exact2026_locals.json','model_binding':D/'independent_model_input_binding.json'}.items()}
@lru_cache(None)
def gram_axis(n,level,index):
    d=25*(1<<level);a=39*index-d
    lin=tuple(n*a+39*i for i in range(n+1));sq=tuple(n*(n-1)*a*a+2*(n-1)*a*39*i+39*39*i*(i-1) for i in range(n+1))
    return lin,n*d,sq,n*(n-1)*d*d

def gram_numbers(levels,indices,n):
    rows=[gram_axis(n,l,i) for l,i in zip(levels,indices)];prod_den=rows[0][1]*rows[1][1]*rows[2][1];den=lcm(prod_den,*(r[3] for r in rows));factor=2*(den//prod_den);sq=[tuple(v*(den//r[3]) for v in r[2]) for r in rows]
    return tuple(den+factor*rows[0][0][i]*rows[1][0][j]*rows[2][0][k]-sq[0][i]-sq[1][j]-sq[2][k] for i,j,k in product(range(n+1),repeat=3)),den

def gram_correction(levels,indices,lam,scale):
    nums,den=gram_numbers(levels,indices,10);a=lam.numerator*scale;b=lam.denominator*den
    return tuple(-((-a*v)//b) for v in nums)

class FastMath(C.Math):
    def positive(self,tensor,levels,indices,box,lam=Q(0)):
        hh=[self.H(l,i) for l,i in zip(levels,indices)];cor=gram_correction(levels,indices,lam,self.S) if lam else (0,)*1331
        low=min(v-c+hh[0][i]+hh[1][j]+hh[2][k] for (i,j,k),v,c in zip(product(range(11),repeat=3),tensor,cor))
        if low<0:
            poly=dict(self.k)
            for p,v in C.GRAM.items():poly[p]=poly.get(p,Q(0))-lam*v
            direct=tuple(C.fl(v*self.S) for v in C.bern(poly,box,(10,10,10)))
            low=min(v+hh[0][i]+hh[1][j]+hh[2][k] for (i,j,k),v in zip(product(range(11),repeat=3),direct))
        return low

def child_geometry(box,levels,indices,axis,side):
    bb=list(box);l,r=box[axis];mid=(l+r)/2;bb[axis]=(l,mid) if side==0 else (mid,r);lv=list(levels);ix=list(indices);lv[axis]+=1;ix[axis]=2*ix[axis]+side
    return tuple(bb),tuple(lv),tuple(ix)

def scan_tree(path):
    stack=[('',C.ROOT,(0,0,0),(0,0,0))];nodes=[];leaves=Counter();th=sha256()
    with Path(path).open('rb') as f:
        while True:
            offset=f.tell();line=f.readline()
            if not line:break
            th.update(line);C.need(bool(stack),'extra structural node');node=json.loads(line);prefix,box,lv,ix=stack.pop();C.need(node['path']==prefix,'structural path gap');C.need(node['levels']==list(lv) and node['indices']==list(ix),'structural dyadic geometry');C.need(tuple(tuple(map(C.rat,p)) for p in node['box'])==box,'structural box geometry')
            typ=node['type'];meta={'path':prefix,'offset':offset,'line_end':f.tell(),'levels':list(lv),'indices':list(ix),'box':node['box'],'type':typ}
            if typ=='split':
                axis=node['axis'];C.need(type(axis) is int and 0<=axis<3,'structural split axis');meta['axis']=axis
                for side in (1,0):stack.append((prefix+str(side),*child_geometry(box,lv,ix,axis,side)))
            else:
                C.need(typ=='leaf' and node['kind'] in KINDS,'structural illegal terminal');leaves[node['kind']]+=1
            nodes.append(meta)
    C.need(not stack and bool(nodes),'structural uncovered root')
    for i in range(len(nodes)-1,-1,-1):
        node=nodes[i]
        if node['type']=='leaf':node['size']=1;node['end']=node['line_end']
        else:
            left=i+1;right=left+nodes[left]['size'];C.need(right<len(nodes) and nodes[left]['path']==node['path']+'0' and nodes[right]['path']==node['path']+'1','subtree indexing')
            node['size']=1+nodes[left]['size']+nodes[right]['size'];node['end']=nodes[right]['end']
    C.need(nodes[0]['size']==len(nodes),'structural root span')
    return nodes,dict(leaves),th.hexdigest()

def check_frontier(paths):
    C.need(bool(paths),'empty frontier');C.need(all(type(p) is str and all(c in '01' for c in p) for p in paths),'invalid frontier path')
    ordered=sorted(paths)
    for a,b in zip(ordered,ordered[1:]):C.need(not b.startswith(a),'overlapping frontier')
    C.need(sum((Q(1,1<<len(p)) for p in ordered),Q(0))==1,'frontier leaves uncovered domain')

def choose_chunks(nodes,limit):
    C.need(type(limit) is int and limit>=1,'invalid chunk size');indices=[0];selected=[];by_path={n['path']:n for n in nodes}
    while indices:
        i=indices.pop();n=nodes[i]
        if n['size']<=limit:
            selected.append({'id':'chunk-'+str(len(selected)).zfill(5),'path':n['path'],'offset':n['offset'],'end':n['end'],'size':n['size'],'levels':n['levels'],'indices':n['indices'],'box':n['box'],'ancestor_axes':[by_path[n['path'][:j]]['axis'] for j in range(len(n['path']))]})
        else:
            C.need(n['type']=='split','uncuttable oversized leaf');left=i+1;right=left+nodes[left]['size'];indices.extend((right,left))
    check_frontier([c['path'] for c in selected]);return selected

def create_manifest(run,limit):
    run=Path(run);run.mkdir(parents=True,exist_ok=False);nodes,counts,tree_sha=scan_tree(TREE);binding=source_bindings();C.need(tree_sha==binding['tree'],'tree changed during scan')
    model=json.loads((D/'independent_model_input_binding.json').read_text());C.need(model['status']=='PASS_EXPORTED_MODEL_INPUT_BINDING' and all(model['checks'].values()),'model source binding not verified');C.need(model['root_input_sha256']==binding['inputs'] and model['source_hashes']=={'co':binding['co'],'locals':binding['locals']},'model source binding hash mismatch')
    manifest={'schema':'independent-subtree-frontier-v1','bindings':binding,'root_box':[['-1','14/25']]*3,'node_count':len(nodes),'leaf_counts':counts,'chunk_limit':limit,'chunks':choose_chunks(nodes,limit),'scope':'Full root-box partition; residual nonnegative conditionally on sorted Gram-feasible D, local and original model enclosure premises.'};manifest['manifest_sha256']=digest(manifest);write_new(run/'manifest.json',manifest)
    write_new(run/'launch.json',{'pid':os.getpid(),'started_epoch':time.time(),'legacy_run':'bash-198 last observed 115000 nodes/3002.0948615219677s; registry lost, UNKNOWN_INCOMPLETE, not resumed or counted'})
    print(json.dumps({'stage':'MANIFEST_CREATED','chunks':len(manifest['chunks']),'node_count':len(nodes),'manifest_sha256':manifest['manifest_sha256']}),flush=True);return manifest

MATH=None;MANIFEST=None;RUN=None

def initialize_worker(manifest,run):
    global MATH,MANIFEST,RUN
    C.need(source_bindings()==manifest['bindings'],'worker source/input bindings changed');MATH=FastMath(json.loads(INPUT.read_bytes()));MANIFEST=manifest;RUN=Path(run)

def verify_chunk(chunk):
    started=time.monotonic();box=C.ROOT;lv=(0,0,0);ix=(0,0,0);tensor=MATH.root
    C.need(len(chunk['ancestor_axes'])==len(chunk['path']),'chunk ancestor count')
    for bit,axis in zip(chunk['path'],chunk['ancestor_axes']):
        side=int(bit);tensor=C.split_tensor(tensor,axis)[side];box,lv,ix=child_geometry(box,lv,ix,axis,side)
    C.need(list(lv)==chunk['levels'] and list(ix)==chunk['indices'] and tuple(tuple(map(C.rat,z)) for z in chunk['box'])==box,'chunk root reconstruction')
    stack=[(chunk['path'],box,lv,ix,tensor)];counts=Counter();n=sp=0;h=sha256()
    with TREE.open('rb') as f:
        f.seek(chunk['offset'])
        while f.tell()<chunk['end']:
            line=f.readline();C.need(bool(line) and f.tell()<=chunk['end'],'chunk byte span');h.update(line);C.need(bool(stack),'chunk extra node');node=json.loads(line);path,box,lv,ix,tensor=stack.pop();n+=1
            C.need(node['path']==path and node['levels']==list(lv) and node['indices']==list(ix),'chunk path/dyadic geometry');C.need(tuple(tuple(map(C.rat,z)) for z in node['box'])==box,'chunk box geometry')
            if node['type']=='split':
                axis=node['axis'];C.need(type(axis) is int and 0<=axis<3,'chunk split axis');halves=C.split_tensor(tensor,axis)
                for side in (1,0):stack.append((path+str(side),*child_geometry(box,lv,ix,axis,side),halves[side]))
                sp+=1
            else:
                C.need(node['type']=='leaf','chunk illegal termination');kind=node['kind'];ident=node.get('ident');ok=False
                if kind=='ordered_disjoint':ok=any(box[i][0]>box[j][1] for i in range(3) for j in range(i+1,3))
                elif kind=='gram_negative':ok=max(gram_numbers(lv,ix,2)[0])<0
                elif kind=='local_region':C.need(ident in MATH.local,'chunk unknown local');ok=all(a<=l<=r<=b for (l,r),(a,b) in zip(box,MATH.local[ident]))
                elif kind in ('positive','boundary_multiplier'):
                    lam=Q(0)
                    if kind=='boundary_multiplier':C.need(ident in MATH.boundary,'chunk unknown multiplier');lam=MATH.boundary[ident]
                    ok=MATH.positive(tensor,lv,ix,box,lam)>=0
                C.need(ok,'chunk invalid leaf '+str(kind)+' at '+path);counts[kind]+=1
    C.need(not stack and n==chunk['size'] and n==2*sp+1,'chunk incomplete binary subtree')
    result={'status':'PASS_COMPLETE_SUBTREE','id':chunk['id'],'path':chunk['path'],'nodes':n,'splits':sp,'leaves':sum(counts.values()),'leaf_counts':dict(counts),'chunk_tree_sha256':h.hexdigest(),'manifest_sha256':MANIFEST['manifest_sha256'],'bindings':MANIFEST['bindings'],'elapsed_seconds':time.monotonic()-started,'worker_pid':os.getpid()};write_new(RUN/(chunk['id']+'.json'),result);return result

def validate_manifest(manifest,nodes,counts,tree_sha):
    core={k:v for k,v in manifest.items() if k!='manifest_sha256'};C.need(digest(core)==manifest['manifest_sha256'],'manifest digest');C.need(manifest['bindings']==source_bindings() and manifest['bindings']['tree']==tree_sha,'aggregate actual artifact bindings');C.need(manifest['node_count']==len(nodes) and manifest['leaf_counts']==counts,'aggregate structure counts');chunks=manifest['chunks'];check_frontier([c['path'] for c in chunks]);by_path={n['path']:n for n in nodes}
    for i,c in enumerate(chunks):
        C.need(c['id']=='chunk-'+str(i).zfill(5),'chunk identifier');C.need(c['path'] in by_path,'frontier path absent from tree');n=by_path[c['path']]
        for key in ('offset','end','size','levels','indices','box'):C.need(c[key]==n[key],'frontier metadata '+key)
        C.need(c['size']<=manifest['chunk_limit'],'oversized frontier chunk');C.need(c['ancestor_axes']==[by_path[c['path'][:j]]['axis'] for j in range(len(c['path']))],'frontier ancestor split axes')

def aggregate(run,elapsed=None):
    run=Path(run);manifest=json.loads((run/'manifest.json').read_text());nodes,counts,tree_sha=scan_tree(TREE);validate_manifest(manifest,nodes,counts,tree_sha);totals=Counter();node_sum=split_sum=0;reports=[]
    with TREE.open('rb') as f:
        for c in manifest['chunks']:
            path=run/(c['id']+'.json');raw=path.read_bytes();r=json.loads(raw);C.need(r['status']=='PASS_COMPLETE_SUBTREE','chunk not PASS');C.need(r['id']==c['id'] and r['path']==c['path'],'chunk result identity');C.need(r['manifest_sha256']==manifest['manifest_sha256'] and r['bindings']==manifest['bindings'],'chunk result binding');C.need(r['nodes']==c['size'] and r['nodes']==2*r['splits']+1 and r['leaves']==r['splits']+1 and r['leaves']==sum(r['leaf_counts'].values()),'chunk result counts');f.seek(c['offset']);C.need(sha256(f.read(c['end']-c['offset'])).hexdigest()==r['chunk_tree_sha256'],'chunk physical bytes hash');totals.update(r['leaf_counts']);node_sum+=r['nodes'];split_sum+=r['splits'];reports.append({'id':c['id'],'result_sha256':sha256(raw).hexdigest(),'path':c['path']})
    upper_splits=len(manifest['chunks'])-1;C.need(dict(totals)==counts,'aggregate leaf reason counts');C.need(node_sum+upper_splits==len(nodes),'aggregate missing nodes');C.need(2*(split_sum+upper_splits)+1==len(nodes),'aggregate split count')
    result={'status':'VERIFIED_CONDITIONAL_COVERAGE_SHARDED','conditional_only':True,'nodes':len(nodes),'splits':split_sum+upper_splits,'leaves':sum(totals.values()),'leaf_counts':dict(totals),'chunks':len(reports),'frontier_prefix_free_complete':True,'upper_structure_splits':upper_splits,'manifest_sha256':manifest['manifest_sha256'],'bindings':manifest['bindings'],'chunk_reports':reports,'elapsed_seconds':elapsed,'legacy_run_status':'UNKNOWN_INCOMPLETE; last observed115000 nodes, not counted','scope':'Complete tree partition of B=[-1,14/25]^3 and conditional residual nonnegativity on D={-1<=u<=v<=t<=14/25,Gram>=0}.','premises':['Original algebraic coefficient enclosures valid for intended model','Original local nonnegativity proofs valid on frozen source boxes','PSD, pair reduction and reduction to D valid'],'full_independent_thomson_proof':False};write_new(run/'aggregate.json',result);return result

def run_parallel(run,workers,limit,resume):
    started=time.monotonic();run=Path(run)
    if resume:
        manifest=json.loads((run/'manifest.json').read_text());nodes,counts,tree_sha=scan_tree(TREE);validate_manifest(manifest,nodes,counts,tree_sha)
    else:manifest=create_manifest(run,limit)
    pending=[c for c in manifest['chunks'] if not (run/(c['id']+'.json')).exists()];print(json.dumps({'stage':'WORKERS_START','workers':workers,'pending_chunks':len(pending),'run':str(run),'pid':os.getpid()}),flush=True)
    with ProcessPoolExecutor(max_workers=workers,initializer=initialize_worker,initargs=(manifest,str(run))) as pool:
        futures=[pool.submit(verify_chunk,c) for c in pending]
        for future in as_completed(futures):
            r=future.result();print(json.dumps({'stage':'CHUNK_COMPLETE','id':r['id'],'path':r['path'],'nodes':r['nodes'],'seconds':r['elapsed_seconds'],'worker_pid':r['worker_pid']}),flush=True)
    result=aggregate(run,time.monotonic()-started);print(json.dumps(result),flush=True);return result

def main():
    p=argparse.ArgumentParser();p.add_argument('--run-dir',required=True);p.add_argument('--workers',type=int,default=4);p.add_argument('--chunk-nodes',type=int,default=4000);p.add_argument('--resume',action='store_true');p.add_argument('--aggregate-only',action='store_true');p.add_argument('--prepare-only',action='store_true');a=p.parse_args();C.need(1<=a.workers<=8,'workers out of range')
    if a.aggregate_only:print(json.dumps(aggregate(a.run_dir)),flush=True)
    elif a.prepare_only:create_manifest(a.run_dir,a.chunk_nodes)
    else:run_parallel(a.run_dir,a.workers,a.chunk_nodes,a.resume)
if __name__=='__main__':main()
