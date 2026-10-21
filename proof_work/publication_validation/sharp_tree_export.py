"""Exclusive single-root full-tree exporter. Frozen sources are never modified."""
from pathlib import Path
from fractions import Fraction
from hashlib import sha256
from collections import Counter
from time import monotonic
import importlib.util,json,sys,traceback
OUT=Path(__file__).resolve().parent
SOURCE=OUT.parent
sys.path.insert(0,str(SOURCE))
def dump_new(name,obj):
    with (OUT/name).open('x') as f:json.dump(obj,f,sort_keys=True,separators=(',',':'));f.write('\n')
def digest(p):return sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text())
def instrument():
    text=(SOURCE/'analytic10_sharp2026_engine.py').read_text()
    for name in ['analytic10_2026_sum.so','analytic10_2026_sum.c']:
        text=text.replace("Path(__file__).with_name('"+name+"')", "(Path(__file__).parent.parent / '"+name+"')")
    text=text.replace("    stack=[(b,g,active,ROOT_BOX", "    _export_root(rootinputs)\n    stack=[(b,g,active,ROOT_BOX")
    text=text.replace("        b,g,act,box,levels,indices,path=stack.pop();visited", "        current=stack[-1]\n        b,g,act,box,levels,indices,path=stack.pop();visited")
    text=text.replace("            counts[kind]+=1;transcript.update(json.dumps([path,kind,ident,witness]).encode());continue", "            _export_node('leaf',path,box,levels,indices,kind=kind,ident=ident,witness=None if witness is None else str(witness))\n            current=None\n            counts[kind]+=1;transcript.update(json.dumps([path,kind,ident,witness]).encode());continue")
    text=text.replace("        splits+=1", "        _export_node('split',path,box,levels,indices,axis=axis)\n        current=None\n        splits+=1")
    a=text.index('    while stack and visited<budget');z=text.index('    terminals=sum(counts.values())',a)
    text=text[:a]+"    current=None\n    try:\n"+''.join('    '+line if line.strip() else line for line in text[a:z].splitlines(True))+"    finally:\n        _export_pending(stack,current,boundary)\n"+text[z:]
    with (OUT/'sharp_tree_engine_instrumented.py').open('x') as f:f.write(text)
def geometry_check(expected=None):
    start=monotonic();nodes={}
    for line in (OUT/'sharp_root_tree.jsonl').open():
        n=json.loads(line);p=n['path'];assert p not in nodes,('duplicate',p);assert set(p)<=set('01')
        assert len(n['box'])==len(n['levels'])==len(n['indices'])==3
        box=tuple(tuple(map(Fraction,x))for x in n['box'])
        for i in range(3):
            lv=n['levels'][i];ix=n['indices'][i]
            assert type(lv)is int and lv>=0 and type(ix)is int and 0<=ix<2**lv
            lo=Fraction(-1)+Fraction(39,25)*Fraction(ix,2**lv);hi=lo+Fraction(39,25*2**lv)
            assert box[i]==(lo,hi),(p,i,'box differs from exact dyadic indices')
        assert sum(n['levels'])==len(p);nodes[p]=n
    assert '' in nodes;assert nodes['']['levels']==nodes['']['indices']==[0,0,0]
    seen=set();stack=[''];types=Counter();kinds=Counter();transcript=sha256()
    while stack:
        p=stack.pop();assert p not in seen;seen.add(p);n=nodes[p];types[n['type']]+=1
        if n['type']=='split':
            ax=n['axis'];assert type(ax)is int and ax in (0,1,2);assert ax==min(range(3),key=lambda i:n['levels'][i])
            for side in (0,1):
                child=nodes[p+str(side)];lv=n['levels'].copy();ix=n['indices'].copy();lv[ax]+=1;ix[ax]=2*ix[ax]+side
                assert child['levels']==lv and child['indices']==ix
                pb=[list(map(Fraction,b))for b in n['box']];mid=sum(pb[ax])/2;pb[ax][1-side]=mid
                assert [list(map(Fraction,b))for b in child['box']]==pb
            stack.extend([p+'1',p+'0'])
        elif n['type']=='leaf':
            assert n['kind'] in {'positive','gram_negative','ordered_disjoint','local_region','boundary_multiplier'}
            assert 'ident' in n and 'witness' in n
            if n['kind'] in {'positive','boundary_multiplier'}:assert int(n['witness'])>=0
            kinds[n['kind']]+=1
            transcript.update(json.dumps([p,n['kind'],n['ident'],None if n['witness'] is None else int(n['witness'])]).encode())
        else:assert n['type']=='pending'
    assert seen==set(nodes),'unreachable nodes';assert types['leaf']+types['pending']==types['split']+1
    if expected:
        assert types['split']==expected['split_nodes'];assert dict(kinds)==expected['counts'];assert types['pending']==expected['pending_count']
        assert types['leaf']+types['split']==expected['visited_nodes'];assert transcript.hexdigest()==expected['transcript_sha256']
    return {'status':'PASS','scope':'exact full-tree geometry/connectivity/count/hash selfcheck; not independent witness validation','nodes':len(nodes),'node_types':dict(types),'leaf_kinds':dict(kinds),'pending_count':types['pending'],'all_nodes_reached_from_root':True,'every_split_exact_midpoint':True,'every_box_matches_levels_indices':True,'leaf_transcript_sha256':transcript.hexdigest(),'tree_sha256':digest(OUT/'sharp_root_tree.jsonl'),'tree_bytes':(OUT/'sharp_root_tree.jsonl').stat().st_size,'elapsed_seconds':monotonic()-start}
def main():
    start=monotonic();replay_path=SOURCE/'relative_normal2026_replay2/root_replay.json';co_path=SOURCE/'d10_relative_normal_exact2026_coefficients.json';local_path=SOURCE/'d10_relative_normal_exact2026_locals.json';manifest_path=SOURCE/'analytic10_sharp2026_run1_inputs.json'
    manifest=load(manifest_path);replay=load(replay_path);co=load(co_path)
    protected=[Path(p)for p in manifest['frozen_sha256']]+[replay_path,manifest_path];before={str(p):digest(p)for p in protected}
    for p,h in manifest['frozen_sha256'].items():assert before[p]==h,('frozen hash mismatch',p)
    bindings={'source_file_sha256':before,'original_root_inputs_sha256':replay['root_inputs_sha256'],'original_replay_sha256':before[str(replay_path)],'coefficient_sha256':before[str(co_path)],'locals_sha256':before[str(local_path)],'schema':'sharp-root-tree-v1','root_box':[['-1','14/25']]*3,'budget':200000,'seconds':180,'root_invocations':1,'conditional_only':True}
    dump_new('sharp_tree_metadata.json',bindings);instrument()
    spec=importlib.util.spec_from_file_location('sharp_export_instrument',OUT/'sharp_tree_engine_instrumented.py');eng=importlib.util.module_from_spec(spec);spec.loader.exec_module(eng)
    def interval(x):
        den=1<<x['denominator_power_of_two'];return (Fraction(int(x['lo_numerator']),den),Fraction(int(x['hi_numerator']),den))
    F={tuple(p):interval(v)for p,v in co['F_coefficients']};c=interval(co['c'])
    _,local,boundary=eng._normalize(F,replay['rootinputs']['local_regions'],replay['rootinputs']['boundary_multipliers'])
    assert eng._serial(local)==replay['rootinputs']['local_regions'];assert eng._serial(boundary)==replay['rootinputs']['boundary_multipliers']
    def root_hook(root):
        assert root==replay['rootinputs'],'reconstructed root differs from frozen rootinputs';assert eng._hash(root)==replay['root_inputs_sha256'];dump_new('sharp_root_inputs.json',root)
    result=None;error=None
    with (OUT/'sharp_root_tree.jsonl').open('x',buffering=1024*1024) as tree:
        def node_hook(typ,path,box,levels,indices,**kwargs):
            n={'type':typ,'path':path,'box':eng._serial(box),'levels':list(levels),'indices':list(indices),**kwargs};tree.write(json.dumps(n,separators=(',',':'))+'\n')
        def pending_hook(stack,current,boundary):
            frontier=list(reversed(stack))
            if current is not None:frontier.insert(0,current)
            for _,_,act,box,lv,ix,path in frontier:node_hook('pending',path,box,lv,ix,active_boundary_ids=[boundary[i]['id']for i in act])
            tree.flush()
        eng._export_root=root_hook;eng._export_node=node_hook;eng._export_pending=pending_hook
        try:result=eng.check_analytic(F,c,replay['rootinputs']['local_regions'],replay['rootinputs']['boundary_multipliers'],budget=200000,seconds=180,delta=Fraction(0),bits=96)
        except BaseException:
            error=traceback.format_exc();dump_new('sharp_tree_failure.json',{'error':error,'elapsed_seconds':monotonic()-start,'root_invocations':1})
    after={str(p):digest(p)for p in protected};unchanged=before==after
    if result:
        result['export_bindings']=bindings;result['frozen_sources_unchanged']=unchanged;result['tree_sha256']=digest(OUT/'sharp_root_tree.jsonl');result['instrumented_engine_sha256']=digest(OUT/'sharp_tree_engine_instrumented.py');dump_new('sharp_tree_result.json',result)
    try:
        check=geometry_check(result);check['frozen_sources_unchanged']=unchanged;check['root_inputs_sha256']=digest(OUT/'sharp_root_inputs.json');check['root_inputs_canonical_sha256']=replay['root_inputs_sha256'];check['total_driver_seconds']=monotonic()-start;dump_new('sharp_tree_selfcheck.json',check)
    except BaseException:dump_new('sharp_tree_selfcheck_failure.json',{'error':traceback.format_exc(),'frozen_sources_unchanged':unchanged});raise
    assert unchanged;print(json.dumps({'status':result['status'] if result else 'FAILED','error':error,'selfcheck':check}),flush=True)
    return 0 if result and result['pending_count']==0 else 1
if __name__=='__main__':sys.exit(main())
