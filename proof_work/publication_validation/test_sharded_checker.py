"""Deterministic exact differential and adversarial sharding tests."""
from pathlib import Path
from fractions import Fraction as Q
from collections import Counter
import copy,json,tempfile
import checker_exact as C
import sharded_checker as S
D=Path(__file__).resolve().parent
passed=[]
def reject(name,fn):
    try:fn()
    except (C.Invalid,KeyError,TypeError,ValueError,FileNotFoundError):passed.append(name);return
    raise AssertionError('negative fixture accepted: '+name)
def test():
    for levels,indices in [((0,0,0),(0,0,0)),((4,5,6),(7,15,31)),((8,7,9),(237,101,407))]:
        box=tuple((Q(-1)+Q(39*i,25*(1<<l)),Q(-1)+Q(39*(i+1),25*(1<<l))) for l,i in zip(levels,indices))
        for n in (2,10):
            nums,den=S.gram_numbers(levels,indices,n);exact=C.bern(C.GRAM,box,(n,n,n));assert tuple(Q(v,den) for v in nums)==exact
            if n==10:
                for lam in (Q(0),Q(3,7),Q(123456789,97)):
                    assert S.gram_correction(levels,indices,lam,1<<96)==tuple(C.ce(v*lam*(1<<96)) for v in exact)
    passed.append('integer_Gram_and_ceil_equal_exact_Fraction_at_three_geometries')
    for paths in [[''],['0','1'],['00','01','1'],['0','10','110','111']]:S.check_frontier(paths)
    passed.append('valid_complete_variable_depth_frontiers')
    for name,paths in [('frontier_missing_domain',['0']),('frontier_empty',[]),('frontier_duplicate',['0','0','1']),('frontier_overlap_ancestor',['','0']),('frontier_illegal_path',['2'])]:reject(name,lambda paths=paths:S.check_frontier(paths))
    with tempfile.TemporaryDirectory(prefix='independent-shard-tests-') as td:
        td=Path(td);tree=td/'toy.jsonl';rows=[]
        def row(path,box,lv,ix,typ,**extra):return dict(path=path,box=[[str(l),str(r)] for l,r in box],levels=list(lv),indices=list(ix),type=typ,**extra)
        rows.append(row('',C.ROOT,(0,0,0),(0,0,0),'split',axis=0))
        for side in (0,1):
            box,lv,ix=S.child_geometry(C.ROOT,(0,0,0),(0,0,0),0,side);rows.append(row(str(side),box,lv,ix,'leaf',kind='positive'))
        tree.write_text(''.join(json.dumps(r)+chr(10) for r in rows));nodes,counts,th=S.scan_tree(tree);chunks=S.choose_chunks(nodes,1);assert len(chunks)==2 and all(c['size']==1 for c in chunks);passed.append('subtree_spans_and_early_singletons')
        for name,badrows in [('structure_missing_child',rows[:-1]),('structure_extra_child',rows+[rows[-1]]),('structure_wrong_geometry',copy.deepcopy(rows)),('structure_illegal_terminal',copy.deepcopy(rows))]:
            if name=='structure_wrong_geometry':badrows[1]['indices'][0]=7
            if name=='structure_illegal_terminal':badrows[-1]['type']='stopped'
            bad=td/(name+'.jsonl');bad.write_text(''.join(json.dumps(r)+chr(10) for r in badrows));reject(name,lambda bad=bad:S.scan_tree(bad))
        binding={'tree':th};man={'schema':'test','bindings':binding,'node_count':3,'leaf_counts':counts,'chunk_limit':1,'chunks':chunks};man['manifest_sha256']=S.digest(man);oldbindings=S.source_bindings;oldtree=S.TREE;S.source_bindings=lambda:binding;S.TREE=tree
        try:
            S.validate_manifest(man,nodes,counts,th);run=td/'run';run.mkdir();S.write_new(run/'manifest.json',man);S.RUN=run;S.MANIFEST=man;S.MATH=S.FastMath({'bits':96,'delta':'0','F_mid_sym':[[[0,0,0],'-100']],'epsF':'0','c_interval':['0','0'],'local_regions':[],'boundary_multipliers':[]})
            reports=[S.verify_chunk(c) for c in chunks];assert sum(r['nodes'] for r in reports)==2 and sum(r['leaves'] for r in reports)==2;assert S.aggregate(run)['status']=='VERIFIED_CONDITIONAL_COVERAGE_SHARDED';passed.append('complete_shards_from_global_root_then_global_aggregate')
            for name,modify in [('wrong_chunk_status',lambda r:r.update(status='FAILED')),('wrong_chunk_path',lambda r:r.update(path='11')),('wrong_chunk_manifest_hash',lambda r:r.update(manifest_sha256='0'*64)),('wrong_chunk_bytes_hash',lambda r:r.update(chunk_tree_sha256='0'*64)),('wrong_chunk_counts',lambda r:r.update(nodes=7)),('wrong_chunk_binding',lambda r:r.update(bindings={'tree':'0'*64}))]:
                p=run/'chunk-00000.json';original=p.read_text();r=json.loads(original);modify(r);p.write_text(json.dumps(r));reject(name,lambda:S.aggregate(run));p.write_text(original)
            p=run/'manifest.json';original=p.read_text();bad=copy.deepcopy(man);bad['chunks']=bad['chunks'][:-1];bad.pop('manifest_sha256');bad['manifest_sha256']=S.digest(bad);p.write_text(json.dumps(bad));reject('rehash_cannot_hide_frontier_gap',lambda:S.aggregate(run));p.write_text(original)
            for name,key,value in [('wrong_frontier_byte_span','end',999),('wrong_frontier_ancestor_axis','ancestor_axes',[2]),('wrong_frontier_geometry','indices',[99,0,0])]:
                bad=copy.deepcopy(man);bad['chunks'][0][key]=value;bad.pop('manifest_sha256');bad['manifest_sha256']=S.digest(bad);reject(name,lambda bad=bad:S.validate_manifest(bad,nodes,counts,th))
            passed.append('bound_frontier_and_report_mutations_checked')
        finally:S.source_bindings=oldbindings;S.TREE=oldtree
    result={'status':'PASS','sharded_checker_sha256':S.filehash(S.__file__),'exact_checker_sha256':S.filehash(C.__file__),'groups':len(passed),'tests':passed,'scope':'Additional exact Gram and recoverable-sharding tests; no local nonnegativity or PSD proof.'};S.write_new(D/'independent_sharded_selftests_v2.json',result);print(json.dumps(result),flush=True)
if __name__=='__main__':test()
