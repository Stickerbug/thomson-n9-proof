"""Reproduce toy valid/invalid full transport runs in owned temporary directories."""
from pathlib import Path
import argparse,tempfile,json,subprocess,sys,hashlib,time
D=Path(__file__).resolve().parent
NAMES=('checker_exact.py','sharded_checker.py','run_sharded_subprocess.py','subprocess_shard_worker.py')
def h(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def run_test(output):
    start=time.monotonic()
    with tempfile.TemporaryDirectory(prefix='.transport-reproduction-',dir=D) as td:
        root=Path(td).resolve();assert root.parent==D and root.name.startswith('.transport-reproduction-');T=root/'proof_work'/'publication_validation';T.mkdir(parents=True)
        for name in NAMES:
            with (T/name).open('xb') as f:f.write((D/name).read_bytes())
        inp={'bits':96,'delta':'0','F_mid_sym':[[[0,0,0],'-100']],'epsF':'0','c_interval':['0','0'],'local_regions':[],'boundary_multipliers':[]}
        co=T.parent/'d10_relative_normal_exact2026_coefficients.json';lo=T.parent/'d10_relative_normal_exact2026_locals.json';co.write_text('{}');lo.write_text('{}')
        rows=[{'path':'','box':[['-1','14/25']]*3,'levels':[0,0,0],'indices':[0,0,0],'type':'split','axis':0}]
        for side,b in [(0,['-1','-11/50']),(1,['-11/50','14/25'])]:rows.append({'path':str(side),'box':[b,['-1','14/25'],['-1','14/25']],'levels':[1,0,0],'indices':[side,0,0],'type':'leaf','kind':'positive'})
        (T/'sharp_root_tree.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
        def execute(value,runname):
            inp['F_mid_sym'][0][1]=str(value);(T/'sharp_root_inputs.json').write_text(json.dumps(inp));model={'status':'PASS_EXPORTED_MODEL_INPUT_BINDING','checks':{'toy_known_constant':True},'root_input_sha256':h(T/'sharp_root_inputs.json'),'source_hashes':{'co':h(co),'locals':h(lo)}};(T/'independent_model_input_binding.json').write_text(json.dumps(model));run=T/runname;proc=subprocess.run([sys.executable,'-u',str(T/'run_sharded_subprocess.py'),'--run-dir',str(run),'--workers','2','--chunk-nodes','1'],capture_output=True,text=True);return proc,run
        good,run=execute(-100,'good');assert good.returncode==0,(good.stdout,good.stderr);r=json.loads((run/'aggregate.json').read_text());assert (r['nodes'],r['chunks'],r['leaves'])==(3,2,2) and r['status']=='VERIFIED_CONDITIONAL_COVERAGE_SHARDED'
        bad,run=execute(100,'bad');assert bad.returncode!=0 and not (run/'aggregate.json').exists();errors=''.join((run/('subprocess-execution-v1-worker-'+str(i)+'.stderr.log')).read_text() for i in range(2));assert 'chunk invalid leaf positive' in errors,(bad.stdout,bad.stderr,errors)
        result={'status':'PASS','groups':2,'tests':['two persistent subprocesses verify complete valid toy tree and aggregate','known false positive leaf rejects in worker, propagates failure and prevents aggregate PASS'],'seconds':time.monotonic()-start,'transport_sources':{n:h(D/n) for n in NAMES},'test_source_sha256':h(__file__)}
        with Path(output).open('x') as f:json.dump(result,f,indent=2)
        print(json.dumps(result),flush=True);return result
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',default=str(D/'independent_subprocess_transport_selftests.json'));a=p.parse_args();run_test(a.output)
