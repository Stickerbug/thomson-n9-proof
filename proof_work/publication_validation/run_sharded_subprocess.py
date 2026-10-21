"""Event-driven standard-library process transport for the frozen mathematical checker."""
from pathlib import Path
from collections import deque
import argparse,json,time,os,sys,subprocess,selectors
import sharded_checker as S
D=Path(__file__).resolve().parent

def execute(run,workers,limit,resume,label):
    start=time.monotonic();run=Path(run).resolve()
    if resume:
        manifest=json.loads((run/'manifest.json').read_text());nodes,counts,tree_sha=S.scan_tree(S.TREE);S.validate_manifest(manifest,nodes,counts,tree_sha)
    else:manifest=S.create_manifest(run,limit)
    pending=deque(c for c in manifest['chunks'] if not (run/(c['id']+'.json')).exists());initial_pending=len(pending);procs={};sel=selectors.DefaultSelector();done=0
    S.C.need(bool(label) and all(c.isalnum() or c in '-_' for c in label),'invalid execution label')
    try:
        for i in range(workers):
            err=(run/(label+'-worker-'+str(i)+'.stderr.log')).open('x');proc=subprocess.Popen([sys.executable,'-u',str(D/'subprocess_shard_worker.py'),'--run-dir',str(run)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=err,text=True,bufsize=1);err.close();procs[proc.pid]={'process':proc,'current':None,'ready':False,'stopping':False};sel.register(proc.stdout,selectors.EVENT_READ,proc.pid)
        launch={'pid':os.getpid(),'started_epoch':time.time(),'workers':[p for p in procs],'pending_chunks':initial_pending,'manifest_sha256':manifest['manifest_sha256'],'transport_sources':{name:S.filehash(D/name) for name in ('run_sharded_subprocess.py','subprocess_shard_worker.py')},'mathematical_bindings':manifest['bindings'],'mechanism':'persistent subprocesses and selectors; no POSIX named semaphore','trust':'resume/aggregate trust complete local execution records; fresh run required for external review'};S.write_new(run/(label+'.json'),launch);print(json.dumps({'stage':'SUBPROCESS_WORKERS_START',**launch}),flush=True)
        while sel.get_map():
            events=sel.select(30)
            if not events:print(json.dumps({'stage':'HEARTBEAT','completed_new_chunks':done,'queued_chunks':len(pending),'active_workers':len(sel.get_map())}),flush=True)
            for key,mask in events:
                state=procs[key.data];proc=state['process'];line=proc.stdout.readline()
                if not line:
                    code=proc.wait();S.C.need(state['stopping'] and state['current'] is None and code==0,'worker exited unexpectedly pid '+str(proc.pid)+' code '+str(code));sel.unregister(proc.stdout);proc.stdout.close();continue
                message=json.loads(line)
                if message['stage']=='READY':
                    S.C.need(not state['ready'] and message['pid']==proc.pid and message['manifest_sha256']==manifest['manifest_sha256'],'worker readiness binding');state['ready']=True
                else:
                    S.C.need(message['stage']=='CHUNK_COMPLETE' and state['current']==message['id'] and message['worker_pid']==proc.pid,'worker completion identity');state['current']=None;done+=1;print(json.dumps(message),flush=True)
                if pending:
                    c=pending.popleft();state['current']=c['id'];proc.stdin.write(json.dumps({'chunk_id':c['id']})+'\n');proc.stdin.flush()
                else:state['stopping']=True;proc.stdin.write(json.dumps({'stop':True})+'\n');proc.stdin.flush();proc.stdin.close()
        S.C.need(done==initial_pending,'unreported new chunk completion');result=S.aggregate(run,time.monotonic()-start);print(json.dumps(result),flush=True);return result
    finally:
        sel.close()
        for state in procs.values():
            proc=state['process']
            if proc.poll() is None:proc.terminate()
        for state in procs.values():state['process'].wait()

def main():
    p=argparse.ArgumentParser();p.add_argument('--run-dir',required=True);p.add_argument('--workers',type=int,default=4);p.add_argument('--chunk-nodes',type=int,default=4000);p.add_argument('--resume',action='store_true');p.add_argument('--execution-label',default='subprocess-execution-v1');a=p.parse_args();S.C.need(1<=a.workers<=8,'workers out of range');execute(a.run_dir,a.workers,a.chunk_nodes,a.resume,a.execution_label)
if __name__=='__main__':main()
