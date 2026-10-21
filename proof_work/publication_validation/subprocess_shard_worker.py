"""Persistent mathematical subprocess worker, no multiprocessing shared semaphores."""
from pathlib import Path
import argparse,json,sys,os
import sharded_checker as S

def main():
    p=argparse.ArgumentParser();p.add_argument('--run-dir',required=True);a=p.parse_args();run=Path(a.run_dir).resolve();manifest=json.loads((run/'manifest.json').read_text());S.initialize_worker(manifest,run);chunks={c['id']:c for c in manifest['chunks']}
    print(json.dumps({'stage':'READY','pid':os.getpid(),'manifest_sha256':manifest['manifest_sha256']}),flush=True)
    for line in sys.stdin:
        command=json.loads(line)
        if command.get('stop') is True:return
        ident=command['chunk_id'];S.C.need(ident in chunks,'worker unknown chunk id');r=S.verify_chunk(chunks[ident]);print(json.dumps({'stage':'CHUNK_COMPLETE','id':r['id'],'path':r['path'],'nodes':r['nodes'],'seconds':r['elapsed_seconds'],'worker_pid':os.getpid()}),flush=True)
if __name__=='__main__':main()
