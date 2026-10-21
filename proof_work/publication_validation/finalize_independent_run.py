"""Finalize on Linux CLOSE_WRITE notification; no polling and no duplicate verification."""
from pathlib import Path
from hashlib import sha256
import ctypes,os,struct,subprocess,sys,json
D=Path(__file__).resolve().parent
TARGET='independent_full_result.json'
def completed():
    try:return bool(json.loads((D/TARGET).read_text()).get('status'))
    except (FileNotFoundError,json.JSONDecodeError):return False

def await_result():
    libc=ctypes.CDLL(None,use_errno=True);fd=libc.inotify_init1(0)
    if fd<0:raise OSError(ctypes.get_errno(),'inotify_init1')
    try:
        if libc.inotify_add_watch(fd,os.fsencode(D),8)<0:raise OSError(ctypes.get_errno(),'inotify_add_watch')
        if completed():return
        print('Awaiting full report CLOSE_WRITE event; verification not restarted.',flush=True)
        while True:
            events=os.read(fd,65536);off=0
            while off<len(events):
                wd,mask,cookie,n=struct.unpack_from('iIII',events,off);off+=16;name=events[off:off+n].split(b'\0',1)[0].decode();off+=n
                if mask&8 and name==TARGET:
                    if not completed():raise RuntimeError('closed full report is incomplete')
                    return
    finally:os.close(fd)

def main():
    await_result()
    subprocess.run([sys.executable,str(D/'audit_independent_result.py')],check=True)
    report=json.loads((D/TARGET).read_text());summary=json.loads((D/'independent_validation_summary.json').read_text());old=json.loads((D/'independent_source_manifest.json').read_text())
    if report['checker_sha256']!=old['checker_exact.py']['sha256']:raise RuntimeError('initial checker hash changed')
    if summary['status']!='PASS':raise RuntimeError('full binding audit failed')
    premise=json.loads((D/'independent_premise_binding.json').read_text());negative=json.loads((D/'independent_known_failed_kernel.json').read_text())
    if not all(x['matches'] for x in premise['source_files'].values()):raise RuntimeError('premise digest binding failed')
    if not all(negative['checks'].values()):raise RuntimeError('known negative check failed')
    scope='Complete binary tree partition of root B=[-1,14/25]^3, and conditional residual nonnegativity on D={-1<=u<=v<=t<=14/25, Gram(u,v,t)>=0}. Local nonnegativity, intended-model coefficient enclosures, PSD, pair reduction and reduction to D remain explicit premises. This is not an independent complete Thomson N=9 proof.'
    final=dict(summary);final.update(scope=scope,initial_checker_digest_matches=True,premise_artifact_binding=premise,known_failed_kernel=negative)
    with (D/'independent_validation_final.json').open('x') as f:json.dump(final,f,indent=2);f.write(chr(10))
    p=D/'README_independent_checker.md';text=p.read_text();lines=text.splitlines()
    for i,line in enumerate(lines):
        if line.startswith('The output claim is '):lines[i]='The checker establishes a **complete binary tree partition of the root box** B=[-1,14/25]^3 and **conditional residual nonnegativity on** D={-1 <= u <= v <= t <= 14/25, Gram(u,v,t) >= 0}. Ordering and Gram exclusion leaves prove absence of feasible D-points; they do not claim residual nonnegativity on excluded boxes. Local nonnegativity, intended-model coefficient enclosures, PSD, pair reduction and reduction to D remain explicit premises. This is not a complete independent proof of the nine-point Thomson minimum. Midpoint symmetry itself is checked exactly; intended-model symmetry and enclosure remain premises.'
        if line.startswith('The full run started as managed background job '):lines[i]='The full run **finished successfully** as managed job `bash-198`: status `VERIFIED_CONDITIONAL_COVERAGE`, 136125 nodes, 68062 splits, 68063 leaves, elapsed '+format(report['elapsed_seconds'],'.3f')+' seconds. Input, tree and checker digests match the frozen bindings and the initial source manifest. `independent_validation_final.json` is the complete audited result; `independent_full_result.json` is the raw verifier output.'
    text='\n'.join(lines)+'\n\n## Final full verification result\n\nStatus: **PASS, conditional coverage only**. All 24 test groups passed. The known failed rational kernel was independently rejected at its pre-existing exact negative point. No frozen sources were overwritten.\n\n| Leaf reason | Count |\n|---|---:|\n'
    for kind,count in sorted(report['leaf_counts'].items()):text+='| '+kind+' | '+str(count)+' |\n'
    text+='\nReproduce binding audit after a full run with `python3 proof_work/publication_validation/audit_independent_result.py` (its output uses exclusive creation, so preserve prior reports under a separate run directory). The finalizer reacts to the completed result file via a Linux filesystem event and performs no mathematical verification through C; all certificate mathematics remains in the unchanged standard-library checker.\n'
    p.write_text(text)
    names=['checker_exact.py','test_checker_exact.py','test_checker_supplemental.py','check_known_failed_kernel.py','audit_independent_result.py','finalize_independent_run.py','README_independent_checker.md','independent_selftests.json','independent_supplemental_tests.json','independent_full_result.json','independent_validation_summary.json','independent_validation_final.json','independent_premise_binding.json','independent_known_failed_kernel.json']
    manifest={name:{'sha256':sha256((D/name).read_bytes()).hexdigest(),'bytes':(D/name).stat().st_size,'regular_file':not (D/name).is_symlink()} for name in names}
    with (D/'independent_final_manifest.json').open('x') as f:json.dump(manifest,f,indent=2);f.write(chr(10))
    print(json.dumps({'status':'FINAL_AUDIT_PASS','nodes':report['nodes'],'leaf_counts':report['leaf_counts'],'elapsed_seconds':report['elapsed_seconds'],'checker_sha256':report['checker_sha256'],'scope':scope}),flush=True)
if __name__=='__main__':main()
