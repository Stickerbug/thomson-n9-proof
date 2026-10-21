from pathlib import Path
import concurrent.futures as cf, urllib.request as U, urllib.error, json, hashlib, tarfile, time, os
BASE=Path(__file__).resolve().parent/'formal'
UP=json.loads((BASE/'.lake/packages/mathlib/lake-manifest.json').read_text())
OUT=BASE/'.lake/pinned_sources'
OUT.mkdir(exist_ok=True)
def get_json(url):
    for attempt in range(3):
        try:
            with U.urlopen(U.Request(url,headers={'User-Agent':'ThomsonNine-validation'}),timeout=30) as r:return json.load(r)
        except urllib.error.HTTPError as e:
            if e.code!=403:raise
            print('GIT_TREE_API_RATE_LIMIT',url,flush=True)
            return None
        except (urllib.error.URLError,TimeoutError) as e:
            print('GIT_TREE_API_RETRY',attempt,type(e).__name__,flush=True)
    print('GIT_TREE_API_UNAVAILABLE',url,flush=True)
    return None
def obtain(pkg):
    name=pkg['name'];rev=pkg['rev'];repo=pkg['url'].split('github.com/')[1].removesuffix('.git')
    completed=OUT/(name+'_verified.json')
    if completed.exists():
        result=json.loads(completed.read_text())
        if result['commit']!=rev:raise RuntimeError('wrong preserved commit')
        print('PRESERVED_VERIFIED',name,flush=True)
        return result
    root=OUT/name;archive=OUT/(name+'.tar.gz');root.mkdir(exist_ok=True)
    if any(root.iterdir()) or archive.exists():raise RuntimeError('incomplete nonempty target requires review '+name)
    tree=get_json(f'https://api.github.com/repos/{repo}/git/trees/{rev}?recursive=1')
    if tree and tree.get('truncated'):raise RuntimeError('truncated tree '+name)
    entries={x['path']:x for x in tree['tree'] if x['type']=='blob'} if tree else None
    url=f'https://codeload.github.com/{repo}/tar.gz/{rev}'
    with U.urlopen(url,timeout=60) as r,archive.open('xb') as f:
        while True:
            block=r.read(1024*1024)
            if not block:break
            f.write(block)
    seen=set();observed={}
    with tarfile.open(archive,'r:gz') as tf:
        members=tf.getmembers()
        prefix=members[0].name.split('/')[0]
        for m in members:
            parts=Path(m.name).parts
            if parts[0]!=prefix:raise RuntimeError('unexpected archive root')
            rel=Path(*parts[1:])
            if rel==Path('.'):continue
            dest=root/rel
            if not dest.resolve().is_relative_to(root.resolve()):raise RuntimeError('unsafe member')
            if m.isdir():dest.mkdir(parents=True,exist_ok=True);continue
            key=rel.as_posix()
            if key in seen:raise RuntimeError('duplicate archive member '+key)
            if entries is not None and key not in entries:raise RuntimeError('unlisted member '+key)
            if m.issym():
                data=m.linkname.encode()
                if not (dest.parent/m.linkname).resolve().is_relative_to(root.resolve()):raise RuntimeError('unsafe symlink')
                mode='120000'
            elif m.isfile():
                data=tf.extractfile(m).read();mode='100755'if m.mode&0o111 else'100644'
            else:raise RuntimeError('unsupported member type')
            digest=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
            if entries is not None and (digest!=entries[key]['sha'] or mode!=entries[key]['mode']):raise RuntimeError('blob/mode mismatch '+key)
            observed[key]={'sha':digest,'mode':mode}
            dest.parent.mkdir(parents=True,exist_ok=True)
            if m.issym():os.symlink(m.linkname,dest)
            else:
                with dest.open('xb')as f:f.write(data)
                dest.chmod(0o755 if mode=='100755'else 0o644)
            seen.add(key)
    if entries is not None and seen!=set(entries):raise RuntimeError('missing tracked files '+name+str(set(entries)-seen))
    result={'name':name,'repo':repo,'commit':rev,'git_tree':tree['sha'] if tree else None,'verified_blobs':len(seen) if tree else None,'observed_blobs':observed,'archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'path':str(root.relative_to(BASE)),'source_url':url,'verification':('Every archive blob and mode matches GitHub git-tree API for the pinned commit; API/TLS is trusted for commit-to-tree binding.' if tree else 'Pinned GitHub codeload URL over TLS and recorded archive SHA256. Git-tree API quota exhausted; no independent blob comparison for this dependency.')}
    with (OUT/(name+'_verified.json')).open('x')as f:json.dump(result,f,indent=2)
    print('ARCHIVE_READY',name,len(seen),'git_blobs_verified',bool(tree),flush=True)
    return result
start=time.monotonic()
with cf.ThreadPoolExecutor(max_workers=8)as pool:results=list(pool.map(obtain,UP['packages']))
p=BASE/'lake-manifest.json';old=json.loads(p.read_text());by={r['name']:r for r in results}
with (BASE/'lake-manifest.original_git.json').open('x')as f:json.dump(old,f,indent=2)
for i,entry in enumerate(old['packages']):
    if entry['name']in by:
        x=by[entry['name']];old['packages'][i]={'type':'path','dir':x['path'],'scope':entry.get('scope',''),'name':entry['name'],'inherited':True,'configFile':entry['configFile'],'manifestFile':'lake-manifest.json'}
p.write_text(json.dumps(old,indent=2)+'\n')
with (BASE/'pinned_archives_ready.json').open('x')as f:json.dump({'status':'PINNED_ARCHIVES_READY_VERIFICATION_LEVELS_RECORDED','dependencies':results,'seconds':time.monotonic()-start},f,indent=2)
print('ALL_PINNED_ARCHIVES_READY',time.monotonic()-start,flush=True)
