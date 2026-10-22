#!/usr/bin/env python3
"""Reproduce authored construction proof sources from bound source templates.

This exporter records source provenance and exact source reproducibility. Lean
checks the mathematics; neither the template hashes nor upstream JSON statuses
are proof premises.
"""
from pathlib import Path
from copy import deepcopy
import argparse,hashlib,json
P=Path(__file__).resolve().parent
PREFIX='ThomsonNine.Construction.'
DIMENSIONS={'N_meaningful':405,'contact_selected_rows':33,'contact_parameters':190,'A_entries':506,'F_coefficients':756,'R_coefficients':807,'contact_value_types':12,'moment_entries':506}
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def validate(m):
    if m.get('schema')!='actual_construction_sources_v1' or m.get('numeric_dimensions')!=DIMENSIONS:raise ValueError('construction schema/dimensions mismatch')
    files=m.get('files',{})
    if len(files)!=m.get('formal_module_count') or not files:raise ValueError('construction module count mismatch')
    for module,item in files.items():
        if not module.startswith(PREFIX) or any(not part.isidentifier()for part in module.split('.')):raise ValueError('invalid construction module')
        source='formal/'+module.replace('.','/')+'.lean'
        template='construction_inputs/'+module.removeprefix(PREFIX).replace('.','/')+'.lean.in'
        if item.get('formal')!=source or item.get('template')!=template:raise ValueError('construction path mismatch')
        if digest(P/template)!=item.get('sha256'):raise ValueError('construction template hash mismatch: '+module)
    for name,sha in m['input_sha256'].items():
        path=(P/name).resolve()
        if not path.is_relative_to(P.parent.resolve()) or digest(path)!=sha:raise ValueError('construction input hash mismatch: '+name)
    if not set(m['roots'])<=set(files):raise ValueError('missing construction root')
    return files

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');ap.add_argument('--self-test',action='store_true');args=ap.parse_args()
    m=json.loads((P/'actual_construction_manifest.json').read_text());files=validate(m)
    if args.self_test:
        for case in ['count','path','template_hash','input_hash']:
            bad=deepcopy(m);first=next(iter(files))
            if case=='count':bad['formal_module_count']+=1
            elif case=='path':bad['files'][first]['formal']='formal/../escape.lean'
            elif case=='template_hash':bad['files'][first]['sha256']='0'*64
            else:bad['input_sha256'][next(iter(m['input_sha256']))]='0'*64
            try:validate(bad)
            except ValueError:continue
            raise AssertionError('invalid construction manifest accepted: '+case)
        print('CONSTRUCTION_MANIFEST_NEGATIVE_TESTS_PASS 4')
    for module,item in files.items():
        source=P/item['formal'];payload=(P/item['template']).read_bytes()
        if args.check:
            if not source.is_file() or source.read_bytes()!=payload:raise SystemExit('construction source mismatch: '+module)
        else:
            source.parent.mkdir(parents=True,exist_ok=True);source.write_bytes(payload)
    print('ACTUAL_CONSTRUCTION_SOURCES_PASS',len(files),'modules')
if __name__=='__main__':main()
