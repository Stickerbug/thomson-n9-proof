#!/usr/bin/env python3
"""Reproduce explicitly registered proof modules without renaming imports.

Templates are source provenance, never mathematical premises. The Lean kernel
checks every certificate. Original module names allow exact existing compiler
artifacts to be adopted before a complete fresh replay.
"""
from pathlib import Path
from copy import deepcopy
import argparse
import hashlib
import json
import re

P = Path(__file__).resolve().parent
MANIFEST = P / 'packed_coverage_manifest.json'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(manifest):
    if manifest.get('schema') != 'packed_coverage_sources_v1':
        raise ValueError('packed coverage schema mismatch')
    files = manifest.get('files', {})
    if not files or len(files) != manifest.get('module_count'):
        raise ValueError('packed coverage module count mismatch')
    for module, item in files.items():
        if not re.fullmatch(r'[A-Za-z_][\w]*(?:\.[A-Za-z_][\w]*)*', module):
            raise ValueError('invalid registered module name')
        if module.split('.')[0] in {'ThomsonNine', 'Mathlib', 'Lean', 'Std', 'Init', 'Lake'}:
            raise ValueError('registered module would shadow a dependency')
        relative = module.replace('.', '/')
        if item.get('formal') != 'formal/' + relative + '.lean':
            raise ValueError('registered source path mismatch')
        if item.get('template') != 'packed_inputs/' + relative + '.lean.in':
            raise ValueError('registered template path mismatch')
        if digest(P / item['template']) != item.get('sha256'):
            raise ValueError('registered template hash mismatch: ' + module)
    if not set(manifest['roots']) <= set(files):
        raise ValueError('unregistered coverage root')
    for relative, expected in manifest['input_sha256'].items():
        path = (P / relative).resolve()
        if not path.is_relative_to(P.parent.resolve()) or digest(path) != expected:
            raise ValueError('coverage input hash mismatch: ' + relative)
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    manifest = json.loads(MANIFEST.read_text())
    files = validate(manifest)
    if args.self_test:
        for case in ['count', 'path', 'name', 'template_hash', 'input_hash']:
            bad = deepcopy(manifest)
            first = next(iter(files))
            if case == 'count':
                bad['module_count'] += 1
            elif case == 'path':
                bad['files'][first]['formal'] = 'formal/../escape.lean'
            elif case == 'name':
                bad['files']['Mathlib.Shadow'] = bad['files'].pop(first)
            elif case == 'template_hash':
                bad['files'][first]['sha256'] = '0' * 64
            else:
                bad['input_sha256'][next(iter(bad['input_sha256']))] = '0' * 64
            try:
                validate(bad)
            except ValueError:
                continue
            raise AssertionError('invalid coverage manifest accepted: ' + case)
        print('PACKED_COVERAGE_MANIFEST_NEGATIVE_TESTS_PASS 5')
    for module, item in files.items():
        source = P / item['formal']
        payload = (P / item['template']).read_bytes()
        if args.check:
            if not source.is_file() or source.read_bytes() != payload:
                raise SystemExit('packed coverage source mismatch: ' + module)
        else:
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_bytes(payload)
    print('PACKED_COVERAGE_SOURCES_PASS', len(files), 'modules')


if __name__ == '__main__':
    main()
