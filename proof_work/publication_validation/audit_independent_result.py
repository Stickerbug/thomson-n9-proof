"""Bind finished full-check report to the exported physical artifacts and test reports."""
from pathlib import Path
from hashlib import sha256
import json
D=Path(__file__).resolve().parent
EXPECTED_INPUT='3dd4ba639e78cabaa2c3a8182db3724545751ade50635e6d542067338b281066'
EXPECTED_TREE='4712313969755f9fb5126b7a95ced989db5e16710ccddffee5dad1cf91776c12'
EXPECTED_COUNTS={'boundary_multiplier':10518,'gram_negative':26797,'local_region':78,'ordered_disjoint':3278,'positive':27392}
def main():
    report=json.loads((D/'independent_full_result.json').read_text())
    tests=[json.loads((D/name).read_text()) for name in ('independent_selftests.json','independent_supplemental_tests.json')]
    checks={'full_checker_verified':report['status']=='VERIFIED_CONDITIONAL_COVERAGE','conditional_flag':report['conditional_only'] is True,'all_nodes':report['nodes']==136125,'all_splits':report['splits']==68062,'all_leaves':report['leaves']==68063,'all_leaf_reasons':report['leaf_counts']==EXPECTED_COUNTS,'input_binding':report['input_sha256']==EXPECTED_INPUT==sha256((D/'sharp_root_inputs.json').read_bytes()).hexdigest(),'tree_binding':report['tree_sha256']==EXPECTED_TREE==sha256((D/'sharp_root_tree.jsonl').read_bytes()).hexdigest(),'checker_binding':report['checker_sha256']==sha256((D/'checker_exact.py').read_bytes()).hexdigest(),'selftests':all(t['status']=='PASS' for t in tests),'test_count':sum(t['count'] for t in tests)==24}
    result={'status':'PASS' if all(checks.values()) else 'FAIL','checks':checks,'independent_full_report':report,'test_groups':24,'full_independent_thomson_proof':False,'scope':'Complete exact coverage and every leaf reason verified on the exported root box, conditional on the intended-model enclosure, local nonnegativity, PSD, pair reduction and root-domain reduction premises.','unverified_local_leaf_count':78,'local_nonnegativity_independently_proved':False,'psd_independently_proved':False}
    out=D/'independent_validation_summary.json'
    with out.open('x') as f:json.dump(result,f,indent=2);f.write(chr(10))
    print(json.dumps(result));return 0 if all(checks.values()) else 1
if __name__=='__main__':raise SystemExit(main())
