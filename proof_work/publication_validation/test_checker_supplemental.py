"""Reproduce supplemental boundary, exact-input, and external-binding tests."""
from pathlib import Path
import copy,json,tempfile
import checker_exact as C
from test_checker_exact import fixture,node

def main():
    checks=[]
    with tempfile.TemporaryDirectory() as td:
        a=Path(td)/'input.json';b=Path(td)/'tree.jsonl'
        def run(inp,n):
            a.write_text(json.dumps(inp));b.write_text(json.dumps(n)+chr(10));return C.verify(a,b,progress=0)
        inp=fixture();inp['boundary_multipliers']=[dict(id='B',centerI=[['0','0']]*3,**{'lambda':'1'})];n=node();n['kind']='boundary_multiplier';n['ident']='B'
        assert run(inp,n)['leaf_counts']=={'boundary_multiplier':1};checks.append('valid boundary multiplier polynomial')
        bad=copy.deepcopy(inp);bad['c_interval']=['100','100']
        try:run(bad,n)
        except C.Invalid as e:assert 'invalid leaf' in str(e);checks.append('mathematically false boundary multiplier')
        else:raise AssertionError('false boundary accepted')
        for name,change,fragment in [('negative lambda',lambda z:z['boundary_multipliers'][0].update({'lambda':'-1'}),'negative lambda'),('asymmetric midpoint',lambda z:z.update(F_mid_sym=[[[1,0,0],'1']]),'not symmetric'),('float enclosure',lambda z:z.update(epsF=0.0),'exact rational')]:
            bad=copy.deepcopy(inp);change(bad)
            try:run(bad,n)
            except C.Invalid as e:assert fragment in str(e);checks.append(name)
            else:raise AssertionError(name+' accepted')
        run(inp,n)
        try:C.verify(a,b,expected_input_sha256='0'*64,progress=0)
        except C.Invalid as e:assert 'digest mismatch' in str(e);checks.append('wrong external input binding')
        else:raise AssertionError('wrong input digest accepted')
    r={'status':'PASS','count':len(checks),'test_groups':checks}
    Path(__file__).with_name('independent_supplemental_tests.json').write_text(json.dumps(r,indent=2)+chr(10));print(json.dumps(r))
if __name__=='__main__':main()
