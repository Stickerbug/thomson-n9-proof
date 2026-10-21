"""Stronger fixed-triangle thresholds; original verifiers remain unchanged."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json
import verify_fixed_triangle_two_caps_widened_v1 as verifier
verifier.M=F(1,25000)
verifier.TAU=F(21,200000)
if __name__=='__main__':
 report=verifier.run()
 report['wrapper_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
 report['wrapper_source']=str(Path(__file__))
 out=Path(__file__).with_name('fixed_triangle_two_caps_stronger_certificate_v1.json')
 out.write_text(json.dumps(report,indent=2)+'\n')
 print('SAVED',out,report['status'],'sixlower=',report['six_point_cost_lower'],flush=True)
 if report['status']!='certified_fixed_triangle_two_cap_bounds':raise SystemExit(2)
