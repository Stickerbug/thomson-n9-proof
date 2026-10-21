if not __debug__:
 raise RuntimeError('Run without -O')
from fractions import Fraction as F
from pathlib import Path
import json
H=lambda d:2/d**3-F(1,4)/d
delta=F(43,10000);theta=F(93,1000);dm=F(469,500)-theta/2
assert 2*delta/(1-delta/2)<theta**2
assert dm==F(1783,2000)
assert 4-2*delta>F(199,100)**2
M=F(7,2)*H(dm)+F(1,4);cost=M*theta**2/2
assert F(129,5)-cost>F('25.759986531269832')
assert F(56,100)+theta/2==F(1213,2000)<F(63,100)
saved=json.loads(Path('proof_work/antipodal_anchor2580_2026_symmetric9957_exact.json').read_text())
assert saved['movement_cost']==str(cost) and saved['Hessian_upper']==str(M)
print('PASS strongest symmetric global-minimizer exclusion -9957/10000')
