"""NONRIGOROUS independent audit of saved d6 sharp solution."""
import json
from pathlib import Path
import numpy as np
from sharp_three_point import validate
from three_point_sampled import minorant
p=Path(__file__).with_name('sharp_three_point_d6_eq.json')
data=json.loads(p.read_text());A=list(map(np.array,data['solution']['A']));c=data['solution']['c'];h,_,_,_=minorant()
validation,_=validate(6,A,c,h,np.random.default_rng(713379),count=30000)
out=Path(__file__).with_name('sharp_d6_final_validation.json');assert not out.exists()
out.write_text(json.dumps({'warning':'NONRIGOROUS; concrete counterexamples to the polynomial residual, not counterexamples to Thomson candidate.','validation':validation},indent=2)+'\n')
print(json.dumps(validation,indent=2))
