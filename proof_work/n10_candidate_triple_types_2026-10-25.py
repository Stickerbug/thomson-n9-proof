"""Exact symbolic classification of D4d n=10 candidate triples.

Discovery/geometry input only: h is symbolic and no global residual theorem is
claimed.  The output records the twelve unordered inner-product types among
the 120 candidate triangles and their Gram determinants.
"""
import itertools
import json
from pathlib import Path
import sympy as s

h = s.symbols('h', real=True)
q = s.sqrt(2)
r = s.sqrt(1-h**2)
points = [s.Matrix([0, 0, 1]), s.Matrix([0, 0, -1])]
for j in range(4):
    a = s.pi*j/2
    points.append(s.Matrix([r*s.cos(a), r*s.sin(a), -h]))
for j in range(4):
    a = s.pi*j/2+s.pi/4
    points.append(s.Matrix([r*s.cos(a), r*s.sin(a), h]))
gram = [[s.simplify(s.nsimplify(points[i].dot(points[j])))
         for j in range(10)] for i in range(10)]

types = {}
for i, j, k in itertools.combinations(range(10), 3):
    vals = tuple(sorted((gram[i][j], gram[i][k], gram[j][k]),
                        key=lambda z: str(z)))
    key = tuple(str(s.factor(z)) for z in vals)
    det = s.factor(1 + 2*vals[0]*vals[1]*vals[2] -
                   sum(z*z for z in vals))
    row = types.setdefault(key, {'inner_products': list(key),
                                 'multiplicity': 0,
                                 'gram_determinant': str(det)})
    row['multiplicity'] += 1

result = {
    'status': 'EXACT_SYMBOLIC_D4D_TRIPLE_CLASSIFICATION',
    'instance_n': 10,
    'triangle_count': 120,
    'type_count': len(types),
    'pair_inner_products': sorted({str(gram[i][j])
                                   for i, j in itertools.combinations(range(10), 2)}),
    'types': sorted(types.values(), key=lambda row: row['inner_products']),
    'scope': 'symbolic candidate geometry only; no global lower-bound or uniqueness theorem',
}
out = Path(__file__).with_suffix('.json')
out.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'status': result['status'], 'type_count': len(types),
                  'triangle_count': 120}))
