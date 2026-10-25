"""Numerical three-point SDP discovery for Thomson n=10.

This is deliberately a discovery tool.  It uses CVXPY/Clarabel, floating-point
sampling, and differential refinement; the output is not a certificate and is
never imported by Lean.  The normalization is the n=10 analogue of the n=9
three-point identity: an admissible kernel contributes ``8 F + d`` and the
objective is ``15*c - (5/3) F(1,1,1)``.
"""
from __future__ import annotations

import itertools
import json
import time
from pathlib import Path

import cvxpy as cp
import numpy as np
from scipy.optimize import differential_evolution

N = 10
H = 0.422687424043986066
ENERGY = 32.71694946014759


def kernels(points: np.ndarray, degree: int):
    out = [np.zeros((len(points), degree-k+1, degree-k+1))
           for k in range(degree + 1)]
    for perm in itertools.permutations(range(3)):
        u, v, t = points[:, perm].T
        a = t-u*v
        b = (1-u*u)*(1-v*v)
        q = [np.ones(len(points))]
        if degree:
            q.append(a)
        for k in range(1, degree):
            q.append(2*a*q[-1]-b*q[-2])
        for k in range(degree + 1):
            powers = np.arange(degree-k+1)
            z = u[:, None]**powers
            w = v[:, None]**powers
            out[k] += q[k][:, None, None]*z[:, :, None]*w[:, None, :]/6
    return out


def design(points: np.ndarray, degree: int):
    base = kernels(points, degree)
    repeated = [kernels(np.column_stack([np.ones(len(points)),
                                         points[:, j], points[:, j]]), degree)
                for j in range(3)]
    return [8*base[k] + sum(row[k] for row in repeated)
            for k in range(degree + 1)]


def sample(count: int, rng: np.random.Generator):
    u = rng.uniform(-1, 1, count)
    v = rng.uniform(-1, 1, count)
    theta = rng.uniform(0, np.pi, count)
    t = u*v + np.sqrt((1-u*u)*(1-v*v))*np.cos(theta)
    return np.column_stack([u, v, t])


def structured_points(grid_count: int = 31, angle_count: int = 7):
    """Deterministic interior and Gram-boundary points for discovery sampling."""
    values = np.linspace(-1, 1, grid_count)
    angles = np.linspace(0, np.pi, angle_count)
    rows = []
    for u in values:
        for v in values:
            rad = max(0.0, (1-u*u)*(1-v*v))**0.5
            for theta in angles:
                rows.append((u, v, u*v + rad*np.cos(theta)))
    return np.asarray(rows)


def candidate_triangles():
    r = np.sqrt(1-H*H)
    points = [[0, 0, 1], [0, 0, -1]]
    points += [[r*np.cos(2*np.pi*j/4), r*np.sin(2*np.pi*j/4), -H]
               for j in range(4)]
    points += [[r*np.cos(2*np.pi*j/4+np.pi/4),
                r*np.sin(2*np.pi*j/4+np.pi/4), H]
               for j in range(4)]
    gram = np.asarray(points) @ np.asarray(points).T
    triples = [[gram[i, j], gram[i, k], gram[j, k]]
               for i, j, k in itertools.combinations(range(N), 3)]
    return np.unique(np.round(triples, 13), axis=0)


def hermite_minorant():
    # Seven D4d pair nodes, doubled for Hermite interpolation.  This is only
    # a floating discovery model; the exact node/root layer is separate.
    r2 = H*H
    nodes = np.array([-1, -H, H, r2, 2*r2-1,
                      -r2+(1-r2)/np.sqrt(2),
                      -r2-(1-r2)/np.sqrt(2)])
    x = np.repeat(np.sort(nodes), 2)
    m = len(x)
    table = np.zeros((m, m))
    f = lambda t: (2-2*t)**-.5
    fp = lambda t: (2-2*t)**-1.5
    for i in range(m):
        table[i, 0] = f(x[i])
        if i:
            table[i, 1] = fp(x[i]) if x[i] == x[i-1] else (table[i, 0]-table[i-1, 0])/(x[i]-x[i-1])
        for j in range(2, i+1):
            table[i, j] = (table[i, j-1]-table[i-1, j-1])/(x[i]-x[i-j])
    coeff = np.diag(table)

    def evaluate(t):
        t = np.asarray(t)
        value = np.zeros_like(t)+coeff[-1]
        for j in range(m-2, -1, -1):
            value = coeff[j] + (t-x[j])*value
        return value

    return evaluate, x, coeff


def run(degree: int = 8, rounds: int = 4, initial_count: int = 4000,
        validation_count: int = 30000):
    started = time.time()
    rng = np.random.default_rng(20261025 + degree)
    minorant, nodes, hermite_coeff = hermite_minorant()
    points = np.vstack([sample(initial_count, rng), structured_points(),
                        candidate_triangles()])
    blocks = [cp.Variable((degree-k+1, degree-k+1), symmetric=True)
              for k in range(degree + 1)]
    c = cp.Variable()
    # F(1,1,1) is the sum of all entries of the k=0 coefficient matrix,
    # because the monomial feature vector is the all-ones vector at 1.
    objective = 15*c - (5/3)*cp.sum(blocks[0])
    history = []
    for iteration in range(rounds):
        mats = design(points, degree)
        lhs = c + sum(cp.sum(cp.multiply(m.reshape(len(points), -1),
                                         cp.reshape(a, (1, a.size), order='C')),
                             axis=1)
                      for m, a in zip(mats, blocks))
        rhs = np.sum(minorant(points), axis=1)
        problem = cp.Problem(cp.Maximize(objective),
                             [a >> 0 for a in blocks] + [lhs <= rhs])
        problem.solve(solver='CLARABEL', tol_gap_abs=1e-8,
                      tol_gap_rel=1e-8, tol_feas=1e-8, max_iter=220)
        if any(a.value is None for a in blocks):
            raise RuntimeError(problem.status)
        test = sample(validation_count, rng)
        test_mats = design(test, degree)
        values = [a.value for a in blocks]

        def evaluate(points):
            mats = design(np.asarray(points), degree)
            out = np.sum(minorant(np.asarray(points)), axis=1)-float(c.value)
            return out - sum(np.einsum('nij,ij->n', m, a)
                             for m, a in zip(mats, values))

        residual = evaluate(test)
        def objective_angles(z):
            u, v, theta = z
            t = u*v + np.sqrt(max(0.0, (1-u*u)*(1-v*v)))*np.cos(theta)
            return float(evaluate(np.asarray([[u, v, t]]))[0])

        de = differential_evolution(objective_angles,
                                    [(-1, 1), (-1, 1), (0, np.pi)],
                                    seed=20261025+degree+iteration,
                                    popsize=8, maxiter=55, polish=True,
                                    workers=1, updating='immediate')
        de_u, de_v, de_theta = de.x
        de_t = de_u*de_v + np.sqrt(max(0.0, (1-de_u*de_u)*(1-de_v*de_v)))*np.cos(de_theta)
        de_point = np.asarray([[de_u, de_v, de_t]])
        de_residual = float(de.fun)
        min_eig = min(float(np.linalg.eigvalsh(a.value).min()) for a in blocks)
        row = {
            'iteration': iteration,
            'status': problem.status,
            'objective': float(problem.value),
            'candidate_energy_reference': ENERGY,
            'candidate_gap_reference': ENERGY-float(problem.value),
            'validation_min_residual': float(residual.min()),
            'differential_evolution_min_residual': de_residual,
            'differential_evolution_point': de_point[0].tolist(),
            'training_count': len(points),
            'validation_count': validation_count,
            'min_psd_eigenvalue': min_eig,
            'seconds': time.time()-started,
        }
        history.append(row)
        print(json.dumps(row), flush=True)
        if min(float(residual.min()), de_residual) >= -1e-7:
            break
        points = np.vstack([points, test[np.argsort(residual)[:500]], de_point])
    result = {
        'status': 'NUMERICAL_DISCOVERY_ONLY',
        'warning': 'CVXPY/Clarabel floating SDP with finite sampling; not a global certificate and not a Lean theorem.',
        'instance_n': N,
        'degree': degree,
        'normalization': 'E >= 15*c - (5/3)*F(1,1,1), with residual c + 8F + d <= H(u)+H(v)+H(t)',
        'candidate_energy_reference': ENERGY,
        'root_height_reference': H,
        'hermite_nodes': nodes.tolist(),
        'hermite_coefficients': hermite_coeff.tolist(),
        'history': history,
        'solution': {
            'c': float(c.value),
            'blocks': [a.value.tolist() for a in blocks],
        },
        'elapsed_seconds': time.time()-started,
    }
    out = (Path(__file__).with_suffix('.json') if degree == 8 else
           Path(__file__).with_name(f'n10_three_point_sdp_discovery_degree{degree}_2026-10-25.json'))
    out.write_text(json.dumps(result, indent=2) + '\n')
    print('saved', out, flush=True)
    return result


if __name__ == '__main__':
    run()
