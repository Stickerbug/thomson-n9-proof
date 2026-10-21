"""Conditional native signed128 Bernstein coverage of the symmetric Gram domain.

This module verifies only a polynomial interval and geometric coverage statement.
It does not establish coefficient enclosures, symmetry of the unknown true R,
local nonnegativity certificates, PSD, pair reduction, or any Thomson bound.
No CLI or resume interface is supplied.
"""
if not __debug__:
    raise RuntimeError('Conditional away replay requires assertions; do not use python -O.')
from fractions import Fraction
from hashlib import sha256
from itertools import permutations
from math import isfinite
from pathlib import Path
from time import monotonic
import json
import numpy as np
from exact_tensor_bernstein import coefficients
import exact128_2026 as native_backend
from exact128_2026 import NativeTensor

ROOT_BOX = ((Fraction(-1), Fraction(14, 25)),) * 3
GRAM = {(0, 0, 0): Fraction(1), (1, 1, 1): Fraction(2),
        (2, 0, 0): Fraction(-1), (0, 2, 0): Fraction(-1),
        (0, 0, 2): Fraction(-1)}


def _rational(value):
    if isinstance(value, (float, np.floating, bool)):
        raise TypeError('Exact rational input required; floating-point and bool inputs are rejected.')
    return Fraction(value)


def _center(value):
    if len(value) != 3:
        raise ValueError('center must contain three rational intervals')
    ans = tuple(tuple(_rational(z) for z in pair) for pair in value)
    if any(len(p) != 2 or p[0] > p[1] for p in ans):
        raise ValueError('invalid center interval')
    return ans


def split_outward(tensor, axis, upper=False):
    """Split same-scale signed128 tensor with EACH average rounded outward.

    The backend first checks strict abs(value)<2^124. Every average preserves
    that bound; the sum plus rounding flag safely fits signed128. Stepwise
    floor/ceil gives valid enclosures, potentially wider than rounding only the
    final exact binomial sum. No scale conversion or floating arithmetic occurs.
    """
    assert isinstance(tensor, NativeTensor)
    return tensor.split(axis, upper=upper)


def _normalize(poly_intervals, local_regions, boundary_multipliers):
    poly = {}
    for powers, interval in poly_intervals.items():
        if len(powers) != 3 or any(type(n) is not int or n < 0 for n in powers):
            raise ValueError('powers must be triples of nonnegative Python integers')
        if len(interval) != 2:
            raise ValueError('each coefficient requires a lower and an upper endpoint')
        lo, hi = map(_rational, interval)
        if lo > hi:
            raise ValueError('coefficient interval is reversed')
        poly[tuple(powers)] = (lo, hi)
    local = []
    for i, region in enumerate(local_regions):
        center = _center(region['center'])
        width = _rational(region['halfwidth'])
        if width < 0:
            raise ValueError('local halfwidth must be nonnegative')
        # Intersection of the cubes for ALL possible exact centers; never midpoint +/- delta.
        core = tuple((hi - width, lo + width) for lo, hi in center)
        local.append({'id': str(region.get('id', i)), 'center': center,
                      'halfwidth': width, 'core': core})
    boundary = []
    for i, item in enumerate(boundary_multipliers):
        center = _center(item['centerI'])
        lam = _rational(item['lambda'])
        assert lam >= 0, 'boundary lambda must be nonnegative'
        radius = _rational(item.get('activation_radius', Fraction(1, 20)))
        if radius < 0:
            raise ValueError('activation radius must be nonnegative')
        activation = tuple((lo - radius, hi + radius) for lo, hi in center)
        boundary.append({'id': str(item.get('id', i)), 'centerI': center,
                         'lambda': lam, 'activation_radius': radius,
                         'activation': activation})
    return poly, local, boundary


def _serial(obj):
    if isinstance(obj, Fraction):
        return str(obj)
    if isinstance(obj, dict):
        return {str(k): _serial(v) for k, v in obj.items()}
    if isinstance(obj, (tuple, list)):
        return [_serial(x) for x in obj]
    return obj


def _hash(obj):
    return sha256(json.dumps(_serial(obj), sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def _intersects(box, other):
    return all(lo <= oh and ol <= hi for (lo, hi), (ol, oh) in zip(box, other))


def _contained(box, other):
    return all(ol <= lo <= hi <= oh for (lo, hi), (ol, oh) in zip(box, other))


def check_away(poly_intervals, local_regions, boundary_multipliers, budget, seconds, bits=80):
    """Return conditional coverage or a complete list of unresolved physical boxes.

    Preconditions supplied by the caller, NOT checked here:
      * true R is symmetric and each monomial coefficient lies in poly_intervals;
      * true R >= 0 on Gram >= 0 in each exact-center +/- local halfwidth cube.
    A local terminal uses [center_hi-delta, center_lo+delta], contained in every
    possible exact-center cube. Only u<=v<=t is traversed, using true symmetry.
    The boundary lemma uses L-lambda*g >= 0 and lambda >= 0 on Gram >= 0.
    seconds includes normalization/root transforms; transforms are not preempted.
    budget counts visited DFS nodes; budget=0 retains the complete root as pending.
    The return value contains JSON-compatible strings for all exact rationals.
    """
    start = monotonic()
    if type(budget) is not int or budget < 0:
        raise ValueError('budget must be a nonnegative integer')
    if type(bits) is not int or bits < 1:
        raise ValueError('bits must be a positive integer')
    if not isfinite(seconds) or seconds < 0:
        raise ValueError('seconds must be finite and nonnegative')
    poly, local, boundary = _normalize(poly_intervals, local_regions, boundary_multipliers)
    canonical_inputs = {'poly_intervals': [[list(k), list(v)] for k, v in sorted(poly.items())],
                        'local_regions': local, 'boundary_multipliers': boundary,
                        'root_box': ROOT_BOX, 'bits': bits, 'budget': budget, 'seconds': seconds}
    midpoint, eps = {}, Fraction(0)
    rounding_scale = 1 << 200
    for powers, (lo, hi) in poly.items():
        mid = Fraction(round((lo + hi) * rounding_scale / 2), rounding_scale)
        if mid:
            midpoint[powers] = mid
        eps += max(mid - lo, hi - mid)
    # True R symmetric => averaging p over all six permutations preserves eps error.
    symmetric = {}
    for permutation in permutations(range(3)):
        for powers, value in midpoint.items():
            key = tuple(powers[j] for j in permutation)
            symmetric[key] = symmetric.get(key, Fraction(0)) + value / 6
    lower = {k: v for k, v in symmetric.items() if v}
    lower[(0, 0, 0)] = lower.get((0, 0, 0), Fraction(0)) - eps
    lower = {k: v for k, v in lower.items() if v}
    assert eps >= 0
    degree = tuple(max((p[i] for p in lower), default=0) for i in range(3))
    degrees = tuple(max(n, 2) for n in degree) if boundary else degree
    B = coefficients(lower, ROOT_BOX, degrees=degrees, bits=bits)
    G = coefficients(GRAM, ROOT_BOX, bits=bits, upper=True)
    S = {}
    for i, item in enumerate(boundary):
        if not _intersects(ROOT_BOX, item['activation']):
            continue
        shifted = lower.copy()
        for powers, value in GRAM.items():
            shifted[powers] = shifted.get(powers, Fraction(0)) - item['lambda'] * value
        S[i] = coefficients({k: v for k, v in shifted.items() if v}, ROOT_BOX,
                            degrees=degrees, bits=bits)
    B, G = NativeTensor(B), NativeTensor(G)
    S = {i: NativeTensor(sb) for i, sb in S.items()}
    for tensor in (B, G, *S.values()):
        assert isinstance(tensor, NativeTensor)
    backend_paths = {'C': Path(native_backend.__file__).with_suffix('.c').resolve(),
                     'wrapper': Path(native_backend.__file__).resolve(),
                     'loaded_shared_library': Path(native_backend.library()._name).resolve()}
    backend_hashes = {key: sha256(path.read_bytes()).hexdigest()
                      for key, path in backend_paths.items()}
    initial_bounds = {'R_lower_min': str(B.min()), 'R_lower_max': str(B.max()),
                      'Gram_upper_min': str(G.min()), 'Gram_upper_max': str(G.max())}
    # Each stack entry represents one leaf of an exact binary partition of ROOT_BOX.
    stack = [(B, G, S, ROOT_BOX, (0, 0, 0), '')]
    counts = {'positive': 0, 'gram_negative': 0, 'ordered_disjoint': 0,
              'local_region': 0, 'boundary_multiplier': 0}
    local_counts = {x['id']: 0 for x in local}
    boundary_counts = {x['id']: 0 for x in boundary}
    visited = splits = maxdepth = activation_dropped = 0
    native_tensor_split_calls = 0
    def progress():
        if visited % 5000 == 0:
            print(json.dumps({'stage': 'native128_away_progress', 'visited': visited,
                  'elapsed_seconds': monotonic() - start, 'pending': len(stack),
                  'counts': counts, 'native_tensor_split_calls': native_tensor_split_calls}), flush=True)
    transcript = sha256()
    scale = 1 << bits
    guard_reason = None
    while stack and visited < budget and monotonic() - start < seconds:
        if len(stack)>256:
            guard_reason = 'pending_stack_exceeds256'
            break
        if len(stack[-1][-1])>150:
            guard_reason = 'next_path_depth_exceeds150'
            break
        b, g, active, box, levels, path = stack.pop()
        visited += 1
        maxdepth = max(maxdepth, len(path))
        kind, identifier, witness = None, None, None
        if any(box[i][0] > box[j][1] for i in range(3) for j in range(i + 1, 3)):
            kind = 'ordered_disjoint'
        elif g.max() < 0:
            kind, witness = 'gram_negative', int(g.max())
        elif b.min() >= 0:
            kind, witness = 'positive', int(b.min())
        else:
            for region in local:
                if _contained(box, region['core']):
                    kind, identifier = 'local_region', region['id']
                    local_counts[identifier] += 1
                    break
            if kind is None:
                for i, sb in active.items():
                    if sb.min() >= 0:
                        kind, identifier, witness = 'boundary_multiplier', boundary[i]['id'], int(sb.min())
                        boundary_counts[identifier] += 1
                        break
        if kind is not None:
            counts[kind] += 1
            transcript.update(json.dumps([path, kind, identifier, witness], separators=(',', ':')).encode() + b'\n')
            progress()
            continue
        axis = min(range(3), key=lambda i: levels[i])
        levels_child = list(levels)
        levels_child[axis] += 1
        levels_child = tuple(levels_child)
        lo, hi = box[axis]
        middle = (lo + hi) / 2
        boxes = [list(box), list(box)]
        boxes[0][axis], boxes[1][axis] = (lo, middle), (middle, hi)
        boxes = [tuple(x) for x in boxes]
        bs, gs = split_outward(b, axis), split_outward(g, axis, upper=True)
        native_tensor_split_calls += 2
        children_active = [{}, {}]
        for i, sb in active.items():
            eligible = [_intersects(child, boundary[i]['activation']) for child in boxes]
            activation_dropped += sum(not x for x in eligible)
            if any(eligible):
                ss = split_outward(sb, axis)
                native_tensor_split_calls += 1
                for side in range(2):
                    if eligible[side]:
                        children_active[side][i] = ss[side]
        # Right pushed first, so the traversal is left-first DFS. Both closed
        # children cover their parent exactly and overlap only on their face.
        for side in (1, 0):
            stack.append((bs[side], gs[side], children_active[side], boxes[side],
                          levels_child, path + str(side)))
        splits += 1
        progress()
    assert all(sha256(path.read_bytes()).hexdigest() == backend_hashes[key]
               for key, path in backend_paths.items()), 'Frozen native backend artifacts changed'
    terminals = sum(counts.values())
    assert visited == terminals + splits
    assert terminals + len(stack) == splits + 1
    pending = [{'path': path, 'box': _serial(box), 'axis_split_counts': list(levels),
                'active_boundary_ids': [boundary[i]['id'] for i in active]}
               for _, _, active, box, levels, path in reversed(stack)]
    status = 'away_certified_given_local_regions' if not stack else 'incomplete_budget_or_time'
    return {'status': status, 'guard_reason': guard_reason,
            'conditional_only': True,
            'premises_NOT_verified': ['true residual symmetric', 'true coefficient enclosure',
                                      'every supplied exact-center local Gram nonnegativity certificate'],
            'statement': 'R_true >= 0 on Gram PSD in [-1,14/25]^3, conditional on the explicitly listed premises' if not stack else 'No complete away-region conclusion; every unresolved partition leaf is retained',
            'root_box': _serial(ROOT_BOX), 'ordered_wedge': 'u <= v <= t',
            'degree': list(degree), 'tensor_degrees': list(degrees), 'bits': bits,
            'midpoint_rounding_bits': 200, 'eps': str(eps),
            'lower_polynomial_sha256': _hash([[list(p), v] for p, v in sorted(lower.items())]),
            'parent_selfhash': sha256(Path(__file__).read_bytes()).hexdigest(),
            'selfhash_scope': 'engine module; exact_tensor_bernstein plus native C/wrapper/loaded library separately hashed',
            'bernstein_dependency_sha256': sha256(Path(__import__('exact_tensor_bernstein').__file__).read_bytes()).hexdigest(),
            'inputhash': _hash(canonical_inputs), 'terminal_transcript_sha256': transcript.hexdigest(),
            'counts': counts, 'local_counts': local_counts, 'boundary_counts': boundary_counts,
            'activation_dropped_children': activation_dropped,
            'visited_nodes': visited, 'split_nodes': splits, 'terminal_leaves': terminals,
            'pending_count': len(pending), 'pending': pending,
            'root_coverage': {'binary_partition_complete': True,
                              'terminal_plus_pending_equals_splits_plus_one': terminals + len(stack) == splits + 1,
                              'visited_equals_terminal_plus_splits': visited == terminals + splits,
                              'pending_boxes_complete': True},
            'maxdepth': maxdepth, 'local_regions': _serial(local),
             'restart_from_full_root': True, 'frontier_resumed': False,
             'arithmetic_backend': 'signed128-native', 'native_safe_abs': str(1 << 124),
             'native_rounding': 'each midpoint average floor lower / ceil upper; original integer scale',
             'native_tensor_split_calls': native_tensor_split_calls,
             'native_backend_sha256': backend_hashes,
             'native_backend_paths': {key: str(path) for key, path in backend_paths.items()},
            'boundary_multipliers': _serial(boundary),
            'initial_scaled_integer_bounds': initial_bounds,
            'scale': str(scale), 'elapsed_seconds': monotonic() - start}
