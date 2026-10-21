"""Classify generated AAA term bounds and verify the sign-aware coarse replay.

This is a numeric feasibility check, not a Lean proof. It reads only generated
Lean sources. It exists to test the next certificate design: zero terms are
already fast; every nonzero term bound is either one-sided at zero or symmetric
about zero, so a sign-aware/absolute-value proof should reproduce the archived
chunk and target intervals exactly.
"""
from fractions import Fraction as Q
from pathlib import Path
import re
import sys

BASE = Path(__file__).resolve().parent
FORMAL = BASE / 'formal/ThomsonNine'
TARGET_RE = re.compile(
    r'def targetH00 : RatInterval := ⟨\((.*?) : ℚ\), \((.*?) : ℚ\), by norm_num⟩')
TERM_RE = re.compile(
    r'private def termBound_(\d+) : RatInterval := ⟨\((.*?) : ℚ\), \((.*?) : ℚ\), by norm_num⟩')
CHUNK_RE = re.compile(
    r'def chunkInterval_(\d+) : RatInterval := ⟨\((.*?) : ℚ\), \((.*?) : ℚ\), by norm_num⟩')


def rat(text):
    text = text.strip().strip('()')
    if '/' in text:
        a, b = text.split('/')
        return Q(int(a), int(b))
    return Q(int(text))


def intervals(path, regex):
    text = path.read_text()
    return {int(m.group(1)): (rat(m.group(2)), rat(m.group(3)))
            for m in regex.finditer(text)}


def classify(lo, hi):
    if lo == 0 and hi == 0:
        return 'zero'
    if lo == 0 and hi > 0:
        return 'nonneg'
    if lo < 0 and hi == 0:
        return 'nonpos'
    if lo < 0 < hi:
        scale = max(abs(lo), abs(hi))
        if abs(lo + hi) / scale < Q(1, 10 ** 80):
            return 'symmetric'
        return 'asymmetric'
    if lo > 0 and hi > 0:
        return 'point' if lo == hi else 'positive_interval'
    if lo < 0 and hi < 0:
        return 'negative_interval'
    return 'other'


def coarse(bound):
    """Return the archived bound itself; grading is a shape check, not a replacement."""
    lo, hi = bound
    return (lo, hi), classify(lo, hi)



def main():
    base = (FORMAL / 'LocalSparseHessianAAABase.lean').read_text()
    m = TARGET_RE.search(base)
    if not m:
        raise SystemExit('targetH00 not found')
    target = (rat(m.group(1)), rat(m.group(2)))
    terms = {}
    chunks = {}
    for path in sorted(FORMAL.glob('LocalSparseHessianAAAChunk*.lean')):
        terms.update(intervals(path, TERM_RE))
        chunks.update(intervals(path, CHUNK_RE))
    if len(terms) != 807:
        raise SystemExit(f'expected 807 terms, got {len(terms)}')
    counts = {}
    replay = (Q(0), Q(0))
    for k in sorted(terms):
        bound, kind = coarse(terms[k])
        counts[kind] = counts.get(kind, 0) + 1
        replay = (replay[0] + bound[0], replay[1] + bound[1])
    print('term shapes:', ', '.join(f'{k}={v}' for k, v in sorted(counts.items())))
    if 'asymmetric' in counts or 'other' in counts:
        raise SystemExit('some terms are not zero/one-sided/symmetric')
    if counts.get('positive_interval', 0) + counts.get('negative_interval', 0) > 1:
        raise SystemExit('more than one exceptional interval term')
    if replay != target:
        raise SystemExit(f'term replay {replay} != target {target}')
    print('target exact match:', float(target[0]), float(target[1]))
    for path in sorted(FORMAL.glob('LocalSparseHessianAAAChunk*.lean')):
        local_terms = intervals(path, TERM_RE)
        local_chunks = intervals(path, CHUNK_RE)
        for c, bound in sorted(local_chunks.items()):
            got = (sum(local_terms[k][0] for k in local_terms),
                   sum(local_terms[k][1] for k in local_terms))
            if got != bound:
                raise SystemExit(f'chunk {c} replay {got} != {bound}')
    print(f'chunk replay exact: {len(chunks)} chunks')
    print('SIGN_AWARE_SHAPE_CHECK_PASS')

if __name__ == '__main__':
    main()
