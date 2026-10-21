"""Replay the new N=9 proof candidate into a fresh directory.
Mathematical geometry and harmonic PSD arguments are documented in the manuscript.
"""
import argparse
from pathlib import Path
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--outdir',required=True,type=Path,help='New, nonexistent output directory; never overwritten')
args=parser.parse_args()
if not __debug__:raise RuntimeError('Run without -O')
if args.outdir.exists():parser.error('Output directory already exists; choose a fresh path')
import relative_normal2026_replay2 as replay
replay.OUT=args.outdir.resolve()
replay.main()
print('Numerical premises and complete sharp coverage replayed. See manuscript for mathematical arguments and review limits.')
