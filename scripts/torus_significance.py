#!/usr/bin/env python3
"""Torus comparison with standard errors (simulation): peak over the offered loads, mean and
standard error of 8 seeds (11 to 18, unused by the other scripts).

Usage: python3 scripts/torus_significance.py dor,val,ugal,bandit2m7f5k \
           uniform,transpose,shuffle,bitrev,bitcomp,hotspot,tornado,neighbor,randperm \
           0.4,0.5,0.55,0.6,0.65,0.7,0.8,1.0
"""
import sys
from multiprocessing import Pool
import torus_experiments as T
pats = sys.argv[2].split(',')
schemes = sys.argv[1].split(',')
rates = [float(x) for x in sys.argv[3].split(',')] if len(sys.argv) > 3 else [0.55, 0.6, 0.65, 0.7, 0.75, 0.8, 0.9]
seeds = range(11, 19)
jobs = [(s, r, p, sd) for s in schemes for r in rates for p in pats for sd in seeds]
with Pool() as pool: res = dict(zip(jobs, pool.map(T.job, jobs)))
print(f'{"scheme":<18}' + ''.join(f'{p[:9]:>16}' for p in pats))
for s in schemes:
    cells = []
    for p in pats:
        means = {r: sum(res[(s, r, p, x)] for x in seeds) / len(seeds) for r in rates}
        r = max(rates, key=means.get); m = means[r]
        v = [res[(s, r, p, x)] for x in seeds]
        se = (sum((a - m) ** 2 for a in v) / (len(v) - 1)) ** .5 / len(v) ** .5
        cells.append(f'{m:.4f}±{se:.4f}')
    print(f'{s:<18}' + ''.join(f'{c:>16}' for c in cells), flush=True)
