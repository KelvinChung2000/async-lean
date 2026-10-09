#!/usr/bin/env python3
"""The final torus comparison of the README (simulation): peak accepted throughput over offered
loads 0.3 to 1.0, mean of 4 seeds, all nine patterns.

Usage: python3 scripts/torus_final.py dor,min,val,ugal,bandit2m7f5k
"""
import sys
from multiprocessing import Pool
import torus_experiments as T
pats = T.PATS
schemes = sys.argv[1].split(',')
rates = [0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 1.0]
seeds = range(1, 5)
jobs = [(s, r, p, sd) for s in schemes for r in rates for p in pats for sd in seeds]
with Pool() as pool: res = dict(zip(jobs, pool.map(T.job, jobs)))
print(f'{"scheme":<16}' + ''.join(f'{p[:9]:>10}' for p in pats))
for s in schemes:
    cells = []
    for p in pats:
        means = {r: sum(res[(s, r, p, x)] for x in seeds) / len(seeds) for r in rates}
        r = max(rates, key=means.get)
        m = means[r]
        cells.append(f'{m:.3f}')
    print(f'{s:<16}' + ''.join(f'{c:>10}' for c in cells), flush=True)
