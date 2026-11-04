#!/usr/bin/env python3
"""Check (ii) of Section 9.2 of theta_sum_conj33.pdf: compare the output of sp.c (lines "p S(p)")
with data/S_p_upto_6e6.txt.gz. The published run covered all 129703 primes 4e6 < p <= 6e6.
Usage: python3 -I compare_recompute.py [out1.txt ...]   (default: out*.txt in this directory)
"""
import glob, gzip, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
with gzip.open(os.path.join(HERE, "..", "..", "data", "S_p_upto_6e6.txt.gz"), "rt") as fh:
    d = {int(a): int(b) for a, b in (line.split() for line in fh)}
files = sys.argv[1:] or sorted(glob.glob(os.path.join(HERE, "out*.txt")))
n = bad = 0
for f in files:
    for line in open(f):
        p, s = map(int, line.split()); n += 1
        if d.get(p) != s:
            bad += 1; print("MISMATCH", p, s, d.get(p))
print("compared", n, "mismatches", bad, "(primes 4e6 < p <= 6e6 in the data:", sum(1 for p in d if p > 4000000), ")")
