#!/usr/bin/env python3
"""Recompute the numerical claims of theta_sum_conj33.pdf that are read off the list of values
data/S_p_upto_6e6.txt.gz (lines "p S(p)", all odd primes p <= 6e6):

  * the table of values of S(p) in Section 1.1;
  * Theorem 1.1(a), |S(p)| <= (2/pi^2) p (log p + 2)^2, on the computed range;
  * Proposition 1.2 (Section 9.3): the thresholds 5, 233, 3119, 58013, 869399 and S(p_m);
  * the minima of S(p)/p after Proposition 1.2 and the bound S(p)/p > 5.82 on (5e6, 6e6];
  * Section 9.4: mean, standard deviation, minimum and maximum of X_p = S(p)/p - (1/2) log p,
    and Table 1 (in Section 9.4);
  * Section 9.2: the prime counts, and agreement of data/crosscheck_floorsum*.txt (output of
    code/floorsum_check.c) with the list, including the 20 extreme values of X_p on (1e5, 5e6].

Usage: python3 -I numerics_6e6.py [values.txt[.gz]]   (default: data/S_p_upto_6e6.txt.gz)
"""
import gzip, math, os, sys
import numpy as np

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
DATA = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, "data", "S_p_upto_6e6.txt.gz")


def read_pairs(path):
    opener = gzip.open if path.endswith(".gz") else open
    with opener(path, "rt") as f:
        return [tuple(map(int, line.split())) for line in f if line.strip() and not line.startswith("#")]


pairs = read_pairs(DATA)
P = np.array([p for p, _ in pairs], dtype=np.int64)
S = np.array([s for _, s in pairs], dtype=np.int64)
assert np.all(np.diff(P) > 0)

# completeness: the file holds exactly the odd primes <= 6e6
N = 6_000_000
sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(N ** 0.5) + 1):
    if sieve[i]:
        sieve[i * i::i] = False
odd_primes = np.nonzero(sieve)[0]; odd_primes = odd_primes[odd_primes > 2]
assert np.array_equal(odd_primes, P), "data is not exactly the odd primes <= 6e6"
print("odd primes <= 6e6:", len(P), "  <= 4e6:", int(np.sum(P <= 4_000_000)),
      "  in (4e6, 6e6]:", int(np.sum(P > 4_000_000)))

c0 = 0.2399341036320694676850476643893461879171
X = S / P - 0.5 * np.log(P.astype(float))
val = dict(zip(P.tolist(), S.tolist()))

print("\n== Section 1.1: values of S(p) ==")
print("  " + ", ".join(f"S({p}) = {val[p]}" for p in (3, 5, 7, 11, 13, 101, 233, 1009, 3119, 999983)))

print("\n== Theorem 1.1(a): max of |S(p)| / ((2/pi^2) p (log p + 2)^2) ==")
ratio = np.abs(S) / ((2 / math.pi ** 2) * P * (np.log(P.astype(float)) + 2) ** 2)
i = int(np.argmax(ratio))
print(f"  {ratio[i]:.4f} at p = {P[i]}  (bound holds: {bool(ratio[i] <= 1)})")

print("\n== Proposition 1.2: last p <= 6e6 with S(p) <= m p ==")
print("  S(p) > 0 for all:", bool(np.all(S > 0)))
for m in range(1, 6):
    bad = P[S <= m * P]
    pm = int(bad[-1])
    print(f"  m = {m}: p_m = {pm}, S(p_m) = {val[pm]}, m p_m = {m * pm}")

print("\n== minima of S(p)/p ==")
for lo in (3119, 58013, 869399, 5_000_000):
    sel = P > lo
    r = S[sel] / P[sel]; i = int(np.argmin(r))
    print(f"  ({lo}, 6e6]: min S/p = {r[i]:.4f} at p = {P[sel][i]}")

print("\n== Section 9.4: X_p = S(p)/p - (1/2) log p ==")
i, j = int(np.argmin(X)), int(np.argmax(X))
print(f"  all odd p <= 6e6: min {X[i]:.3f} at {P[i]}, max {X[j]:.3f} at {P[j]}")
sel = P > 1000
print(f"  1e3 < p <= 6e6: n = {sel.sum()}, mean {X[sel].mean():.4f}, sd {X[sel].std(ddof=1):.3f}"
      f"  (c0 = {c0:.5f})")

print("\n== Table 1 (Section 9.4) ==")
edges = [1e3, 2e5, 1e6, 2e6, 3e6, 4e6, 5e6, 6e6]
for lo, hi in zip(edges[:-1], edges[1:]):
    sel = (P > lo) & (P <= hi)
    x = X[sel]; pp = P[sel]
    i, j = int(np.argmin(x)), int(np.argmax(x))
    print(f"  ({lo:.0e},{hi:.0e}]  {sel.sum():6d}  mean {x.mean():.4f}  sd {x.std(ddof=1):.3f}"
          f"  min {x[i]:.3f} ({pp[i]})  max {x[j]:.3f} ({pp[j]})")

print("\n== Section 9.2: data/crosscheck_floorsum*.txt against the list ==")
sel = (P > 100_000) & (P <= 5_000_000)
order = np.argsort(X[sel])
extremes = set(P[sel][order[:15]].tolist()) | set(P[sel][order[-5:]].tolist())
for name in ("crosscheck_floorsum_upto_2e5.txt", "crosscheck_floorsum.txt"):
    cc = read_pairs(os.path.join(ROOT, "data", name))
    ps = [p for p, _ in cc]
    bad = sum(1 for p, s in cc if val.get(p) != s)
    line = f"  {name}: {len(cc)} values ({len(set(ps))} distinct primes), mismatches {bad}"
    if name == "crosscheck_floorsum_upto_2e5.txt":
        line += f", covers all odd primes < 2e5: {sorted(ps) == P[P < 200_000].tolist()}"
    else:
        line += f", contains the 15 smallest and 5 largest X_p on (1e5, 5e6]: {extremes <= set(ps)}"
    print(line)
