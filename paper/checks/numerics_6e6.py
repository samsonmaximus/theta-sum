#!/usr/bin/env python3
"""D3: recompute every statistic of Section 10, Table 2 (observed class means), Table 3,
the thresholds/minima, Remark 3.4 and the page-2 statistics from the exact data
../../data/S_p_upto_6e6.txt.gz (lines "p S(p)", all odd primes <= 6e6).
Usage: python3 -I numerics_6e6.py
"""
import gzip, math
import numpy as np

DATA = "../../data/S_p_upto_6e6.txt.gz"
P, S = [], []
with gzip.open(DATA, "rt") as f:
    for line in f:
        a, b = line.split()
        P.append(int(a)); S.append(int(b))
P = np.array(P, dtype=np.int64); S = np.array(S, dtype=np.int64)
assert np.all(np.diff(P) > 0)

# primality / completeness check: sieve up to 6e6
N = 6_000_000
sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(N ** 0.5) + 1):
    if sieve[i]:
        sieve[i * i::i] = False
odd_primes = np.nonzero(sieve)[0]; odd_primes = odd_primes[odd_primes > 2]
assert np.array_equal(odd_primes, P), "data is not exactly the odd primes <= 6e6"
print("odd primes <= 6e6:", len(P), " <= 4e6:", int(np.sum(P <= 4_000_000)))

gamma = 0.5772156649015329
K0 = gamma + math.log(4 / math.pi)
c0 = 0.2399341036320694676850476643893461879171
X = S / P - 0.5 * np.log(P.astype(float))

print("\n== thresholds: last p with S(p) <= m p ==")
for bound in (4_000_000, 6_000_000):
    sel = P <= bound
    out = []
    for m in range(0, 7):
        bad = P[sel][S[sel] <= m * P[sel]]
        out.append((m, int(bad[-1]) if len(bad) else None))
    print(f"  p <= {bound:.0e}:", out)
print("  S(5), S(233), S(3119):", dict(zip(P[np.isin(P, [5, 233, 3119])].tolist(), S[np.isin(P, [5, 233, 3119])].tolist())))
for p0, m in ((58013, 4), (869399, 5), (5935409, 6), (3958499, 6)):
    i = np.searchsorted(P, p0); print(f"  S({p0}) = {S[i]},  S/p = {S[i]/p0:.4f}  (< {m}p: {S[i] < m*p0})")
print("  S(p) > 0 for all:", bool(np.all(S > 0)))

print("\n== minima of S(p)/p ==")
for lo in (3119, 58013, 869399, 5_000_000):
    for hi in (4_000_000, 6_000_000):
        sel = (P > lo) & (P <= hi)
        if not sel.any(): continue
        r = S[sel] / P[sel]; i = np.argmin(r)
        print(f"  ({lo}, {hi:.0e}]: min S/p = {r[i]:.5f} at p = {P[sel][i]}")

print("\n== X_p = S(p)/p - (1/2)log p ==")
for hi in (4_000_000, 6_000_000):
    sel = P <= hi
    i, j = np.argmin(X[sel]), np.argmax(X[sel])
    print(f"  all odd p <= {hi:.0e}: min {X[sel][i]:.4f} at {P[sel][i]}, max {X[sel][j]:.4f} at {P[sel][j]}")
    sel2 = (P > 1000) & (P <= hi)
    print(f"  1e3 < p <= {hi:.0e}: n = {sel2.sum()}, mean {X[sel2].mean():.5f}, sd {X[sel2].std(ddof=1):.5f}")

print("\n== Table 3 (statistics by range) ==")
edges = [1e3, 2e5, 1e6, 2e6, 3e6, 4e6, 5e6, 6e6]
for lo, hi in zip(edges[:-1], edges[1:]):
    sel = (P > lo) & (P <= hi)
    x = X[sel]; pp = P[sel]
    i, j = np.argmin(x), np.argmax(x)
    print(f"  ({lo:.0e},{hi:.0e}]  {sel.sum():6d}  mean {x.mean():.4f}  sd {x.std(ddof=1):.3f}"
          f"  min {x[i]:.3f} ({pp[i]})  max {x[j]:.3f} ({pp[j]})")

print("\n== Table 2 (class means over 1e3 < p <= hi) ==")
classes = [(3, 1), (3, 2), (5, 1), (5, 2), (5, 3), (5, 4), (7, 1), (7, 6), (9, 1), (9, 8), (4, 1), (4, 3)]
for hi in (4_000_000, 6_000_000):
    print(f"  hi = {hi:.0e}")
    base = (P > 1000) & (P <= hi)
    for q, r in classes:
        sel = base & (P % q == r)
        x = X[sel]
        print(f"    q={q} r={r}: mean {x.mean():.4f}  se {x.std(ddof=1)/math.sqrt(len(x)):.4f}  n {len(x)}")

print("\n== Remark 3.4: |S(p)| / ((2/pi^2) p (log p + K0)^2) ==")
for hi in (4_000_000, 6_000_000):
    sel = P <= hi
    ratio = np.abs(S[sel]) / ((2 / math.pi ** 2) * P[sel] * (np.log(P[sel].astype(float)) + K0) ** 2)
    i = np.argmax(ratio)
    print(f"  p <= {hi:.0e}: max ratio {ratio[i]:.4f} at p = {P[sel][i]}")

print("\n== page 2: p = 999983 ==")
i = np.searchsorted(P, 999983)
print(f"  S = {S[i]}, S/p = {S[i]/999983:.4f}, (1/2)log p = {0.5*math.log(999983):.4f},"
      f" (1/2)log p + c0 = {0.5*math.log(999983)+c0:.4f}, X_p - c0 = {X[i]-c0:.4f}")
for p0 in (3, 5, 7, 11, 13, 101, 233, 1009, 3119, 999983):
    print(f"  S({p0}) = {S[np.searchsorted(P, p0)]}")
np.save("./PSX.npy",
        np.stack([P.astype(float), S.astype(float), X]))
