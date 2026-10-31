#!/usr/bin/env python3
"""D3, Section 10.3: mean of S(p)/p - (1/2)log p - (4/pi) R_K(p), K = 3002 (odd k <= 3001),
over the primes 3001 < p <= hi, for hi = 4e6 (to reproduce the printed v3 numbers
0.23993, 282715 primes, s.e. 4e-5, s.d. 0.022) and hi = 6e6.
R_K(p) = sum_{3<=k<K, k odd} F_k(p)/k^2, F_k(n) = sum_{t=1}^{(k-1)/2} tan(pi n t/k).
Needs PSX.npy from numerics_6e6.py."""
import math, numpy as np
D = "./"
P, S, X = np.load(D + "PSX.npy"); P = P.astype(np.int64)
K = 3002
R = np.zeros(len(P))
for k in range(3, K, 2):
    tanv = np.tan(np.pi * np.arange(k) / k)
    t = np.arange(1, (k - 1) // 2 + 1)
    r = np.arange(k)[:, None]
    Fk = tanv[(r * t[None, :]) % k].sum(axis=1)          # F_k(r), r = 0..k-1
    R += Fk[P % k] / k ** 2
np.save(D + "R3002.npy", R)
c0 = 0.23993410363206946768
Y = X - 4 / math.pi * R
for hi in (4_000_000, 6_000_000):
    sel = (P > 3001) & (P <= hi)
    y = Y[sel]
    print(f"3001 < p <= {hi:.0e}: n = {sel.sum()}, mean {y.mean():.6f}, sd {y.std(ddof=1):.4f},"
          f" se {y.std(ddof=1)/math.sqrt(sel.sum()):.1e}, mean - c0 = {y.mean()-c0:+.1e}")
