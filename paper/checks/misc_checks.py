#!/usr/bin/env python3
"""Small checks for round 2: c0 digits (1.6), K0, root of L = 8(log L)^6 (Section 11),
p = 999983 factorizations, Theorem C nontrivial range, A = A_BG + 1 absorbs log 3,
rho(lambda)/lambda^2 -> 7 pi^2/72 (Lemma 4.2 remark)."""
from mpmath import mp, mpf, euler, log, pi, zeta, findroot, quad, tanh, coth, inf
from sympy import factorint
mp.dps = 40
K0 = euler + log(4 / pi)
c0 = K0 / 2 + log(2) / 6 + 3 / pi**2 * zeta(2, derivative=1)
print("K0 =", K0); print("c0 =", c0)
f = lambda L: L - 8 * log(L) ** 6
r = findroot(f, mpf("5e8")); print("root of L = 8(log L)^6 near 5e8:", r, " check f(5.2e8) =", f(mpf("5.2e8")), " f(5e8) =", f(mpf("5e8")))
p = 999983
for n in (p - 1, p + 1, 2 * p - 1, 2 * p + 1):
    print(n, factorint(n))
# rho(lambda)/lambda^2 at small lambda from the definition of I
def I(lam):
    return quad(lambda v: (mp.cosh(v) - mp.cosh(lam * v)) / (mp.sinh(v) * mp.sinh(lam * v)), [0, 1, 10, 100 / lam, 2000 / lam]) / pi
for lam in (mpf("0.01"), mpf("0.001")):
    rho = log(1 / lam) + K0 - pi * lam * I(lam)
    print("lambda", lam, "rho/lambda^2 / (7pi^2/72) =", rho / lam**2 / (7 * pi**2 / 72))

# p = 999983: contribution of moduli k | 2p-1 to (4/pi) R_3002(p)
import numpy as np, math
D = "./"
P, S, X = np.load(D + "PSX.npy"); R = np.load(D + "R3002.npy")
i = int(np.searchsorted(P, p)); c0f = float(c0)
def F(k, n):
    return sum(math.tan(math.pi * n * t / k) for t in range(1, (k - 1) // 2 + 1))
part = sum(F(k, p) / k**2 for k in range(3, 3002, 2) if (2 * p - 1) % k == 0)
print("p=999983: X_p - c0 =", X[i] - c0f, " (4/pi)R_3002 =", 4 / math.pi * R[i],
      " (4/pi)*part from k | 2p-1 =", 4 / math.pi * part)
# Section 1.3 / 11: margin of Conjecture 3.2 at p = 6e6: S(p)/p - (1/2)log p > 3 - (1/2)log p
print("3 - (1/2) log(6e6) =", 3 - 0.5 * math.log(6e6))
# Theorem C: error/main = 2 L^(g - 1/3) (log L)^(8/3), L = log p; tends to 0 iff g < 1/3 (asymptotically)
import sympy as sp
L = sp.symbols('L', positive=True)
for g in (sp.Rational(3, 10), sp.Rational(1, 3)):
    print("gamma0 =", g, ": limit of error/main as log p -> oo is", sp.limit(2 * L**(g - sp.Rational(1, 3)) * sp.log(L)**sp.Rational(8, 3), L, sp.oo))
