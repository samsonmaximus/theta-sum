#!/usr/bin/env python3
"""Small numerical claims of theta_sum_conj33.pdf, at 40 digits:
  * the constants kappa_0 (2.3) and c_0 (2.4);
  * Lemma 3.2: 0 <= rho(lambda) <= (7 pi^2/72) lambda^2, with ratio -> 1 as lambda -> 0
    (so the constant is sharp), and kappa_0 + 7 pi^2/72 < 2 (proof of Theorem 4.1(i));
  * Theorem 4.1(ii): the range p^{3/4}(log p)^4 <= K <= p^{9/10} is nonempty only for
    log p > 129, i.e. p > 10^56;
  * Remark 7.4(c): Lambda >= 420 log(4 Lambda) holds only for Lambda > 4073, and the example
    q = 10^12 + 39, a = 985496152350226952635200 (left-hand side 5.155..., T^{-gamma_0/4} = 0.985...).
Usage: python3 -I misc_checks.py      (needs mpmath and sympy)
"""
from mpmath import mp, mpf, euler, log, exp, pi, zeta, findroot, quad
from sympy import divisors, isprime
from math import gcd

mp.dps = 40
K0 = euler + log(4 / pi)
c0 = K0 / 2 + log(2) / 6 + 3 / pi**2 * zeta(2, derivative=1)
print("kappa0 =", K0)
print("c0     =", c0)


def I(lam):
    return quad(lambda v: (mp.cosh(v) - mp.cosh(lam * v)) / (mp.sinh(v) * mp.sinh(lam * v)),
                [0, 1, 10, 100 / lam, 2000 / lam]) / pi


for lam in (mpf("0.5"), mpf("0.1"), mpf("0.01"), mpf("0.001")):
    rho = log(1 / lam) + K0 - pi * lam * I(lam)
    print("Lemma 3.2: lambda =", lam, " rho/((7pi^2/72) lambda^2) =", mp.nstr(rho / lam**2 / (7 * pi**2 / 72), 12))
print("kappa0 + 7pi^2/72 =", mp.nstr(K0 + 7 * pi**2 / 72, 12), "(< 2)")

# Theorem 4.1(ii): (log p)^4 <= p^{3/20}  <=>  4 log L <= 0.15 L,  L = log p
L1 = findroot(lambda L: 0.15 * L - 4 * log(L), 130)
print("Theorem 4.1(ii): range nonempty iff log p >=", mp.nstr(L1, 8), " i.e. p >= 10^" + mp.nstr(L1 / log(10), 5))

# Remark 7.4(c)
lam0 = findroot(lambda x: x - 420 * log(4 * x), 4000)
print("Remark 7.4(c): Lambda = 420 log(4 Lambda) at Lambda =", mp.nstr(lam0, 10))
q, a, g0 = 10**12 + 39, 985496152350226952635200, mpf(1) / 20
T = exp(log(mpf(q)) ** g0)
lhs = sum(mpf(1) / d for d in divisors(a) if d > T)
print(f"  q = {q} prime: {isprime(q)}, gcd(a, q) = {gcd(a, q)}, a <= q^2: {a <= q * q}")
print("  T =", mp.nstr(T, 8), " sum_{d | a, d > T} 1/d =", mp.nstr(lhs, 8), " T^(-gamma0/4) =", mp.nstr(T ** (-g0 / 4), 8))
