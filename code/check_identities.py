"""Independent numerical checks of the exact identities in theta_sum_v3.pdf.

Each check prints the largest discrepancy found. Run: python3 -I check_identities.py
Requires mpmath.
"""
import math, random
from fractions import Fraction
import mpmath as mp

mp.mp.dps = 40
pi = mp.pi

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0: return False
        d += 2
    return True

def S_brute(p):
    return sum((-1) ** (j + 1 + (h * j) // p) for h in range(1, p) for j in range(1, p))

def C(m, k):   # C_m(k) = sum_{0<a<m, a odd} cot(pi k a / 2m)
    return mp.fsum(mp.cot(pi * k * a / (2 * m)) for a in range(1, m, 2))

def F(k, n):   # F_k(n) = sum_{t=1}^{(k-1)/2} tan(pi n t / k)
    return mp.fsum(mp.tan(pi * n * t / k) for t in range(1, (k - 1) // 2 + 1))

def I(lam):
    lam = mp.mpf(lam)
    f = lambda v: (mp.cosh(v) - mp.cosh(lam * v)) / (mp.sinh(v) * mp.sinh(lam * v)) if v != 0 else (1 - lam**2) / (2 * lam)
    s = 1 / lam
    pts = [0, 1, 10, 50] + [x for x in (s, 10 * s, 60 * s) if x > 50] + [mp.inf]
    pts = sorted(set(pts))
    return mp.quad(f, pts) / pi

K0 = mp.euler + mp.log(4 / pi)
c0 = K0 / 2 + mp.log(2) / 6 + 3 / pi**2 * mp.diff(mp.zeta, 2)

def report(name, err, tol):
    status = "OK" if err < tol else "FAIL"
    print(f"[{status}] {name}: max discrepancy {mp.nstr(err, 3)} (tolerance {tol})")

def main():
    random.seed(1)
    print("K0 =", mp.nstr(K0, 20), "  c0 =", mp.nstr(c0, 30))

    # Lemma 4.1 (reciprocity): C_m(k) = (m/k) F_k(m) + I(k/m), coprime odd m, k
    err = 0
    pairs = [(m, k) for m in range(3, 60, 2) for k in range(1, 60, 2) if math.gcd(m, k) == 1]
    for m, k in random.sample(pairs, 40):
        err = max(err, abs(C(m, k) - (mp.mpf(m) / k * (F(k, m) if k > 1 else 0) + I(mp.mpf(k) / m))))
    report("Lemma 4.1 reciprocity", err, 1e-20)

    # Lemma 4.2: I(1/lam) = -lam I(lam), and 0 <= rho(lam) <= 7 pi^2 lam^2 / 72
    err, worst = 0, 0
    for lam in [mp.mpf(1) / 7, mp.mpf(1) / 3, mp.mpf('0.5'), mp.mpf('0.9'), mp.mpf('0.01')]:
        err = max(err, abs(I(1 / lam) + lam * I(lam)))
        rho = mp.log(1 / lam) + K0 - pi * lam * I(lam)
        assert rho >= 0, lam
        worst = max(worst, rho / (7 * pi**2 * lam**2 / 72))
    report("Lemma 4.2 I(1/l) = -l I(l)", err, 1e-20)
    print(f"      Lemma 4.2 rho/(7pi^2 l^2/72) max = {mp.nstr(worst, 6)} (must be <= 1)")

    # Theorem B(i): S(p) = Psi(p) + Phi(p) exactly; Table 1 second-order term
    for p in [101, 211, 401]:
        S = S_brute(p)
        Psi = 2 / mp.mpf(p) * mp.fsum(mp.cot(pi * k / (2 * p)) * I(mp.mpf(k) / p) for k in range(1, p, 2))
        Phi = 2 * mp.fsum(mp.cot(pi * k / (2 * p)) * F(k, p) / k for k in range(3, p, 2))
        report(f"Theorem B(i) S(p)=Psi+Phi, p={p}", abs(S - Psi - Phi), 1e-20)
        print(f"      Psi - (p/2)log p - c0 p = {mp.nstr(Psi - p * mp.log(p) / 2 - c0 * p, 6)}")

    # Lemma 6.1(b): F_k(p) = -sum_{n odd < k} cot(pi n/2k) sgn(1/2 - {n theta_k}), theta_k = (2p)^{-1} mod k / k
    err = 0
    for p in [101, 1009, 10007]:
        for k in random.sample([k for k in range(3, min(p, 400), 2)], 25):
            if math.gcd(k, p) != 1: continue
            u = pow(2 * p, -1, k)
            g = lambda y: 1 if (y % 1) < Fraction(1, 2) else -1
            rhs = -mp.fsum(mp.cot(pi * n / (2 * k)) * g(Fraction(n * u, k)) for n in range(1, k, 2))
            err = max(err, abs(F(k, p) - rhs))
    report("Lemma 6.1(b) sign form", err, 1e-25)

    # Lemma 2.6 (Gauss-lemma form) and Lemma 2.7 (third formula, Dedekind sums)
    def saw(x):
        x = Fraction(x); fl = x.numerator // x.denominator
        return Fraction(0) if x == fl else x - fl - Fraction(1, 2)
    def ded(x, p):
        return sum(saw(Fraction(c, p)) * saw(Fraction(x * c, p)) for c in range(1, p))
    err26 = err27 = 0
    for p in [p for p in range(3, 110) if is_prime(p)]:
        S = S_brute(p); H = (p - 1) // 2
        Np = sum(1 for a in range(1, H + 1) for b in range(1, H + 1) if (2 * a * b) % p <= H)
        err26 = max(err26, abs(S - (2 * H * H - 4 * Np)))
        if p >= 5:
            inv2 = (p + 1) // 2
            v = 4 * sum(saw(Fraction(a, p)) * (-4 * ded(4 * a, p) + 12 * ded(2 * a, p) + 2 * ded(inv2 * a, p) - 9 * ded(a, p)) for a in range(1, p))
            err27 = max(err27, abs(S - v))
    report("Lemma 2.6 Gauss-lemma form, p<110", err26, 0.5)
    report("Lemma 2.7 Dedekind-sum form, 5<=p<110", err27, 0.5)

    # Corollary 4.3(b): |F_k(r)| <= F_k(1) <= (k/pi)(log k + K0)
    worst = 0
    for k in range(3, 120, 2):
        F1 = F(k, 1)
        assert F1 <= k / pi * (mp.log(k) + K0)
        for r in range(1, k):
            worst = max(worst, abs(F(k, r)) - F1)
    report("Corollary 4.3(b) |F_k(r)| <= F_k(1), k<120", max(worst, 0), 1e-25)

    # Lemma 5.2 (Weil): |sum_{k in J, k odd} e(c kbar/2p)| <= 2 sqrt(p) (log p + 2) for all intervals J, p∤c.
    # The max over intervals is the diameter of the prefix-sum path; we bound it above via widths
    # in 90 directions (diameter <= max width / cos(pi/180)).
    import numpy as np
    for p in [211, 1009, 4001]:
        ks = np.arange(1, p, 2)
        kbar = np.array([pow(int(k), -1, 2 * p) for k in ks])
        dirs = np.exp(-1j * np.pi * np.arange(90) / 90)
        worst = 0.0
        for c in range(1, 2 * p):
            if c % p == 0: continue
            pref = np.concatenate([[0], np.cumsum(np.exp(2j * np.pi * c * kbar / (2 * p)))])
            proj = np.real(np.outer(dirs, pref))
            worst = max(worst, float(np.max(proj.max(axis=1) - proj.min(axis=1))) / np.cos(np.pi / 180))
        bound = 2 * math.sqrt(p) * (math.log(p) + 2)
        print(f"[{'OK' if worst <= bound else 'FAIL'}] Lemma 5.2 p={p}: max interval sum <= {worst:.2f}, bound {bound:.2f}")

if __name__ == "__main__":
    main()
