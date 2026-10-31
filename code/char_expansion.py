"""Character expansion of the limit law (companion paper, Theorem 2).

For odd primitive Dirichlet characters chi of odd conductor f, computes
  W(chi) = i tau(chi) chi(2) (2 - conj chi(2))^2 L(1, conj chi)^2 E(chi) / (4 f phi(f)),
and from it
  * c0(q; r) = c0 + (4/pi) * sum_{f | q'} W(chi) chi(r)   (Theorem J(c); compare Table 2),
  * sigma^2 = (1/pi^2) sum |2 - chi(2)|^4 |L(1,chi)|^4 |E(chi)|^2 / (f phi(f)^2)  (Theorem J(b)),
    summed over conductors f <= F, printing the partial sums.

Usage: python3 -I char_expansion.py c0 q          # c0(q; r) for all r
       python3 -I char_expansion.py sigma F [P]   # partial sums of sigma^2, Euler products over primes < P
Needs numpy, sympy, mpmath.
"""
import itertools, math, sys
import numpy as np
from sympy import factorint, primitive_root, primerange, totient
from mpmath import digamma as _digamma

C0 = 0.2399341036


def primitive_odd_characters(f):
    """Yield the odd primitive characters mod f (f odd) as complex arrays chi[0..f-1]."""
    a = np.arange(f)
    unit = np.gcd(a, f) == 1
    comps = []
    for p, k in factorint(f).items():
        q = p ** k
        g = primitive_root(q)
        n = q // p * (p - 1)
        dlog = np.full(q, -1, dtype=np.int64)
        x = 1
        for e in range(n):
            dlog[x] = e
            x = x * g % q
        comps.append((p, k, n, dlog[a % q]))
    for exps in itertools.product(*[range(c[2]) for c in comps]):
        # primitive iff each local component is primitive
        if not all((e % p != 0) if k >= 2 else (e != 0) for e, (p, k, _, _) in zip(exps, comps)):
            continue
        phase = sum(e * np.where(dl >= 0, dl, 0) / n for e, (_, _, n, dl) in zip(exps, comps))
        chi = np.where(unit, np.exp(2j * np.pi * phase), 0)
        if abs(chi[f - 1] + 1) < 1e-9:      # odd
            yield chi


def W_coefficients(f, primes):
    """List of (chi, W(chi), L(1, conj chi), E(chi)) for the odd primitive chi mod f."""
    psi = np.zeros(f)
    psi[1:] = [float(_digamma(x / f)) for x in range(1, f)]
    phi = int(totient(f))
    lmod = primes % f
    notdiv = (f % primes) != 0
    local = np.prod([1 / (1 - 1.0 / p ** 2) for p in factorint(f)])
    tail = math.exp(1.0 / (primes[-1] * math.log(primes[-1])))   # crude correction for primes beyond the cutoff
    out = []
    for chi in primitive_odd_characters(f):
        L = -(np.conj(chi) * psi).sum() / f                     # L(1, conj chi)
        c2 = chi[2 % f]
        tau = (chi * np.exp(2j * np.pi * np.arange(f) / f)).sum()
        cl = chi[lmod]
        g = np.where(notdiv, (1 - cl) * (1 - np.conj(cl) / primes) / ((1 - 1.0 / primes) * (primes ** 2 - 1.0)), 0)
        E = np.prod(1 + g) * local * tail
        W = 1j * tau * c2 * (2 - np.conj(c2)) ** 2 * L ** 2 * E / (4 * f * phi)
        out.append((chi, W, L, E))
    return out


def c0_table(q, primes):
    qo = q
    while qo % 2 == 0:
        qo //= 2
    ws = [(f, w) for f in range(3, qo + 1, 2) if qo % f == 0 for w in W_coefficients(f, primes)]
    for r in range(1, q):
        if math.gcd(r, q) != 1:
            continue
        s = sum(W * chi[r % f] for f, (chi, W, _, _) in ws)
        print(f"c0({q};{r}) = {C0 + 4 / math.pi * s.real:.6f}")


def sigma_partial_sums(F, primes):
    tot = 0.0
    for f in range(3, F + 1, 2):
        phi = int(totient(f))
        for chi, W, L, E in W_coefficients(f, primes):
            tot += abs(2 - chi[2 % f]) ** 4 * abs(L) ** 4 * abs(E) ** 2 / (f * phi ** 2) / math.pi ** 2
        if f % 200 == 1 or f == F:
            print(f, tot, flush=True)


if __name__ == "__main__":
    mode = sys.argv[1]
    P = int(sys.argv[3]) if len(sys.argv) > 3 else 20000
    primes = np.array(list(primerange(3, P)), dtype=np.int64)
    if mode == "c0":
        c0_table(int(sys.argv[2]), primes)
    else:
        sigma_partial_sums(int(sys.argv[2]), primes)
