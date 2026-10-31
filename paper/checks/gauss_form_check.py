#!/usr/bin/env python3
"""D6: check Lemma 2.6 (Gauss-lemma form) against the definition of S(p):
S(p) = 2H^2 - 4N_+, H = (p-1)/2, N_+ = #{(a,b) in [1,H]^2 : (2ab mod p) < p/2},
so S(p) > 0 iff fewer than half of the H^2 products 2ab mod p lie in (0, p/2);
also S(p) = 2(N_- - N_+), and N_-/H^2 - 1/2 = S(p)/(4H^2)."""
import math

def primes(n):
    s = [True] * (n + 1); s[0] = s[1] = False
    for i in range(2, int(n ** .5) + 1):
        if s[i]:
            s[i * i::i] = [False] * len(s[i * i::i])
    return [i for i in range(3, n + 1) if s[i]]

def S_def(p):
    return sum((-1) ** (j + 1 + (h * j) // p) for h in range(1, p) for j in range(1, p))

for p in primes(400):
    H = (p - 1) // 2
    Np = sum(1 for a in range(1, H + 1) for b in range(1, H + 1) if (2 * a * b) % p < p / 2)
    Nm = H * H - Np
    s = S_def(p)
    assert s == 2 * H * H - 4 * Np == 2 * (Nm - Np), p
print("Lemma 2.6 identity S(p) = 2H^2 - 4N_+ = 2(N_- - N_+) verified for all odd primes p < 400")
for p in (101, 233, 1009, 3119):
    H = (p - 1) // 2
    Np = sum(1 for a in range(1, H + 1) for b in range(1, H + 1) if (2 * a * b) % p < p / 2)
    s = 2 * H * H - 4 * Np
    print(f"p={p}: H^2={H*H}, N_+={Np}, N_-={H*H-Np}, S={s}, excess N_- - N_+ = {H*H-2*Np},"
          f" N_+/H^2 = {Np/(H*H):.5f}, (log p)/(2p) = {math.log(p)/(2*p):.5f}")
