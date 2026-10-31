# Item 1 of reader_final: with C_BG=1 and N=sqrt(p) (log N = L/2), the Bourgain-Garaev bound
# C (loglog p)^3 (log p) (log N)^{-3/2} N is below N iff L^{1/2} > 2^{3/2} (log L)^3, i.e. L > 8 (log L)^6.
# Find the crossover L.  Smaller N only makes the bound worse, so this is the threshold for "some N <= sqrt p".
from mpmath import mp, mpf, log, findroot
mp.dps = 30
f = lambda L: L - 8*log(L)**6
L0 = findroot(f, mpf('5e8'))
print("crossover log p =", L0)
for L in [mpf('5.1e8'), mpf('5.2e8'), mpf('5.3e8')]:
    print(L, "bound/N =", (log(L)**3*L/(L/2)**mpf(1.5)))
