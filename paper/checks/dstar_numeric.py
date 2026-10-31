# Numerical check of every "for large L" inequality in the proof of Theorem D*.
# ell = log L, L = log q.  kappa = log T ranges over [(log L)^3, 2L].
# For each ell we test a grid of kappa (log-spaced) and report the failing inequalities.
import mpmath as mp
mp.mp.dps = 60

def check(ell, kappa):
    L = mp.e**ell
    fails = []
    al = 1/ell; be = 1/(2*ell)
    u = mp.floor(kappa/(3*ell))
    if u < 2: return ['u<2']
    if not (u >= ell**2/4): fails.append('u>=ell^2/4')
    if not ((u-1)*be >= 1): fails.append('(u-1)beta>=1')
    if not (kappa/u <= 3.1*ell): fails.append('kappa/u<=3.1ell')
    c = mp.log(2) + kappa/u
    if not (c*u/(u-1) <= 4*ell): fails.append('x_j<=4ell+2L u^-j')
    # compute J exactly from the recursion
    x = 2*L; J = 0
    while x > be*kappa:
        x = mp.log(2) + (kappa + x)/u; J += 1
        if J > 10**6: fails.append('J inf'); break
    Jbound = 1 + mp.log(8*L)/mp.log(u)
    if not (J <= Jbound): fails.append('J<=1+log8L/logu')
    if not (J <= ell/mp.log(ell)): fails.append('J<=ell/logell')
    if not (J*mp.log(2) <= ell): fails.append('Jlog2<=ell')
    if not (ell <= be*kappa/2): fails.append('ell<=beta kappa/2')
    if not (u*mp.log(2) < kappa/2): fails.append('u log2<kappa/2')
    # all x_j <= 2L (needed for log y <= 2L)
    if not (mp.log(2) + (kappa + 2*L)/u <= 2*L): fails.append('x_1<=2L')
    # Rankin: log P(alpha) <= 4 (4L)^alpha (loglog 4L + 1) <= 14 log ell
    if not (4*(4*L)**al*(mp.log(mp.log(4*L)) + 1) <= 14*mp.log(ell)): fails.append('logP<=14loglogL')
    if not (1 <= mp.log(ell)): fails.append('1<=loglogL')
    # y >= 2L^3 :  (3+3beta/2) ell >= log 2 + 3 ell
    if not ((3 + 1.5*be)*ell >= mp.log(2) + 3*ell): fails.append('y>=2L^3')
    # 1+N_y <= y^{1/3}: N_y <= 2L/log y <= 2L/(3 ell); y^{1/3} >= (2 L^3)^{1/3}
    if not (1 + 2*L/(3*ell) <= mp.cbrt(2)*L): fails.append('1+Ny<=y^1/3')
    if not (1 + 2*L/(3*ell) <= L): fails.append('1+Ny<=L')
    # M(y) <= e^gamma (1 + 2L) <= 6L
    if not (mp.e**mp.euler*(1+2*L) <= 6*L): fails.append('M(y)<=6L')
    # G_y bound: u <= N_y case: (kappa/(3ell)) (1 + log4 + ell - log kappa) <= kappa/3
    if not ((kappa/(3*ell))*(1 + mp.log(4) + ell - mp.log(kappa)) <= kappa/3): fails.append('G<=e^{kappa/3}')
    if not (4*L/kappa >= 1): fails.append('4L/kappa>=1')
    # u > N_y case: 2^{N_y} < 2^u <= e^{kappa/3}
    if not (u*mp.log(2) <= kappa/3): fails.append('2^u<=e^{kappa/3}')
    # E_1: 12L * 2.7 * L * e^{kappa/3} * 2^J e^{-kappa} <= exp(-2kappa/3 + 4 ell)
    lhs = mp.log(12*2.7) + 2*ell + J*mp.log(2) - 2*kappa/3
    if not (lhs <= -2*kappa/3 + 4*ell): fails.append('E1')
    # E_1 <= E_b
    if not (-2*kappa/3 + 4*ell <= -kappa/(2*ell) + 15*mp.log(ell)): fails.append('E1<=Eb')
    # base case: (1-al)be*kappa - al*kappa + al*J*log2 + logP <= -be*kappa + 1 + 14 log ell
    logP = 4*(4*L)**al*(mp.log(mp.log(4*L)) + 1)
    if not ((1-al)*be*kappa - al*kappa + al*J*mp.log(2) + logP <= -be*kappa + 15*mp.log(ell)): fails.append('base')
    # conclusion: log(2(J+1)) + J log(6L) - kappa/(2ell) + 15 log ell <= -kappa/(4 ell)
    if not (mp.log(2*(J+1)) + J*mp.log(6*L) - kappa/(2*ell) + 15*mp.log(ell) <= -kappa/(4*ell)): fails.append('final')
    return fails

def kappas(ell):
    L = mp.e**ell
    lo, hi = ell**3, 2*L
    pts = [lo, lo*1.01, lo*2, lo*10]
    n = 40
    for i in range(n+1):
        pts.append(mp.e**(mp.log(lo) + (mp.log(hi)-mp.log(lo))*i/n))
    return [k for k in pts if lo <= k <= hi]

def ok(ell):
    bad = set()
    for k in kappas(ell):
        bad |= set(check(ell, k))
    return bad

for ell in [10, 20, 30, 40, 50, 60, 80, 100, 200, 500, 1000, 10**4]:
    print(ell, sorted(ok(mp.mpf(ell))))

# smallest integer ell (>= 10) from which on all checks pass (scan)
first = None
for ell in range(10, 400):
    if not ok(mp.mpf(ell)):
        if first is None: first = ell
    else:
        first = None
print("all inequalities hold for every tested ell >=", first, "(scan up to 400; then spot checks above)")
