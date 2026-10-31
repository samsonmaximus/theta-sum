# Symbolic checks of the exponents in Theorem C*, the optimality of K_*, and Theorem C-flat.
import sympy as sp

L, l, A, a, b, th, de, g = sp.symbols('L ell A a b theta delta gamma', positive=True)  # l = log L

def lpow(expr):
    """return (exponent of L, exponent of log L) of a monomial c*L^x*l^y"""
    expr = sp.powsimp(sp.expand_power_base(expr, force=True), force=True)
    return (sp.simplify(sp.diff(sp.log(expr).expand(force=True), L) * L),
            sp.simplify(sp.diff(sp.log(expr).expand(force=True), l) * l))

print("=== Theorem C*: T = exp((log L)^3), K_* = exp(A L^{2/3} (log L)^{8/3}) ===")
logN = l**3                       # log N = (log L)^3 + O(log L)
logKs = A*L**sp.Rational(2,3)*l**sp.Rational(8,3)
logH = 2*l                        # H = ceil(L^2)
below = logN*logKs/(2*sp.pi)
above = logN*logH*l**3*L/sp.sqrt(logKs)    # (1+log N)(1+log H)(log L)^3 L (log K_*)^{-1/2}
print("heads below K_*  :", lpow(below))
print("heads above K_*  :", lpow(above))
assert lpow(below) == (sp.Rational(2,3), sp.Rational(17,3))
assert lpow(above) == (sp.Rational(2,3), sp.Rational(17,3))
# exponent 17/3 = 3 (from log N) + 8/3 (from log K_*)
assert sp.Rational(3) + sp.Rational(8,3) == sp.Rational(17,3)

print("=== optimality of the choice of K_* = exp(A L^a (log L)^b) with a=2/3 forced, b>=8/3 forced ===")
logKs_g = A*L**a*l**b
below_g = lpow(logN*logKs_g)
above_g = lpow(logN*logH*l**3*L/sp.sqrt(logKs_g))
print("below:", below_g, " above:", above_g)
bsol = sp.solve(sp.Eq(below_g[1].subs(a, sp.Rational(2,3)), above_g[1].subs(a, sp.Rational(2,3))), b)
print("log-power balance at b =", bsol)
asol = sp.solve(sp.Eq(below_g[0], above_g[0]), a)
print("L-power balance at a =", asol)
assert bsol == [sp.Rational(8,3)] and asol == [sp.Rational(2,3)]

print("=== constants in the heads above K_* (Theorem C*) ===")
# per block: (1+log N)(2/H + 10(1+log H) M_K/K), M_K/K <= 16 sqrt2 C_BG (loglog p)^3 (log p) (log K)^{-3/2}
# sum_j (log K_j)^{-3/2} <= 4 (log K_*)^{-1/2};  1 + log H <= 3 log L
CBG = sp.Symbol('C_BG', positive=True)
const = 10*16*sp.sqrt(2)*CBG*4*3
print("constant in front of (log N)(log L)^4 L (log K_*)^{-1/2}:", const, "=", sp.nsimplify(const/(sp.sqrt(2)*CBG)), "sqrt2 C_BG")
assert sp.simplify(const - 1920*sp.sqrt(2)*CBG) == 0
# check sum_j (log K_* + j log 2)^{-3/2} <= (log K_*)^{-3/2} + int_0^oo = (log K_*)^{-3/2} + 2/(log2 (log K_*)^{1/2}) <= 4 (log K_*)^{-1/2}
x, t = sp.symbols('x t', positive=True)
I = sp.integrate((x + t*sp.log(2))**sp.Rational(-3,2), (t, 0, sp.oo))
print("integral =", sp.simplify(I), "; 2/log2 =", sp.N(2/sp.log(2)))
assert sp.N(2/sp.log(2)) + 1 < 4

print("=== Theorem C-flat: K_* = exp(2 L^theta), log T = (log L)^3, saving (log p)^{-delta} ===")
logKs_f = 2*L**th
below_f = lpow(logN*logKs_f)
above_f = lpow(logN*logH*L*L**(-de))   # (1+log N)(1+log H)(L+1) blocks * L^{-delta}
print("heads below:", below_f, " heads above:", above_f)
assert below_f == (th, 3) and above_f == (1 - de, 4)

print("=== B-G => (HKS) with theta = 9/10, delta = 1/4 ===")
# log N >= L^{9/10}: (log L)^3 L (log N)^{-3/2} <= (log L)^3 L^{1-27/20} = (log L)^3 L^{-7/20} <= L^{-1/4} once (log L)^3 <= L^{1/10}
assert 1 - sp.Rational(9,10)*sp.Rational(3,2) == sp.Rational(-7,20)
assert sp.Rational(-7,20) + sp.Rational(1,10) == sp.Rational(-1,4)
# (1/2) L^{9/10} >= A_BG L^{2/3} (log L)^{8/3} for large L: exponent 9/10 > 2/3
assert sp.Rational(9,10) > sp.Rational(2,3)
print("all symbolic checks passed")
