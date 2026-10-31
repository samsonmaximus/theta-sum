# Numerical checks for the main paper

Each script checks numerical claims of the paper against the exact values in `../../data/S_p_upto_6e6.txt.gz`; the `.out` files are their outputs.

- `numerics_6e6.py`: Proposition 1.3 and Section 10 (thresholds, minima, Tables 2 and 3). Run it first; it writes a cache used by the next scripts.
- `c0_check_R3002.py`: Section 10.3.
- `misc_checks.py`: the constants c₀, K₀ and other small numerical claims.
- `gauss_form_check.py`: the identity S(p) = 2(N₋ − N₊) of Section 1, for p < 400.
- `fk_divisor_check.py`: the size of F_k(p)/k for k dividing p ± 1 and 2p ± 1.
- `threshold_check.py`: the root of L = 8(log L)⁶ (Section 11).
- `exponents.py`, `dstar_numeric.py`: the exponents and parameter inequalities in the proofs of Theorems C* and D*.
- `sp.c`, `compare_recompute.py`: a separately written implementation of S(p) (same counting formula, Lemma 2.5), compared with the data for all primes 4·10⁶ < p ≤ 6·10⁶ (no discrepancy). Compile with `gcc -O2 -o sp sp.c`.
