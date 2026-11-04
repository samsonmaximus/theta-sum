# Numerical checks for theta_sum_conj33.pdf

Run each script from any directory with `python3 -I <script>`. The `.out` files are the saved outputs. The data are in `../../data/`, and the programs that produce them are in `../../code/` (see Section 9 of the paper).

- `numerics_6e6.py`: checks Proposition 1.2 (thresholds 5, 233, 3119, 58013, 869399 and the values S(p_m)), the minima of S(p)/p in Section 9.3, the mean, standard deviation and extremes of X_p and Table 1 in Section 9.4, the values of S(p) in Section 1.1, and Theorem 1.1(a) on p ≤ 6·10⁶. It also checks that `S_p_upto_6e6.txt.gz` holds exactly the odd primes ≤ 6·10⁶, and that `crosscheck_floorsum*.txt` (check (iii) of Section 9.2) agree with it. Needs numpy; runs in about a second. Output: `numerics_6e6.out`.
- `misc_checks.py`: checks the constants κ₀ (2.3) and c₀ (2.4), the bound on ρ(λ) in Lemma 3.2, the threshold p > 10⁵⁶ of Theorem 4.1(ii), and the number 4073 and the example q = 10¹² + 39 of Remark 7.4(c). Needs mpmath and sympy. Output: `misc_checks.out`.
- `fk_divisor_check.py`: checks F_k(p)/k = −(1/π) log k + O(1) for k | p + 1 (Section 1.3). Output: `fk_divisor_check.out`.
- `sp.c` and `compare_recompute.py`: check (ii) of Section 9.2. `sp.c` is a second implementation of Lemma 9.1, and `compare_recompute.py` compares its output with the data file. Build with `gcc -O2 -o sp sp.c`, run `./sp p1 p2 ... > out1.txt`, then `python3 -I compare_recompute.py out1.txt`. Covering all 129703 primes 4·10⁶ < p ≤ 6·10⁶ takes about 20 CPU hours (about 0.65 s per prime).

The identities of Sections 3, 4 and 6 are checked by `../../code/check_identities.py`.
