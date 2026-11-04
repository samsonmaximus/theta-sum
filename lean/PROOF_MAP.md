# Proof map: paper → Lean

Section, theorem, lemma and equation numbers below refer to [`paper/theta_sum_conj33.pdf`](../paper/theta_sum_conj33.pdf). Its Appendix A and the table in its Section 8.3 are the paper's own summary of the formalization; this file gives the details.

Paths are relative to `lean/`. "ThetaSum/X" means `ThetaSum/X.lean`, and "Upper/X" means `Upper/X.lean`. Unqualified names in the ThetaSum files lie in the namespace `ThetaSum`; names in Upper/Cot, Upper/Tangent and Upper/Main lie in `Arxiv.«2501.03234»`.

**Status values used in the tables:**
- **exact**: the Lean statement is the paper's statement, up to notation.
- **modified**: the Lean statement differs, and the difference is stated.
- **not formalized**: nothing in Lean corresponds.

Every Lean declaration named below is free of `sorry` and `native_decide`. Its `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound` (`ThetaSum/MainTheorems.lean`).

`S'` and `S` are the formal-conjectures definitions, copied verbatim into `Upper/Defs` and `ThetaSum/Hypotheses`. `ThetaSum.S_bridge` proves the two copies equal by `rfl`.

**Notation.** The Lean names differ from the paper's symbols in a few places: U(a) is `T` (Upper/Cot) or `Tq` (ThetaSum/Compute); the sum T(p) of Theorem 4.1 is `TheoremB.Phi`; κ₀ is `ThetaSum.Kzero`; W(x, y) of Lemma 9.1 is `Ffl`; sq is `gsq`; R_K(p) is `RsumK K p`; the cutoff K_W is `KW34 p` = ⌊p^{3/4}(log p)⁴⌋.

## Known differences, in brief

The paper (Appendix A and Section 8.3) lists these differences, and the tables below give the details:
- Some constants differ.
- Lemma 6.6 (generic θ) is formalized in an elementary version that does not use Vaaler's lemma.
- The reciprocity law (Lemma 3.1) is proved without contour integration.
- The Lean assembly proves S(p)/p → ∞, that is S(p) = (p/2)log p + o(p log p), rather than the explicit exponent 19/20 of Theorem 1.1(b).
- K_W is rounded down to ⌊p^{3/4}(log p)⁴⌋, which can lie just below the range of Theorem 4.1(ii) as stated; the two versions of R_K(p) differ by at most one term, of size O(p log p/K_W).
- The parameter N of Section 8 is ⌈TM⌉ in Lean, in place of ⌈TM(2 + log M)⌉.

## Section 1: introduction and results

| Result | Lean declaration(s) | Status | Notes |
|---|---|---|---|
| Conjecture 3.3: C₁k < S(k) < C₂k^{1+ε} for large primes k | `conjecture_3_3_of_BG` (ThetaSum/Headline); `conjecture_3_3_of_HKS` (ThetaSum/WeakHyp) | modified | Assumes (HBG), which is Lemma 5.1, or the weaker (HKS). This is the paper's dependence on Lemma 5.1, made explicit. Also `conjecture_3_3_34` (ThetaSum/Conjecture33), which takes the decomposition of Theorem 4.1(ii) as a second argument; `conjecture_3_3_of_BG` supplies it by `hBweak34`. |
| Theorem 1.1(a): \|S(p)\| ≤ (2/π²)p(log p + 2)² | `S_abs_le_cot`, `theorem_A` (Upper/Cot) | exact | |
| Theorem 1.1(b): S(p) = (p/2)log p + O(p(log p)^{19/20}) | `lower_half_HBweak34_HBG` (ThetaSum/LowerHalfFinal) | modified | Assumes (HBG). Proves n·p < S(p) for all large primes p, for every n ∈ ℕ, that is S(p)/p → ∞. The exponent 19/20 is not formalized. |
| Consequences of Theorem 1.1: S(p) > Bp for each fixed B; Conjectures 1.1, 3.1, 3.2 for large p | `lower_half_HBweak34_HBG`; `conjecture_1_1_eventually_of_BG`, `conjecture_3_1_eventually_of_BG`, `conjecture_3_2_eventually_of_BG` (ThetaSum/Headline); `Arxiv.«2501.03234».conjecture_4_4_of_BG` (ThetaSum/FormalConjectures) | exact | Conditional on (HBG), as in the paper. |
| Proposition 1.2: thresholds 0, p, 2p, 3p, 4p, 5p for odd primes p ≤ 6·10⁶ | `S_pos_upto`, `S_gt_two_mul_upto`, `S_gt_three_mul_upto`, `S_233`, `S_3119` (ThetaSum/FiniteRange); `S_gt_self_upto` (ThetaSum/FormalConjectures); `Arxiv.«2501.03234».S_fst_10` | modified | Proved for p ≤ 2·10⁴ only, and only for the thresholds 0, p (p > 5), 2p (p > 233), 3p (p > 3119). The checks are kernel-evaluated (`decide +kernel`). Sharpness: S(5) = 4 (in `S_fst_10`), S(233) = 440, S(3119) = 9194. The 4p and 5p thresholds are not formalized. |
| Theorem 1.3: large divisors of the terms of a progression, T = exp((log q)^{γ₀}) | `theorem_D` (ThetaSum/Asymptotics) | exact | The proof differs in places (Section 7 below). L₀(γ₀) is not explicit, as in the paper. |

## Section 2: notation and the cotangent formula

| Result | Lean declaration(s) | Status | Notes |
|---|---|---|---|
| (2.4): c₀ = κ₀/2 + (log 2)/6 + (3/π²)ζ′(2), with κ₀ = γ + log(4/π) (2.3) | `c0`, `Kzero` (ThetaSum/ConstantC0); `c0_closed_form` (ThetaSum/ZetaClosed) | exact | Lean defines c₀ = κ₀/2 − (4/π²)Σ_{k odd} (log k)/k² and proves (2.4). Supporting lemmas: `SLodd_closed_form`, `deriv_zeta_two`. |
| Lemma 2.1(a): S(p) = Σ_{a,b} (−1)^{⌊ab/p⌋} | `S_eq_sumT`, `S'_reflect` (ThetaSum/Compute) | exact | In the form S(p) = Σ_a U(a). `S'_reflect` is S(p − a, p) = U(a), from the proof. |
| Lemma 2.1(b): U(a) = 0 for even a; S(p) = Σ_{a odd} U(a) | `Tq_even` (ThetaSum/Compute); `T_even`, `S_eq_sum_T` (Upper/Cot) | exact | |
| Lemma 2.2: dual formula for U(a); (2.5) | `T_dual`, `S_dual` (Upper/Cot) | exact | `T_dual` holds for every odd p. (2.5) is `S_dual`. |
| Lemma 2.3: sign form of C_p(k); \|C_p(k)\| ≤ C_p(1) | `Cp_sign_form`, `Cp_abs_le` (Upper/Cot) | exact | |
| Lemma 2.4: C_m(1) ≤ (m/π)(log m + 2) | `Cp_one_le` (Upper/Cot) | exact | Stated for every odd m. |
| Proposition 2.5: \|S(p)\| ≤ (2/p)C_p(1)² ≤ (2/π²)p(log p + 2)² | `theorem_A` (Upper/Cot) | exact | |
| Corollary 2.6: S(p) < C₂p^{1+ε} for large p | `ThetaSum.conjecture_3_3_upper` (ThetaSum/Conjecture33); `Arxiv.«2501.03234».conjecture_3_3_upper` (Upper/Main) | exact | Unconditional. The Lean proof uses the elementary bound \|S(p)\| ≤ 5p·H_p² (`S_abs_le`, `S_abs_le_log`, Upper/Main) in place of Proposition 2.5. |

## Section 3: a reciprocity law for half-range cotangent sums

| Result | Lean declaration(s) | Status | Notes |
|---|---|---|---|
| Lemma 3.1: C_m(k) = (m/k)F_k(m) + I(k/m) | `Recip.reciprocity` (Upper/Reciprocity) | exact | The proof avoids contour integration: a polynomial identity at roots of unity (`Dpoly_eq_zero`) and termwise integration (`integral_Jint`). |
| Lemma 3.2: πλI(λ) = log(1/λ) + κ₀ − ρ(λ) with 0 ≤ ρ ≤ 7π²λ²/72; I(1/λ) = −λI(λ) | `TheoremB.I_asymp_K0` (ThetaSum/ConstantC0); `TheoremB.I_asymp` (Upper/TheoremB); `Recip.Ifun_inv`, `Recip.Ifun_pos` (Upper/Reciprocity) | modified | Weak form: \|πλI(λ) − log(1/λ) − κ₀\| ≤ λ(4 log(1/λ) + 91) on (0, 1]. Lean derives it in the reverse direction, from I(1/m) = C_m(1), the asymptotics of C_m(1) (`TheoremB.Cp_one_asymp`: \|C_m(1) − (m/π)(log m + κ₀)\| ≤ 9 for odd m ≥ 5) and the monotonicity of I. The identity I(1/λ) = −λI(λ) is exact. This weak form suffices for the constant c₀. |
| Corollary 3.3(a): F_m(1) = C_m(1) = I(1/m) | `Fsum_one_eq_Cp` (Upper/Tangent); `TheoremB.Ifun_inv_nat` (Upper/TheoremB) | exact | `Cp_eq_Fsum` (Upper/Tangent) proves C_m(k) = F_m(k) for all odd m, k. |
| Corollary 3.3(b): \|F_k(r)\| ≤ F_k(1) ≤ (k/π)(log k + 2) | `Fsum_abs_le` (Upper/Tangent); `TheoremB.Fsum_abs_bound` (Upper/TheoremB) | exact | |
| Corollary 3.3(c): \|I(λ)\| ≤ (1/(πλ))(log(1/λ) + 2) on (0, 1] | `TheoremB.I_asymp` (Upper/TheoremB) | modified | \|πλI(λ) − log(1/λ)\| ≤ 12 on (0, 1]. |

## Section 4: the exact decomposition

| Result | Lean declaration(s) | Status | Notes |
|---|---|---|---|
| Theorem 4.1(i), identity S(p) = Ψ(p) + T(p) | `TheoremB.S_eq_Psi_Phi` (Upper/TheoremB) | exact | T(p) is `TheoremB.Phi`. |
| Theorem 4.1(i), Ψ(p) = (p/2)log p + c₀p + O(1) | `TheoremB.Psi_asymp` (ThetaSum/ConstantC0); `TheoremB.Psi_bound` (Upper/TheoremB) | modified | `Psi_asymp`: error at most εp for all large odd p, that is o(p), in place of O(1). `Psi_bound`: Ψ(p) = (p/2)log p + O(p). |
| Theorem 4.1(ii): S(p) = (p/2)log p + c₀p + (4p/π)R_K(p) + O(p/log p) for p^{3/4}(log p)⁴ ≤ K ≤ p^{9/10} | `theorem_B_c0` (ThetaSum/ConstantC0); `TheoremB.HBweak34_of_HK34` (Upper/TheoremB), `hBweak34` (ThetaSum/Headline) | modified | Unconditional. Only K = ⌊p^{3/4}(log p)⁴⌋ (rounded down; see the list of differences above). `theorem_B_c0` has the constant c₀ and error at most εp for all large p. `hBweak34` has an unspecified constant c and error O(p); this is the form the proof of Conjecture 3.3 uses. The variant with the sum over all odd k < p is not formalized. |
| Lemma 4.2: \|Kl(b, ν; p)\| ≤ (3p²(p − 2))^{1/4} ≤ 2p^{3/4} | `kl_four_le`, `kloosterman_bound`, `hK34` (ThetaSum/Kloosterman) | modified | Fourth-moment proof, as in the paper, with \|Kl\|⁴ ≤ 3p³ in place of 3p²(p − 2). The final bound 2p^{3/4} is the same. `HK34_bridge` (ThetaSum/Headline) translates it to `TheoremB.HK34`. |
| Lemma 4.3: \|Σ_{k∈J, k odd} e(c k̄/2p)\| ≤ 2p^{3/4}(log p + 2) | `TheoremB.weil_kbar` (Upper/TheoremB) | modified | Proved for any uniform bound B on the complete Kloosterman sums (`KlBound p B`), with the bound B(3 + 2 log p). It is used with B = 2p^{3/4} (`KlBound_of_HK34`). |
| Lemma 4.4: \|Σ_{k∈J, k odd} C_p(k)\| ≤ (4/π²)p^{7/4}(log p + 2)³ | `TheoremB.sum_Cp_interval` (Upper/TheoremB) | modified | Same remark: the bound is (1/p)C_p(1)(2p(1 + log p)·B(3 + 2 log p) + p). |
| Remark 4.5 (Weil's bound gives the cutoff √p(log p)⁴) | `TheoremB.HW`, `TheoremB.KlBound_of_HW` (Upper/TheoremB) | not formalized | Weil's bound is stated as a `Prop` (`HW`) and is neither proved nor used by any headline theorem. |

## Section 5: short Kloosterman sums

| Result | Lean declaration(s) | Status | Notes |
|---|---|---|---|
| Lemma 5.1 (input from Bourgain–Garaev) | hypothesis `HBG` (ThetaSum/Hypotheses); the weaker `HKS` (ThetaSum/WeakHyp) | not formalized | (HBG) is exactly the statement of Lemma 5.1, in the same range log N ≥ ½(log p)^{9/10}. It is an argument of the headline theorem. `HKS_of_HBG` derives (HKS). See [`HYPOTHESES.md`](HYPOTHESES.md). |
| Lemma 5.2: reduction of M_K to four initial sums Σ_{n≤N′} e(bn\*/p) | `odd_interval_sum`, `odd_interval_bound` (ThetaSum/Kloost) | modified | Stated for the sums of e(c(2k)^{−1}/p) over odd k in an interval, with the initial sums at b = c/2 and b = c/4. These are the sums of the paper, written with the inverse of 2k modulo p (`bridge`, ThetaSum/Bridge). |
| Corollary 5.3: M_K/K ≤ 16√2·C_BG(log log p)³(log p)(log K)^{−3/2} | `block_kloost` (ThetaSum/HeadsBG); `block_kloost_KS` (ThetaSum/WeakHyp) from (HKS) | modified | For a block [a, x) ⊆ [a, 2a] with log(a/3) ≥ ½(log p)^{9/10}: bound 4·C(log log p)³(log p)(log(a/3))^{−3/2}·2a. Constants differ. |

## Section 6: heads and tails of the tangent sums

| Result | Lean declaration(s) | Status | Notes |
|---|---|---|---|
| Lemma 6.1(a), (b): F_k(p) = −Σ_{n odd} cot(πn/2k)·sq(nθ_k) | `sign_form` (ThetaSum/SignForm); `Fsum_split` (ThetaSum/Decomp) | exact | (a) and (b) in combined form, with θ_k = u/k, k ∣ 2pu − 1. |
| Lemma 6.1(c): θ_k in terms of the inverse of k modulo 2p | `bridge` (ThetaSum/Bridge) | modified | In the form sq(nu/k) = sq(nw/p), where w is the inverse of 2k modulo p. |
| (6.1): the split Φ_k = Φ_k^{≤N} + Φ_k^{>N} | `Fsum_split`, `headTh` (ThetaSum/Decomp); `phiTail` (ThetaSum/TailsAll) | exact | |
| (6.2): \|Φ_k^{≤N}\| ≤ (2/π)(1 + ½ log N) | `headTh_trivial` (ThetaSum/Decomp) | modified | Bound (2/π)(2 + log N). |
| Lemma 6.2 (Vaaler) | `Vaaler.vaaler_lemma`, `Vaaler.vaaler_real` (ThetaSum/Vaaler); `hV_holds` (ThetaSum/HVProof) | exact | A finite proof, with no Fourier analysis on ℝ. `hV_holds` proves the real form (HV) that the later files use. |
| Lemma 6.3 (square wave) | `square_wave` (ThetaSum/SquareWave) | modified | Real (sine/cosine) form: \|b_h\| ≤ 4/(πh), and the majorant is (2/(H + 1))(1 + Σ_h d_h cos(2πhy)) with 0 ≤ d_h ≤ 2. |
| Lemma 6.4 (heads) | `block_heads` (ThetaSum/Heads); `R_bound` (ThetaSum/RBound) | modified | `block_heads` bounds the heads over a block in terms of any bound for the Kloosterman sums over the block (supplied by `block_kloost`). Constants differ. Abel summation uses `abel_antitone` and `weight_antitone` (ThetaSum/Weights). |
| Lemma 6.5(a): \|Φ_k^{>N}\| ≤ (π/2)D_k log(k/N) | `tail_partial_summation` (ThetaSum/TailBound) | exact | Stated for any coefficients whose partial sums are at most Dt. |
| Lemma 6.5(b): \|Φ_k^{>N}\| ≤ (1/π)log k | `tail_trivial` (ThetaSum/TailBound); `phiTail_trivial` (ThetaSum/TailsAll) | exact | |
| Lemma 6.6 (generic θ): D_k ≤ 1/M + (2 + log M)/(ηN) | `generic_bound`, `generic_bound_div` (ThetaSum/Generic) | modified | Elementary version without Vaaler's lemma (Dirichlet's approximation theorem and a grid count). Bound \|Σ_{j<J} sq((n₀ + 2j)θ)\| ≤ 6J/M + 1/η, hence D_k ≤ 3/M + 1/(ηN). No hypothesis nθ ∉ ½ℤ (`gsq` takes the value −1 at the jumps). |
| Lemma 6.7 (witnesses) | `witness` (ThetaSum/Tails) | exact | |

## Section 7: large divisors of the terms of an arithmetic progression

| Result | Lean declaration(s) | Status | Notes |
|---|---|---|---|
| Lemma 7.1 (Rankin), with log P(α) ≤ 4(4L)^α(log log(4L) + 1) | `rankin_delta`, `sum_primeFactors_rpow_le` (ThetaSum/Rankin) | modified | log P(α) ≤ 4L^α(1/α + 2), from splitting the prime factors at L. θ(ℓ) ≥ ℓ/2 is not used. |
| Lemma 7.2 (one step) | `one_step`, `one_step_le`, `one_step_euler`, `sub_progression` (ThetaSum/OneStep); `one_step_harmonic` (ThetaSum/Counting) | modified | `one_step_euler` has the paper's M(y). The proof of Theorem 1.3 uses `one_step_harmonic`, with the harmonic bound 1 + log R in place of Mertens' bound for M(y). The sum over j ≥ 0 is truncated at a J with X ≤ 2^J T′R. |
| Lemma 7.3: G_y(2^jZ) ≤ (1 + N_y)^{1+j log 2/log y}G_y(Z) | `G_le_rpow`, `dyadic_sum_le` (ThetaSum/Counting) | modified | Replaced by G_y(Z) ≤ Z^{log(N_y+1)/log y} and Σ_{j<J} 2^{−j}G_y(2^{j+1}P) ≤ 4(2P)^θ for θ ≤ ½. |
| Section 7.3: proof of Theorem 1.3 | `base_level`, `rec_step` (ThetaSum/Recursion); ThetaSum/TheoremD; `theorem_D` (ThetaSum/Asymptotics) | modified | Same induction. Parameters: β = γ₀/16 (paper γ₀/8), u = κ/(4 log(L + 1)) (paper ⌊κ/(3 log L)⌋), J = ⌈1/γ₀⌉ (paper j₀ = ⌈1/γ₀⌉ + 1), and explicit majorants x_j of the log-lengths. |
| Remark 7.4 | not formalized | — | |

## Section 8: proof of Theorem 1.1

The Lean assembly is `lower_half_gen` (ThetaSum/LowerHalf) with θ = 3/4, followed by `lower_half34` and `lower_half_HBweak34_HBG` (ThetaSum/LowerHalfFinal). Parameters, with L = log p: T = exp(L^{1/20}), η = 1/T, M = H = ⌈L²⌉, N = ⌈TM⌉, K_* = ⌈exp(L^{9/10})⌉, J = ⌈2L⌉ dyadic blocks, K_W = ⌊p^{3/4}L⁴⌋.

| Step | Lean declaration(s) | Status | Notes |
|---|---|---|---|
| Step 2: the reduction to Σ = R_{K_W}(p) | `hBweak34` (ThetaSum/Headline); `HB34_of_HBweak34` (ThetaSum/Hypotheses) | modified | Uses the O(p) form of Theorem 4.1(ii); only a lower bound for S(p) is needed. |
| Step 3: heads with k < K_* | `headTh_trivial` (ThetaSum/Decomp) | modified | Constant as in (6.2) above. |
| Step 4: heads with K_* ≤ k < K_W | `block_heads`, `block_kloost`, `dyadic_split`, `R_bound` (ThetaSum/Heads, HeadsBG, Decomp, RBound) | modified | (HBG) is used here and nowhere else. |
| Step 5: generic tails | `phiTail_generic`, `tails_sum`, `tails_sum_explicit` (ThetaSum/TailsAll) | modified | Uses the elementary Lemma 6.6. The sum over k is bounded by (log K)(1 + log K) in place of 1 + ¼(log K)². The tails stay O(1). |
| Step 6: non-generic tails | `nongeneric_mass`, `nongeneric_mass_D` (ThetaSum/Tails); `tails_sum_explicit` (ThetaSum/TailsAll) | modified | Same argument: witnesses (Lemma 6.7) and Theorem 1.3 with γ₀ = 1/20. Constants differ (the mass bound is 2·M·I·T^{−γ₀/4}, with I dyadic ranges of r). |
| Step 7: conclusion | `R_bound` (ThetaSum/RBound); `Gb_small` (ThetaSum/Asym2); `eventually_good2`, `lower_half_gen` (ThetaSum/LowerHalf) | modified | Lean shows that the explicit bound for (4/π)\|R_{K_W}(p)\| plus the constant is less than (log p)/2 for all large p. This gives S(p)/p → ∞, not the exponent 19/20. |
| Section 8.2: Conjecture 3.3 from Theorem 1.1 | `lower_real`, `conj_of_lower`, `conjecture_3_3_34` (ThetaSum/Conjecture33); `conjecture_3_3_of_BG` (ThetaSum/Headline) | exact | |
| Remark 8.1 | not formalized | — | |

## Section 9: computations

| Result | Lean declaration(s) | Status | Notes |
|---|---|---|---|
| Lemma 9.1: U(a) = (p − 1)a − 4W(2p, a); S(p) = (p − 1)³/4 − 4Σ W(2p, a); (9.1); (9.2) | `Tq_odd`, `S_eq_lemma25`, `Ffl_add`, `Ffl_recip` (ThetaSum/Compute) | exact | The proof avoids alternating-sign counting. It uses (−1)^m = 1 − 2m + 4⌊m/2⌋ and a general lattice-point lemma (`lattice`). |
| Section 9.2: Euclid-type evaluation of W(2p, a) and S(p) | `Fe_eq`, `Sfast_eq` (ThetaSum/Compute) | exact | `Sfast` is the evaluator used by the kernel computations. |
| Section 9.3: proof of Proposition 1.2 | see Section 1 | modified | |
| Sections 9.4, 9.5 (statistics, open range) | not formalized | — | |

## Further formalized results not used in the paper

| Statement | Lean declaration(s) | Notes |
|---|---|---|
| S(p) = (p/2)log p + O(p(log p)^{2/3+γ₀}(log log p)^{8/3}), γ₀ ∈ (0, 2/3) | `theorem_C` (ThetaSum/TheoremC); `theorem_C_c0` (ThetaSum/ConstantC0) | From (HBGfull), the Bourgain–Garaev bound for log N ≥ A(log p)^{2/3}(log log p)^{8/3}. The c·p term is below the error, so c = c₀ in `theorem_C_c0` is cosmetic. |
| S(p) = (p/2)log p + O(p(log p)^{2/3}(log log p)^{17/3}) | `theorem_C_star` (ThetaSum/TheoremCStar); `theorem_C_star_c0` (ThetaSum/ConstantC0) | From (HBGfull); same remark. |
| Variant of Theorem 1.3 with log T ≥ (log log q)³ | `theorem_D_star` (ThetaSum/TheoremDStar); `nongeneric_mass_Dstar`, `tails_sum_star_explicit` (ThetaSum/TailsStar) | Stated for log log q ≥ 1000. Used only by `theorem_C_star`. |
| \|S(p)\| ≤ 5p·H_p² | `S_abs_le`, `S_abs_le_log` (Upper/Main) | Used for the upper half of Conjecture 3.3. |
| C_m(k) = F_m(k) for odd m, k | `Cp_eq_Fsum` (Upper/Tangent) | Used in the proof of `Recip.reciprocity`. |
| F_k(n) = Σ_{d∣k, d≥3} G_d(n); averages of G_d over residue classes; \|G_d(n)\| ≤ G_d(1) | `Fsum_eq_sum_Gsum`, `Gsum_avg`, `Gsum_abs_le` (Upper/Tangent) | |
| Conjecture 3.3 with the cutoff ⌊√p(log p)⁴⌋, from (HBweak) and (HBG) | `conjecture_3_3` (ThetaSum/Conjecture33); `lower_half` (ThetaSum/LowerHalf) | (HBweak) is the analogue of `hBweak34` for this cutoff; by Remark 4.5 it would follow from Weil's bound. It is not proved in Lean and not used by the headline. |

## Dependency structure of `conjecture_3_3_of_HKS` and `conjecture_3_3_of_BG`

`conjecture_3_3_of_HKS` (ThetaSum/WeakHyp) is `conj_of_lower (lower_half_HKS hK)`, where `lower_half_HKS = lower_half_gen_KS (3/4) … (HB34_of_HBweak34 hBweak34) hV_holds hK`. `lower_half_gen_KS` is the same argument as `lower_half_gen` below, with three changes:
- (HKS) replaces (HBG) in the block bound (`block_kloost_KS`, via `one_term_KS` and Lemma 5.2);
- the parameters are K_* = exp(L^{θ'}) with θ' = (1+θ)/2, and T = exp(L^γ) with γ = min(δ, (1−θ)/8)/2;
- the explicit bound is `GbK`, shown to be o(L) by `GbK_small`.

Both versions run through `R_bound_gen` (ThetaSum/RBound). That lemma takes any block bound 4·Q·2a. The (HBG) version is shown in the tree below:

```
ThetaSum.conjecture_3_3_of_BG (hBG : HBG)                        ThetaSum/Headline
└─ conjecture_3_3_34 hBweak34 hBG                                ThetaSum/Conjecture33
   ├─ conjecture_3_3_upper  (Corollary 2.6; unconditional)       ThetaSum/Conjecture33
   │  └─ Arxiv.«2501.03234».conjecture_3_3_upper ← S_abs_le_log ← main_bound      Upper/Main
   └─ lower_real ← lower_half_HBweak34_HBG                       ThetaSum/LowerHalfFinal
      ├─ hBweak34  (Theorem 4.1(ii), K = ⌊p^{3/4}(log p)^4⌋; unconditional)       ThetaSum/Headline
      │  ├─ TheoremB.HBweak34_of_HK34                            Upper/TheoremB
      │  │  ├─ S_eq_Psi_Phi (Thm 4.1(i)) ← Recip.reciprocity (Lemma 3.1), T_dual, S_dual (Upper/Cot)
      │  │  ├─ Psi_bound ← I_asymp ← Cp_one_le, Fsum_one_eq_Cp
      │  │  └─ sum_Cp_interval (Lemma 4.4) ← weil_kbar (Lemma 4.3) ← KlBound_of_HK34
      │  └─ HK34_bridge ← hK34 ← kloosterman_bound ← kl_four_le (Lemma 4.2)       ThetaSum/Kloosterman
      ├─ HB34_of_HBweak34                                        ThetaSum/Hypotheses
      └─ lower_half34 = lower_half_gen (θ = 3/4) … hV_holds      ThetaSum/LowerHalf
         ├─ hV_holds ← Vaaler.vaaler_real (Lemma 6.2)            ThetaSum/HVProof, ThetaSum/Vaaler
         ├─ tails_sum_explicit                                   ThetaSum/TailsAll
         │  ├─ phiTail_generic ← generic_bound (elementary Lemma 6.6), tail_partial_summation (Lemma 6.5(a))
         │  ├─ phiTail_trivial ← tail_trivial (Lemma 6.5(b))     ThetaSum/TailBound
         │  └─ nongeneric_mass_D ← nongeneric_mass, witness (Lemma 6.7), theorem_D (Theorem 1.3)   ThetaSum/Tails
         │        theorem_D ← base_level (rankin_delta, Lemma 7.1), rec_step (one_step_harmonic, dyadic_sum_le)
         ├─ R_bound  (|R_K(p)| explicitly bounded)               ThetaSum/RBound
         │  ├─ Fsum_split ← sign_form (Lemma 6.1)                ThetaSum/Decomp, ThetaSum/SignForm
         │  ├─ headTh_trivial (heads below K_*, (6.2))           ThetaSum/Decomp
         │  ├─ headTh_eq_headTerm ← bridge                       ThetaSum/Decomp, ThetaSum/Bridge
         │  ├─ dyadic_split                                      ThetaSum/Decomp
         │  ├─ block_heads (Lemma 6.4) ← square_wave (Lemma 6.3) ← HV;
         │  │                            abel_antitone, weight_antitone   ThetaSum/Heads, ThetaSum/Weights
         │  └─ block_kloost (Cor. 5.3) ← odd_interval_bound (Lemma 5.2) ← **HBG** (Lemma 5.1)   ThetaSum/HeadsBG, ThetaSum/Kloost
         └─ Gb_small, eventually_good2  (the bound is o(log p))   ThetaSum/Asym2, ThetaSum/LowerHalf
```

Bottom line:
- (HBG) is used in exactly one place: in `block_kloost`, for the heads with K_* ≤ k < K_W. In the (HKS) version, (HKS) is likewise used only in `block_kloost_KS`.
- Everything else in the chain is proved.

## Trusted base (for `conjecture_3_3_of_HKS`)

1. **The Lean 4 kernel**, toolchain `leanprover/lean4:v4.35.0`. The finite-range results also rely on kernel evaluation of `Nat` arithmetic (`decide +kernel`, GMP-accelerated `Nat` primitives). No `native_decide` and no `Lean.ofReduceBool` are used anywhere.
2. **Mathlib v4.35.0** (`lakefile.toml`, `lake-manifest.json`), with the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
3. **The definitions** `S'` and `S`, copied verbatim from google-deepmind/formal-conjectures, `FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean`.
4. **The single hypothesis (HKS)**, `ThetaSum/WeakHyp.lean`:

```lean
def HKS : Prop :=
  ∃ δ θ C : ℝ, 0 < δ ∧ θ < 1 ∧ ∀ᶠ p : ℕ in Filter.atTop, p.Prime →
    ∀ b : ZMod p, b ≠ 0 → ∀ N : ℕ, Real.log p ^ θ ≤ Real.log N → N < p →
      ‖∑ n ∈ Icc 1 N, psiP p (b * (n : ZMod p)⁻¹)‖ ≤ C * N * Real.log p ^ (-δ)
```

`HKS_of_HBG : HBG → HKS` takes θ = 9/10 and δ = 1/4. So (HKS) is weaker than (HBG), defined next:

```lean
def HBG : Prop :=
  ∃ C : ℝ, ∀ᶠ p : ℕ in Filter.atTop, p.Prime →
    ∀ b : ZMod p, b ≠ 0 → ∀ N : ℕ, Real.log p ^ (9 / 10 : ℝ) / 2 ≤ Real.log N → N < p →
      ‖∑ n ∈ Icc 1 N, psiP p (b * (n : ZMod p)⁻¹)‖ ≤
        C * Real.log (Real.log p) ^ 3 * Real.log p * Real.log N ^ (-(3 / 2 : ℝ)) * N
```

with `psiP p x = exp(2πi·x.val/p)`.

**Source:** J. Bourgain and M. Z. Garaev, *Sumsets of reciprocals in prime fields and multilinear Kloosterman sums*, Izv. Math. 78 (2014); arXiv:1211.4184, Theorem 16. That theorem reads |Σ_{n≤N} e_p(an\*)| ≪ (log log p)³(log p)(log N)^{−3/2}N, with an absolute implied constant and no hypothesis on N. (HBG) is Lemma 5.1 of the paper: the theorem restricted to log N ≥ ½(log p)^{9/10}. The proof of Lemma 5.1 explains why the proof of Theorem 16 covers log N > C^{2/3}(log p)^{2/3}(log log p)^{8/3}, which contains this range for all large p. Checking this against the source is the one step of the argument that is not machine-checked.
