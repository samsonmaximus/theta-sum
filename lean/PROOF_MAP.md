# Proof map: paper → Lean

Paths are relative to `lean/`. "ThetaSum/X" means `ThetaSum/X.lean`, and "Upper/X" means `Upper/X.lean`.

**Status values used in the tables:**
- **exact**: the Lean statement is the paper's statement, up to notation.
- **modified**: the Lean statement differs, and the difference is stated.
- **not formalized**: nothing in Lean corresponds.

Every Lean declaration named below is free of `sorry` and `native_decide`. Its `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound` (`ThetaSum/MainTheorems.lean`).

`S'` and `S` are the formal-conjectures definitions, copied verbatim into `Upper/Defs` and `ThetaSum/Hypotheses`. `ThetaSum.S_bridge` proves the two copies equal by `rfl`.

## 1. Main paper (`../paper/theta_sum.pdf`)

### Section 1: main results

| Statement (short) | Lean declaration(s) | Status | Notes |
|---|---|---|---|
| Conjecture 3.3: C₁k < S(k) < C₂k^{1+ε} for large primes k | `ThetaSum.conjecture_3_3_of_HKS` (ThetaSum/WeakHyp); `conjecture_3_3_of_BG` (ThetaSum/Headline) | modified | Assumes (HKS), which is implied by (HBG). Also stated as `ThetaSum.conjecture_3_3` (ThetaSum/Conjecture33), from (HBweak) and (HBG). |
| Theorem A: \|S(p)\| ≤ (cotangent bound) | `Arxiv.«2501.03234».theorem_A`, `S_abs_le_cot` (Upper/Cot) | modified | Uses the constant 2 from Lemma 3.3 in place of K₀. |
| Upper half of Conj. 3.3, Appendix A: \|S(p)\| ≤ 5p·H_p² | `Arxiv.«2501.03234».S_abs_le`, `S_abs_le_log`, `conjecture_3_3_upper` (Upper/Main); `ThetaSum.conjecture_3_3_upper` (ThetaSum/Conjecture33) | exact | Unconditional. |
| Theorem B(i): S(p) = Ψ(p) + Φ(p) | `TheoremB.S_eq_Psi_Phi` (Upper/TheoremB) | exact | |
| Theorem B(ii): S(p) = (p/2)log p + c₀p + (4p/π)R_K(p) + O(p/log p) for √p(log p)⁴ ≤ K ≤ p^{9/10} | `ThetaSum.theorem_B_c0` (ThetaSum/ConstantC0); weaker forms `TheoremB.HBweak34_of_HK34` (Upper/TheoremB), `ThetaSum.hBweak34` (ThetaSum/Headline) | modified | Unconditional, with the exact constant c₀. The error is o(p) (≤ εp for all large p), not O(p/log p). The cutoff is K = ⌊p^{3/4}(log p)⁴⌋ (Kloosterman), not √p(log p)⁴ (Weil). (`HBweak34_of_HK34` has c₀ existential and error O(p).) |
| The constant c₀ (1.6) | `ThetaSum.c0_closed_form` (ThetaSum/ZetaClosed) | exact | c₀ = K₀/2 + (log 2)/6 + (3/π²)·Re ζ′(2), with K₀ = γ + log(4/π). Supporting lemmas: `SLodd_closed_form`, `deriv_zeta_two`. |
| Theorem C: \|S(p) − (p/2)log p − c₀p\| ≤ Cp(log p)^{2/3+γ₀}(log log p)^{8/3} | `ThetaSum.theorem_C` (ThetaSum/TheoremC); `ThetaSum.theorem_C_c0` (ThetaSum/ConstantC0) | modified | From (HBGfull). In `theorem_C` the constant c is existential. `theorem_C_c0` has c = c₀, but this is cosmetic: the error exceeds p, so the formal content of both is S(p) = (p/2) log p + O(p(log p)^{2/3+γ₀}(log log p)^{8/3}). The real content about c₀ is `theorem_B_c0` and `Psi_asymp` |
| Corollary 1.1: S(p)/p → ∞, so Conj. 3.3 holds | `ThetaSum.lower_half_HBweak34_HBG` (ThetaSum/LowerHalfFinal); `conjecture_3_3_of_BG` | modified | Assumes (HBG). Gives n·p < S(p) for all large p, for every n ∈ ℕ. |
| Theorem D: large divisors in progressions, T = exp((log q)^{γ₀}) | `ThetaSum.theorem_D` (ThetaSum/Asymptotics) | exact | Proof differs: no Mertens bound, a different Rankin step and different parameters. L₀ is not explicit, as in the paper. |
| Proposition 1.3: thresholds 0, p, 2p, 3p, 4p, 5p for odd primes p ≤ 6·10⁶ | `ThetaSum.S_pos_upto`, `S_gt_self_upto`, `S_gt_two_mul_upto`, `S_gt_three_mul_upto`, `S_233`, `S_3119` (ThetaSum/FiniteRange, ThetaSum/FormalConjectures); `Arxiv.«2501.03234».S_fst_10` | modified | Proved for p ≤ 2·10⁴ only, and only for the thresholds 0, p (p > 5), 2p (p > 233), 3p (p > 3119). The checks are kernel-evaluated (`decide +kernel`). Sharpness is proved: S(5) = 4, S(233) = 440, S(3119) = 9194. The 4p and 5p thresholds are not formalized. |
| Theorems E, F; Corollary 1.2 | not formalized | — | |

### Section 2: elementary reformulations

| Statement (short) | Lean declaration(s) | Status | Notes |
|---|---|---|---|
| Lemma 2.1(a)–(c): S(p) = Σ_a T(a); T(even) = 0; S'(p−a, p) = T(a) | `ThetaSum.S_eq_sumT`, `Tq_even`, `S'_reflect` (ThetaSum/Compute); `Arxiv.«2501.03234».T_even`, `S_eq_sum_T` (Upper/Cot) | exact | (a) is used in the form S = Σ_a T(a). |
| Remark 2.2 (Hardy and Dedekind sums) | not formalized | — | The paper has no Lemma 2.2. |
| Lemma 2.3: sawtooth form | not formalized | — | |
| Lemma 2.4: Lehmer form | not formalized | — | |
| Lemma 2.5: T(a) = (p−1)a − 4F(2p, a); S(p) = (p−1)³/4 − 4Σ F(2p, a); the two reciprocity identities for F | `ThetaSum.Tq_odd`, `S_eq_lemma25`, `Ffl_add`, `Ffl_recip` (ThetaSum/Compute) | exact | The proof avoids alternating-sign counting. It uses (−1)^m = 1 − 2m + 4⌊m/2⌋ and a general lattice-point lemma (`lattice`). |
| (Lemma 2.5, algorithm) Euclid-type evaluation | `ThetaSum.Fe_eq`, `Sfast_eq` (ThetaSum/Compute) | exact | Mirrors `../code/thetasum.c`. |
| Lemma 2.6: Gauss-lemma form | not formalized | — | |
| Lemma 2.7: cubic moments | not formalized | — | |

### Section 3: dual formula and Theorem A

| Statement (short) | Lean declaration(s) | Status | Notes |
|---|---|---|---|
| Lemma 3.1: dual formula for T(a) | `Arxiv.«2501.03234».T_dual` (Upper/Cot) | exact | Formula (3.1) is `S_dual`. |
| Lemma 3.2: sign form of C_p(k); \|C_p(k)\| ≤ C_p(1) | `Cp_sign_form`, `Cp_abs_le` (Upper/Cot) | exact | |
| Lemma 3.3: C_m(1) ≤ (m/π)(log m + 2) | `Cp_one_le` (Upper/Cot) | exact | |

### Section 4: reciprocity and the expansion of F_k(n)

| Statement (short) | Lean declaration(s) | Status | Notes |
|---|---|---|---|
| Lemma 4.1: reciprocity C_m(k) = (m/k)F_k(m) + I(k/m) | `Recip.reciprocity` (Upper/Reciprocity) | exact | Proof avoids contour integration: a polynomial identity at roots of unity (`Dpoly_eq_zero`) and termwise integration (`integral_Jint`). |
| Lemma 4.2: πλI(λ) = log(1/λ) + K₀ − ρ(λ), 0 ≤ ρ ≤ 7πλ/72; I(1/λ) = −λI(λ) | `TheoremB.I_asymp_K0` (ThetaSum/ConstantC0); `TheoremB.I_asymp` (Upper/TheoremB); `Recip.Ifun_inv`, `Ifun_pos` (Upper/Reciprocity) | modified | Weak form: \|πλI(λ) − log(1/λ) − K₀\| ≤ λ(4 log(1/λ) + 91) on (0, 1], in place of 0 ≤ ρ ≤ 7πλ/72. The identity I(1/λ) = −λI(λ) is exact. |
| Corollary 4.3: (a) F_m(1) = C_m(1) = I(1/m), with the asymptotic for C_m(1); (b) \|F_k(r)\| ≤ F_k(1); (c) asymptotics | `Fsum_one_eq_Cp`, `Fsum_abs_le` (Upper/Tangent); `TheoremB.Cp_one_asymp`, `I_asymp_K0` (ThetaSum/ConstantC0) | modified | (a): the identity in its elementary part, plus \|C_m(1) − (m/π)(log m + K₀)\| ≤ 9 for odd m ≥ 5 (`Cp_one_asymp`). (b) is the elementary part. (c) is in the weak form of Lemma 4.2. |
| Lemma 4.4: odd reciprocity | `Cp_eq_Fsum` (Upper/Tangent); `Recip.reciprocity` | modified | First part (C_m(k) = F_m(k)) is exact. The second identity is not stated separately. |
| Proposition 4.5 – Corollary 4.11: expansion, bounded part, steps, converse, explicit formula, singularities | not formalized | — | Not used in the proof of Theorem C or of Conj. 3.3. |

### Section 5: Weil's bound

| Statement (short) | Lean declaration(s) | Status | Notes |
|---|---|---|---|
| Lemma 5.2 (Weil): short sums of e(ck̄/p) ≤ 2√p(1 + log p)-type bound | `TheoremB.weil_kbar` (Upper/TheoremB) | modified | Proved for any uniform Kloosterman bound `KlBound p B`. It is used with B = 2p^{3/4} (Kloosterman, proved). Weil's bound itself (`TheoremB.HW`) is not formalized and not used. |
| Lemma 5.3: Σ_{k∈J} C_p(k) ≤ 2p^{3/2}(log p + 2)³ | `TheoremB.sum_Cp_interval` (Upper/TheoremB) | modified | Same remark: the bound is in terms of B. With B = 2p^{3/4} it gives p^{7/4}-type bounds. |

### Section 6: tools for Theorem C

| Statement (short) | Lean declaration(s) | Status | Notes |
|---|---|---|---|
| Lemma 6.1: sign form F_k(p) = −Σ_n cot(πn/2k)·sgn(½ − {nθ_k}) | `ThetaSum.sign_form` (ThetaSum/SignForm); `Fsum_split` (ThetaSum/Decomp) | exact | (a) and (b) in combined form. For (c), θ_k ↔ (2k)⁻¹ mod p: `ThetaSum.bridge` (ThetaSum/Bridge). |
| Lemma 6.2: Vaaler's lemma | `Vaaler.vaaler_lemma`, `vaaler_real` (ThetaSum/Vaaler); `ThetaSum.hV_holds` (ThetaSum/HVProof) | exact | Finite proof, with no Fourier analysis on ℝ. |
| Lemma 6.3: square wave | `ThetaSum.square_wave` (ThetaSum/SquareWave) | exact | Up to constants: \|b_h\| ≤ 4/(πh) and a majorant 2/(H+1)(1 + Σd_h cos). |
| Lemma 6.4: reduction to initial Kloosterman sums | `ThetaSum.odd_interval_sum`, `odd_interval_bound` (ThetaSum/Kloost); `block_kloost` (ThetaSum/HeadsBG) | modified | Same mechanism, with 4 initial sums T_{c/2}, T_{c/4}. |
| Lemma 6.5: Bourgain–Garaev | hypothesis `ThetaSum.HKS` (ThetaSum/WeakHyp), or `ThetaSum.HBG` (ThetaSum/Hypotheses) | not formalized | The headline uses only (HKS): any (log p)^{−δ} saving for log N ≥ (log p)^θ, θ < 1. `HKS_of_HBG` derives it from (HBG). (HBG) is assumed only for log N ≥ (log p)^{9/10}/2, which lies inside the range of Lemma 6.5 of the paper. |
| Lemma 6.6: heads | `ThetaSum.block_heads` (ThetaSum/Heads), `block_kloost` (ThetaSum/HeadsBG), `R_bound` (ThetaSum/RBound) | modified | Constants differ. Abel summation uses `abel_antitone` and `weight_antitone` (ThetaSum/Weights). |
| Lemma 6.7: tails, (a) partial summation and (b) trivial bound | `ThetaSum.tail_partial_summation`, `tail_trivial` (ThetaSum/TailBound) | modified | Constants: (a) (π/2)·D·(log k − log N); (b) (log k)/π. |
| Lemma 6.8: generic θ | `ThetaSum.generic_bound`, `generic_bound_div` (ThetaSum/Generic) | modified | This is an elementary version, not the Vaaler-based proof of the paper. Bound 6J/M + 1/η, with no hypothesis nθ ∉ ½ℤ. |
| Lemma 6.9: witnesses | `ThetaSum.witness` (ThetaSum/Tails) | exact | |

### Section 7: proof of Theorem D

| Statement (short) | Lean declaration(s) | Status | Notes |
|---|---|---|---|
| Lemma 7.1: Rankin, Δ(A; Y) ≤ \|I\|Y^{−α}P(α), with a bound for log P(α) | `ThetaSum.rankin_delta`, `sum_primeFactors_rpow_le` (ThetaSum/Rankin) | modified | log P(α) ≤ 4L^α(1/α + 2), from splitting prime factors at L. θ(ℓ) ≥ ℓ/2 is not used. |
| Lemma 7.2: one step | `ThetaSum.one_step`, `one_step_le`, `one_step_euler` (ThetaSum/OneStep); `one_step_harmonic` (ThetaSum/Counting) | modified | Uses the harmonic bound 1 + log R in place of Mertens. |
| Lemma 7.3: G_y(2^j Z) ≤ (1 + N_y)^{1+j log 2/log y} G_y(Z) | `ThetaSum.G_le_rpow`, `dyadic_sum_le` (ThetaSum/Counting) | modified | Replaced by G_y(Z) ≤ Z^{log(N_y+1)/log y}. |
| (Section 8, non-generic tail mass via Theorem D) | `ThetaSum.nongeneric_mass`, `nongeneric_mass_D` (ThetaSum/Tails); `tails_sum`, `tails_sum_explicit` (ThetaSum/TailsAll) | modified | The bound (log K)(1 + log K) replaces the sharper (1/4)(log K)². The tails stay O(1). |
| Lemma 9.1, Lemma 9.2(a) | `Fsum_eq_sum_Gsum`, `Gsum_avg` (Upper/Tangent) | exact | |

## 2. Further results of the main paper, and the companion paper (`../companion/theta_sum_distribution.pdf`)

| Statement (short) | Lean declaration(s) | Status | Notes |
|---|---|---|---|
| Lemma 6.5 (range log N ≥ A_BG(log p)^{2/3}(log log p)^{8/3}) | hypothesis `ThetaSum.HBG` | not formalized | The Lean hypothesis is the bound on a smaller range: log N ≥ (log p)^{0.9}/2. |
| Theorem C♭ (Conjecture 3.3 from any power-of-log saving; K_* = exp(L^{0.9})) | `ThetaSum.lower_half_gen` (ThetaSum/LowerHalf) | exact | Parameters: K_* = ⌈exp(L^{9/10})⌉, T = exp(L^{1/20}), M = H = ⌈L²⌉. |
| Theorem D*: explicit threshold, log T ≥ (log L)³ | `ThetaSum.theorem_D_star` (ThetaSum/TheoremDStar) | modified | Threshold log log q ≥ 1000 in place of an absolute q₁. Statement otherwise as in the paper. |
| Theorem C* (no ε) | `ThetaSum.theorem_C_star` (ThetaSum/TheoremCStar); `theorem_C_star_c0` (ThetaSum/ConstantC0) | modified | From (HBGfull), with error p(log p)^{2/3}(log log p)^{17/3}. As for Theorem C, the c₀p term is below the error and is not captured in any meaningful way |
| Lemma 6.8 without Vaaler | `ThetaSum.generic_bound`, `generic_bound_div` (ThetaSum/Generic) | modified | Stronger constant: 6J/M + 1/η, against 13J/M + 1/η in a written version. No hypothesis nθ ∉ ½ℤ. |
| Theorem D without Mertens | `ThetaSum.theorem_D`, `theorem_D_star` | exact | This is the route the formalization takes. |
| Companion, Theorem 1 (limiting distribution) | not formalized | — | |
| Companion, Theorem 3 (extreme values) | not formalized | — | |
| Companion, tails of the limit law | not formalized | — | |
| Lemma: \|G_d(n)\| ≤ G_d(1) (companion paper; used for the sharp tails and the effective extreme values) | `Arxiv.«2501.03234».Gsum_abs_le` (Upper/Tangent) | exact | |
| Companion, Theorems 1–4 and their corollaries | not formalized | — | They need the prime number theorem in progressions, Gallagher's theorem and martingale inequalities, which Mathlib does not have |

## 3. Dependency structure of `conjecture_3_3_of_HKS` and `conjecture_3_3_of_BG`

`conjecture_3_3_of_HKS` (ThetaSum/WeakHyp) is `conj_of_lower (lower_half_HKS hK)`, where `lower_half_HKS = lower_half_gen_KS (3/4) … (HB34_of_HBweak34 hBweak34) hV_holds hK`. `lower_half_gen_KS` is the same argument as `lower_half_gen` below, with three changes:
- (HKS) replaces (HBG) in the block bound (`block_kloost_KS`, via `one_term_KS` and Lemma 6.4);
- the parameters are K_* = exp(L^{θ'}) with θ' = (1+θ)/2, and T = exp(L^γ) with γ = min(δ, (1−θ)/8)/2;
- the explicit bound is `GbK`, shown to be o(L) by `GbK_small`.

Both versions run through `R_bound_gen` (ThetaSum/RBound). That lemma takes any block bound 4·Q·2a. The (HBG) version is shown in the tree below:

```
ThetaSum.conjecture_3_3_of_BG (hBG : HBG)                        ThetaSum/Headline
└─ conjecture_3_3_34 hBweak34 hBG                                ThetaSum/Conjecture33
   ├─ conjecture_3_3_upper  (unconditional)                      ThetaSum/Conjecture33
   │  └─ Arxiv.«2501.03234».conjecture_3_3_upper ← S_abs_le_log ← main_bound      Upper/Main
   └─ lower_real ← lower_half_HBweak34_HBG                       ThetaSum/LowerHalfFinal
      ├─ hBweak34  (Theorem B(ii), p^{3/4} cutoff; unconditional)                 ThetaSum/Headline
      │  ├─ TheoremB.HBweak34_of_HK34                            Upper/TheoremB
      │  │  ├─ S_eq_Psi_Phi (B(i)) ← Recip.reciprocity (Lemma 4.1), T_dual, S_dual (Upper/Cot)
      │  │  ├─ Psi_bound ← I_asymp ← Cp_one_le, Fsum_one_eq_Cp
      │  │  └─ sum_Cp_interval ← weil_kbar ← KlBound_of_HK34
      │  └─ HK34_bridge ← hK34 ← kloosterman_bound ← kl_four_le (fourth moment)   ThetaSum/Kloosterman
      ├─ HB34_of_HBweak34                                        ThetaSum/Hypotheses
      └─ lower_half34 = lower_half_gen (θ = 3/4) … hV_holds      ThetaSum/LowerHalf
         ├─ hV_holds ← Vaaler.vaaler_real                        ThetaSum/HVProof, ThetaSum/Vaaler
         ├─ tails_sum_explicit                                   ThetaSum/TailsAll
         │  ├─ phiTail_generic ← generic_bound (elementary Lemma 6.8)  ThetaSum/Generic
         │  ├─ phiTail_trivial ← tail_trivial (Lemma 6.7)        ThetaSum/TailBound
         │  └─ nongeneric_mass_D ← nongeneric_mass, witness (Lemma 6.9), theorem_D    ThetaSum/Tails
         │                         theorem_D ← one_step, rankin_delta, G_le_rpow, base_level, rec_step
         ├─ R_bound  (\|R_K(p)\| explicitly bounded)             ThetaSum/RBound
         │  ├─ Fsum_split ← sign_form (Lemma 6.1)                ThetaSum/Decomp, ThetaSum/SignForm
         │  ├─ headTh_trivial (heads below K_*)                  ThetaSum/Decomp
         │  ├─ headTh_eq_headTerm ← bridge                       ThetaSum/Decomp, ThetaSum/Bridge
         │  ├─ dyadic_split                                      ThetaSum/Decomp
         │  ├─ block_heads (Lemma 6.6) ← square_wave (Lemma 6.3) ← HV;
         │  │                            abel_antitone, weight_antitone   ThetaSum/Heads, ThetaSum/Weights
         │  └─ block_kloost ← odd_interval_bound (Lemma 6.4) ← **HBG** (Lemma 6.5)    ThetaSum/HeadsBG, ThetaSum/Kloost
         └─ Gb_small, eventually_good2  (the bound is o(log p))   ThetaSum/Asym2, ThetaSum/LowerHalf
```

Bottom line:
- (HBG) is used in exactly one place: in `block_kloost`, for the heads with K_* ≤ k < K_W. In the (HKS) version, (HKS) is likewise used only in `block_kloost_KS`.
- Everything else in the chain is proved.

## 4. Trusted base (for `conjecture_3_3_of_HKS`)

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

**Source:** J. Bourgain and M. Z. Garaev, *Sumsets of reciprocals in prime fields and multilinear Kloosterman sums*, Izv. Math. 78 (2014); arXiv:1211.4184, Theorem 16. That theorem reads |Σ_{n≤N} e_p(an*)| ≪ (log log p)³(log p)(log N)^{−3/2}N, with an absolute implied constant. Lemma 6.5 of the paper analyses the range: the proof in §12.2 of the source covers log N ≥ A_BG(log p)^{2/3}(log log p)^{8/3}. (HBG) asks only for log N ≥ (log p)^{0.9}/2, which lies inside that range for all large p. So (HBG) is a consequence of the published theorem, as its proof stands.
