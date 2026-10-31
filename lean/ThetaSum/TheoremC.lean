import ThetaSum.RBoundG
import ThetaSum.Headline

/-!
# Theorem C of arXiv:2501.03234 (the asymptotic formula), conditional on (HBGfull)

`theorem_C : HBGfull → ∀ γ₀ ∈ (0, 2/3), ∃ c C, for all large primes p,
  |S(p) - (p/2) log p - c p| ≤ C p (log p)^{2/3+γ₀} (log log p)^{8/3}`.

(HBGfull) is the Bourgain–Garaev bound in its full range
`N ≥ exp(A (log p)^{2/3} (log log p)^{8/3})` (paper, Lemma 6.5).

Route (§8 of the paper): `hBweak34` (Theorem B with Kloosterman's bound, proved) gives
`S(p) = (p/2) log p + c p + (4p/π) R_{K}(p) + O(p)` with `K = KW34 p`; and `R_thmC` bounds
`|R_K(p)| ≤ C₂ (log p)^{2/3+γ₀} (log log p)^{8/3}` via `R_boundG` with, writing `L = log p`,
`ℓ = log L`, `γ₁ = γ₀/2`, `s = L^{1/3} ℓ^{4/3}`:
`T = exp(L^{γ₁})`, `M = H = ⌈L²⌉`, `N = ⌈T M⌉`, `K_* = ⌈exp(A' s²)⌉` (`A' = max A 0 + 1`),
`J = ⌈2L⌉`, `I = ⌊log₂ K⌋ + 1`. The dyadic sum `∑_j log(2^j K_*/3)^{-3/2} ≤ 16 ℓ/s` and
`s³ = L ℓ⁴` give the heads in `[K_*, K)` as `O(L^{γ₁} ℓ s²)`; `ℓ ≤ L^{γ₁}` absorbs the
logarithm.
-/

open Finset Filter

namespace ThetaSum

/-- **(HBGfull)** The Bourgain–Garaev bound for short Kloosterman sums in its full range
(paper, Lemma 6.5): for all large primes `p`, all `b ≢ 0` and all `N < p` with
`N ≥ exp(A (log p)^{2/3} (log log p)^{8/3})`,
  `|∑_{n=1}^N e(b n^*/p)| ≤ C (log log p)^3 (log p) (log N)^{-3/2} N`. -/
def HBGfull : Prop :=
  ∃ C A : ℝ, ∀ᶠ p : ℕ in Filter.atTop, p.Prime →
    ∀ b : ZMod p, b ≠ 0 → ∀ N : ℕ,
      Real.exp (A * Real.log p ^ (2 / 3 : ℝ) * Real.log (Real.log p) ^ (8 / 3 : ℝ)) ≤ N → N < p →
      ‖∑ n ∈ Icc 1 N, psiP p (b * (n : ZMod p)⁻¹)‖ ≤
        C * Real.log (Real.log p) ^ 3 * Real.log p * Real.log N ^ (-(3 / 2 : ℝ)) * N

/-- `∑_{j<J} log(2^j K_*/3)^{-3/2} ≤ 2 (1 + log(J+1)) / √(log(K_*/3))` when `log(K_*/3) ≥ 1`. -/
lemma sum_dyadic_pow (Ks J : ℕ) (hl : 1 ≤ Real.log ((Ks : ℝ) / 3)) :
    ∑ j ∈ range J, Real.log (((2 ^ j * Ks : ℕ) : ℝ) / 3) ^ (-(3 / 2 : ℝ)) ≤
      2 * (1 + Real.log (J + 1)) / Real.sqrt (Real.log ((Ks : ℝ) / 3)) := by
  set lam := Real.log ((Ks : ℝ) / 3) with hlam
  have hKs : (0 : ℝ) < Ks := by
    rcases Nat.eq_zero_or_pos Ks with h | h
    · rw [h, Nat.cast_zero, zero_div, Real.log_zero] at hlam; linarith
    · exact_mod_cast h
  have hsq : 0 < Real.sqrt lam := Real.sqrt_pos.mpr (by linarith)
  have hterm : ∀ j ∈ range J, Real.log (((2 ^ j * Ks : ℕ) : ℝ) / 3) ^ (-(3 / 2 : ℝ)) ≤
      2 / Real.sqrt lam * (1 / ((1 + j : ℕ) : ℝ)) := by
    intro j _
    have e : Real.log (((2 ^ j * Ks : ℕ) : ℝ) / 3) = j * Real.log 2 + lam := by
      push_cast
      rw [show (2 : ℝ) ^ j * Ks / 3 = 2 ^ j * (Ks / 3) by ring,
        Real.log_mul (by positivity) (by positivity), Real.log_pow]
    rw [e]
    set x := (j : ℝ) * Real.log 2 + lam
    have hl2 := Real.log_two_gt_d9
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hx1 : lam ≤ x := by
      have := mul_nonneg hj0 (by linarith : (0 : ℝ) ≤ Real.log 2); linarith
    have hx2 : ((j : ℝ) + 1) / 2 ≤ x := by nlinarith
    have hx0 : 0 < x := by linarith
    have hsx : Real.sqrt lam ≤ Real.sqrt x := Real.sqrt_le_sqrt hx1
    have h32 : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx0, Real.rpow_one,
        Real.sqrt_eq_rpow]
    rw [Real.rpow_neg hx0.le, h32, ← one_div]
    have hpos : 0 < ((j : ℝ) + 1) / 2 * Real.sqrt lam := by positivity
    calc 1 / (x * Real.sqrt x) ≤ 1 / (((j : ℝ) + 1) / 2 * Real.sqrt lam) :=
          one_div_le_one_div_of_le hpos (mul_le_mul hx2 hsx hsq.le hx0.le)
      _ = 2 / Real.sqrt lam * (1 / ((1 + j : ℕ) : ℝ)) := by
          push_cast; field_simp; ring
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  have hh : ∑ j ∈ range J, (1 / ((1 + j : ℕ) : ℝ)) ≤ 1 + Real.log (J + 1) := by
    have h1 := sum_inv_le_log (J + 1) (Ico 1 (J + 1)) (fun k hk => by simp only [mem_Ico] at hk; omega)
    rw [sum_Ico_eq_sum_range] at h1
    simp only [Nat.add_sub_cancel] at h1
    push_cast at h1 ⊢
    exact h1
  calc 2 / Real.sqrt lam * ∑ j ∈ range J, (1 / ((1 + j : ℕ) : ℝ))
      ≤ 2 / Real.sqrt lam * (1 + Real.log (J + 1)) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

/-- `(L^{1/3} ℓ^{4/3})² = L^{2/3} ℓ^{8/3}`. -/
lemma s_sq (L ℓ : ℝ) (hL : 0 ≤ L) (hℓ : 0 ≤ ℓ) :
    (L ^ (1 / 3 : ℝ) * ℓ ^ (4 / 3 : ℝ)) ^ 2 = L ^ (2 / 3 : ℝ) * ℓ ^ (8 / 3 : ℝ) := by
  rw [mul_pow, ← Real.rpow_mul_natCast hL, ← Real.rpow_mul_natCast hℓ]
  norm_num

/-- `(L^{1/3} ℓ^{4/3})³ = L ℓ⁴`. -/
lemma s_cube (L ℓ : ℝ) (hL : 0 ≤ L) (hℓ : 0 ≤ ℓ) :
    (L ^ (1 / 3 : ℝ) * ℓ ^ (4 / 3 : ℝ)) ^ 3 = L * ℓ ^ 4 := by
  rw [mul_pow, ← Real.rpow_mul_natCast hL, ← Real.rpow_mul_natCast hℓ]
  norm_num

/-- The real inequalities (in `L = log p`) used for the side conditions of Theorem C. -/
def GoodC (γ₁ A' L₀ L : ℝ) : Prop :=
  max L₀ 1000 ≤ L ∧ L ^ γ₁ + 2 + 2 * Real.log L ≤ L - 1 ∧ Real.log L ≤ L ^ γ₁ ∧
    7 * L ^ γ₁ ≤ L ^ (2 / 3 : ℝ) ∧ A' * L ^ (3 / 4 : ℝ) + 1 ≤ L / 2 ∧
    Real.log L ≤ L ^ (1 / 32 : ℝ) ∧ 4 ≤ L ^ (2 / 3 : ℝ) ∧ 32 * Real.log L ≤ γ₁ * L ^ γ₁ ∧
    4 * Real.log L + 3 ≤ L / 4

lemma eventually_goodC (γ₁ A' L₀ : ℝ) (hγ : 0 < γ₁) (hγ1 : γ₁ < 2 / 3) :
    ∀ᶠ L : ℝ in atTop, GoodC γ₁ A' L₀ L := by
  have a1 := ev_rpow_le 4 (show γ₁ < 1 by linarith)
  have a2 := ev_log_pow_le 1 8 (show (0 : ℝ) < 1 by norm_num)
  have a3 := ev_log_pow_le 1 1 hγ
  have a4 := ev_rpow_le 7 hγ1
  have a5 := ev_rpow_le (4 * A') (show (3 / 4 : ℝ) < 1 by norm_num)
  have a6 := ev_log_pow_le 1 1 (show (0 : ℝ) < 1 / 32 by norm_num)
  have a7 := ev_rpow_le 4 (show (0 : ℝ) < 2 / 3 by norm_num)
  have a8 := ev_log_pow_le 1 (32 / γ₁) hγ
  have a9 := ev_log_pow_le 1 32 (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [a1, a2, a3, a4, a5, a6, a7, a8, a9, eventually_ge_atTop (max L₀ 1000),
    eventually_ge_atTop (0 : ℝ)] with L h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp only [pow_one, Real.rpow_one, Real.rpow_zero, mul_one, one_mul] at h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hL : 1000 ≤ L := le_trans (le_max_right _ _) h10
  have h8' : 32 * Real.log L ≤ γ₁ * L ^ γ₁ := by
    have := mul_le_mul_of_nonneg_left h8 hγ.le
    rw [← mul_assoc, mul_div_cancel₀ _ hγ.ne'] at this
    exact this
  refine ⟨h10, by linarith, h3, h4, by linarith, h6, h7, h8', by linarith⟩

/-- The tail term of `tails_sum_explicit` is at most `1`. -/
lemma tail_small (γ₁ L P M I : ℝ) (hL : 1 ≤ L) (h32 : 32 * Real.log L ≤ γ₁ * P)
    (hℓ1 : 1 ≤ Real.log L) (hM0 : 0 ≤ M) (hM : M ≤ 2 * L ^ 2) (hI0 : 0 ≤ I) (hIL : I ≤ 2 * L) :
    L / Real.pi * (2 * M * I * Real.exp (-(γ₁ * P / 4))) ≤ 1 := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hLpos : 0 < L := by linarith
  have hL4 : L ^ 4 * Real.exp 2 ≤ Real.exp (γ₁ * P / 4) := by
    have e4 : Real.exp (4 * Real.log L) = L ^ 4 := by
      rw [show (4 : ℝ) * Real.log L = Real.log (L ^ 4) by rw [Real.log_pow]; norm_num]
      exact Real.exp_log (by positivity)
    rw [← e4, ← Real.exp_add]
    apply Real.exp_le_exp.mpr; linarith
  have he2 : (7 : ℝ) ≤ Real.exp 2 := by
    have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have := Real.exp_one_gt_d9
    rw [e]; nlinarith
  have hE : 0 < Real.exp (γ₁ * P / 4) := Real.exp_pos _
  calc L / Real.pi * (2 * M * I * Real.exp (-(γ₁ * P / 4)))
      ≤ L / Real.pi * (2 * (2 * L ^ 2) * (2 * L) * Real.exp (-(γ₁ * P / 4))) := by
        gcongr
    _ = 8 / Real.pi * (L ^ 4 / Real.exp (γ₁ * P / 4)) := by
        rw [Real.exp_neg]; field_simp; ring
    _ ≤ 1 := by
        rw [div_mul_eq_mul_div, div_le_one hpi]
        have : L ^ 4 / Real.exp (γ₁ * P / 4) ≤ 1 / 7 := by
          rw [div_le_iff₀ hE]
          have : L ^ 4 * 7 ≤ L ^ 4 * Real.exp 2 := mul_le_mul_of_nonneg_left he2 (by positivity)
          linarith
        linarith

/-- The right-hand side of `R_boundG`, with the parameters of Theorem C, is `O(P² s²)`. -/
lemma rhsC_le (A' C' L ℓ P s lN lKs lK Hs Sig M tl : ℝ)
    (hL : 1000 ≤ L) (hℓ1 : 1 ≤ ℓ) (hP1 : 1 ≤ P) (hPL : P ≤ L) (hlP : ℓ ≤ P) (hs0 : 0 < s)
    (hs4 : 4 ≤ s ^ 2) (hs3 : s ^ 3 = L * ℓ ^ 4) (hA' : 1 ≤ A') (hC' : 0 ≤ C')
    (hlN0 : 0 ≤ lN) (hN7 : 2 + lN ≤ 7 * P) (hlKs0 : 0 ≤ 1 + lKs) (hlKs : 1 + lKs ≤ (A' + 1) * s ^ 2)
    (hlK0 : 0 ≤ 1 + lK) (hlK : lK ≤ L) (hM : L ^ 2 ≤ M + 1)
    (hHs0 : 0 ≤ Hs + 4) (hHs : Hs + 4 ≤ 12 * ℓ) (hSig0 : 0 ≤ Sig) (hSig : Sig ≤ 16 * ℓ / s)
    (htl : tl ≤ 1) :
    2 / Real.pi * (2 + lN) * (1 + lKs) + 2 / (M + 1) * (2 / Real.pi * (2 + lN) * (1 + lK)) +
      (Hs + 4) * (16 / Real.pi * (2 + lN) * (C' * (ℓ ^ 3 * L) * Sig)) +
      (2 * Real.pi * (1 + 1 / L) + tl) ≤
      (7 * (A' + 1) + 28 + 8064 * C' + 14) * (P ^ 2 * s ^ 2) := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hLpos : 0 < L := by linarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  have h2N0 : 0 ≤ 2 + lN := by linarith
  have h2pi : 2 / Real.pi ≤ 1 := by rw [div_le_one hpi]; linarith
  have hPP : P ≤ P ^ 2 := le_self_pow₀ hP1 (by norm_num)
  have hP2s2 : 1 ≤ P ^ 2 * s ^ 2 := by
    have : 1 ≤ P ^ 2 := one_le_pow₀ hP1
    nlinarith
  have t1 : 2 / Real.pi * (2 + lN) * (1 + lKs) ≤ 7 * (A' + 1) * (P ^ 2 * s ^ 2) := by
    calc 2 / Real.pi * (2 + lN) * (1 + lKs)
        ≤ 1 * (7 * P) * ((A' + 1) * s ^ 2) :=
          mul_le_mul (mul_le_mul h2pi hN7 h2N0 (by norm_num)) hlKs hlKs0 (by positivity)
      _ = 7 * (A' + 1) * (P * s ^ 2) := by ring
      _ ≤ 7 * (A' + 1) * (P ^ 2 * s ^ 2) := by gcongr
  have t2 : 2 / (M + 1) * (2 / Real.pi * (2 + lN) * (1 + lK)) ≤ 28 * (P ^ 2 * s ^ 2) := by
    have hN7L : 2 + lN ≤ 7 * L := by linarith
    have hK2L : 1 + lK ≤ 2 * L := by linarith
    calc 2 / (M + 1) * (2 / Real.pi * (2 + lN) * (1 + lK))
        ≤ 2 / L ^ 2 * (1 * (7 * L) * (2 * L)) :=
          mul_le_mul (div_le_div_of_nonneg_left (by norm_num) (by positivity) hM)
            (mul_le_mul (mul_le_mul h2pi hN7L h2N0 (by norm_num)) hK2L hlK0 (by positivity))
            (mul_nonneg (mul_nonneg (by positivity) h2N0) hlK0) (by positivity)
      _ = 28 := by field_simp; ring
      _ ≤ 28 * (P ^ 2 * s ^ 2) := by linarith
  have h16 : 16 / Real.pi ≤ 6 := by rw [div_le_iff₀ hpi]; linarith
  have t3 : (Hs + 4) * (16 / Real.pi * (2 + lN) * (C' * (ℓ ^ 3 * L) * Sig)) ≤
      8064 * C' * (P ^ 2 * s ^ 2) := by
    calc (Hs + 4) * (16 / Real.pi * (2 + lN) * (C' * (ℓ ^ 3 * L) * Sig))
        ≤ (12 * ℓ) * (6 * (7 * P) * (C' * (ℓ ^ 3 * L) * (16 * ℓ / s))) :=
          mul_le_mul hHs
            (mul_le_mul (mul_le_mul h16 hN7 h2N0 (by norm_num))
              (mul_le_mul_of_nonneg_left hSig (by positivity)) (mul_nonneg (by positivity) hSig0)
              (by positivity))
            (mul_nonneg (mul_nonneg (by positivity) h2N0) (mul_nonneg (by positivity) hSig0))
            (by positivity)
      _ = 8064 * C' * P * ℓ * ((L * ℓ ^ 4) / s) := by ring
      _ = 8064 * C' * P * ℓ * s ^ 2 := by
          rw [← hs3, pow_succ, mul_div_assoc, div_self hs0.ne', mul_one]
      _ ≤ 8064 * C' * P * P * s ^ 2 := by gcongr
      _ = 8064 * C' * (P ^ 2 * s ^ 2) := by ring
  have t4 : 2 * Real.pi * (1 + 1 / L) + tl ≤ 14 * (P ^ 2 * s ^ 2) := by
    have : 1 / L ≤ 1 := by rw [div_le_one hLpos]; linarith
    have := mul_le_mul_of_nonneg_left (by linarith : 1 + 1 / L ≤ 2)
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    have hpi4 := Real.pi_lt_d2
    linarith
  refine (add_le_add (add_le_add (add_le_add t1 t2) t3) t4).trans (le_of_eq ?_)
  ring

set_option maxHeartbeats 2000000 in
/-- **The bound for `R_K(p)`, `K = KW34 p`**, from (HBGfull):
`|R_K(p)| ≤ C₂ (log p)^{2/3+γ₀} (log log p)^{8/3}` for all large primes. -/
theorem R_thmC (hBG : HBGfull) {γ₀ : ℝ} (hγ : 0 < γ₀) (hγ1 : γ₀ < 2 / 3) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ᶠ p : ℕ in Filter.atTop, p.Prime →
      1 ≤ Real.log p ^ (2 / 3 + γ₀) * Real.log (Real.log p) ^ (8 / 3 : ℝ) ∧
      |RsumK (KW34 p) p| ≤
        C₂ * (Real.log p ^ (2 / 3 + γ₀) * Real.log (Real.log p) ^ (8 / 3 : ℝ)) := by
  obtain ⟨C, A, hC⟩ := hBG
  set γ₁ := γ₀ / 2 with hγ₁def
  have hγ₁ : 0 < γ₁ := by positivity
  have hγ₁1 : γ₁ < 2 / 3 := by linarith
  set C' := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  set A' := max A 0 + 1
  have hA'1 : 1 ≤ A' := by have := le_max_right A 0; linarith
  have hAA : A + 1 ≤ A' := by have := le_max_left A 0; linarith
  obtain ⟨L₀, hL₀⟩ := tails_sum_explicit (γ₀ := γ₁) hγ₁ (by linarith)
  refine ⟨7 * (A' + 1) + 28 + 8064 * C' + 14, by positivity, ?_⟩
  have hlogt : Tendsto (fun p : ℕ => Real.log p) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev := hlogt.eventually (eventually_goodC γ₁ A' L₀ hγ₁ hγ₁1)
  filter_upwards [hev, hC] with p hG hBGp hp
  obtain ⟨hL0, hR1, hlP, hR4, hR5, hl32, hL23, hR6, hR2⟩ := hG
  have hBGp := hBGp hp
  set L := Real.log p with hLdef
  set ℓ := Real.log L with hℓdef
  set P := L ^ γ₁ with hPdef
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hL1000 : 1000 ≤ L := le_trans (le_max_right _ _) hL0
  have hLL₀ : L₀ ≤ L := le_trans (le_max_left _ _) hL0
  have hLpos : 0 < L := by linarith
  have hL2 : 1000 * L ≤ L ^ 2 := by rw [sq]; exact mul_le_mul_of_nonneg_right hL1000 hLpos.le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpL : (p : ℝ) = Real.exp L := (Real.exp_log hp0).symm
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓdef, Real.le_log_iff_exp_le hLpos]
    have := Real.exp_one_lt_d9; linarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hP1 : 1 ≤ P := Real.one_le_rpow (by linarith) hγ₁.le
  have heL : (100 : ℝ) ≤ Real.exp L := by
    have := Real.add_one_le_exp L; linarith
  have hp5 : 5 ≤ p := by
    have : (5 : ℝ) ≤ p := by rw [hpL]; linarith
    exact_mod_cast this
  have hp2 : p ≠ 2 := by omega
  -- `s = L^{1/3} ℓ^{4/3}`
  set s := L ^ (1 / 3 : ℝ) * ℓ ^ (4 / 3 : ℝ) with hsdef
  have hs0 : 0 < s := by positivity
  have hs2 : s ^ 2 = L ^ (2 / 3 : ℝ) * ℓ ^ (8 / 3 : ℝ) := s_sq L ℓ hLpos.le hℓ0
  have hs3 : s ^ 3 = L * ℓ ^ 4 := s_cube L ℓ hLpos.le hℓ0
  have hℓ83 : 1 ≤ ℓ ^ (8 / 3 : ℝ) := Real.one_le_rpow hℓ1 (by norm_num)
  have hs2ge : L ^ (2 / 3 : ℝ) ≤ s ^ 2 := by
    rw [hs2]; exact le_mul_of_one_le_right (by positivity) hℓ83
  have hs2le : s ^ 2 ≤ L ^ (3 / 4 : ℝ) := by
    rw [hs2]
    have h1 : ℓ ^ (8 / 3 : ℝ) ≤ L ^ (1 / 12 : ℝ) := by
      calc ℓ ^ (8 / 3 : ℝ) ≤ (L ^ (1 / 32 : ℝ)) ^ (8 / 3 : ℝ) :=
            Real.rpow_le_rpow hℓ0 hl32 (by norm_num)
        _ = L ^ (1 / 12 : ℝ) := by rw [← Real.rpow_mul hLpos.le]; norm_num
    calc L ^ (2 / 3 : ℝ) * ℓ ^ (8 / 3 : ℝ) ≤ L ^ (2 / 3 : ℝ) * L ^ (1 / 12 : ℝ) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = L ^ (3 / 4 : ℝ) := by rw [← Real.rpow_add hLpos]; norm_num
  have hs4 : 4 ≤ s ^ 2 := hL23.trans hs2ge
  have htarget : L ^ (2 / 3 + γ₀) * ℓ ^ (8 / 3 : ℝ) = P ^ 2 * s ^ 2 := by
    rw [hs2, hPdef, ← Real.rpow_mul_natCast hLpos.le, Real.rpow_add hLpos]
    rw [show γ₁ * ((2 : ℕ) : ℝ) = γ₀ by rw [hγ₁def]; push_cast; ring]
    ring
  rw [htarget]
  have hP2s2 : 1 ≤ P ^ 2 * s ^ 2 := by
    have : 1 ≤ P ^ 2 := one_le_pow₀ hP1
    nlinarith
  refine ⟨hP2s2, ?_⟩
  -- `T`
  set T := Real.exp P with hTdef
  have hT2 : 2 ≤ T := by
    have := Real.add_one_le_exp P; linarith
  have hT0 : 0 < T := Real.exp_pos _
  have hlogL2 : Real.log (L ^ 2 + 2) ≤ 2 + 2 * ℓ := by
    have h1 : L ^ 2 + 2 ≤ Real.exp 2 * L ^ 2 := by
      have : (2 : ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp (2 : ℝ); linarith
      have := mul_le_mul_of_nonneg_right this (sq_nonneg L)
      linarith
    calc Real.log (L ^ 2 + 2) ≤ Real.log (Real.exp 2 * L ^ 2) := Real.log_le_log (by positivity) h1
      _ = 2 + 2 * ℓ := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow]; push_cast; ring
  have hTL : T * (L ^ 2 + 2) ≤ Real.exp (P + 2 + 2 * ℓ) := by
    rw [show P + 2 + 2 * ℓ = P + (2 + 2 * ℓ) by ring, Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hT0.le
    calc L ^ 2 + 2 = Real.exp (Real.log (L ^ 2 + 2)) := (Real.exp_log (by positivity)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlogL2
  have hTLp : T * (L ^ 2 + 2) ≤ Real.exp (L - 1) := hTL.trans (Real.exp_le_exp.mpr hR1)
  have hexpL1 : Real.exp (L - 1) * 2 ≤ Real.exp L := by
    rw [show L = (L - 1) + 1 by ring, Real.exp_add]; simp only [add_sub_cancel_right]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have := Real.add_one_le_exp (1 : ℝ); linarith
  -- `M`, `N`, `H = M`
  set M := ⌈L ^ 2⌉₊
  have hM1 : L ^ 2 ≤ M := Nat.le_ceil _
  have hM2 : (M : ℝ) < L ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  set N := ⌈T * M⌉₊
  have hN1 : T * M ≤ N := Nat.le_ceil _
  have hN2 : (N : ℝ) < T * M + 1 := Nat.ceil_lt_add_one (by positivity)
  have hTM : T * M ≤ T * (L ^ 2 + 1) := mul_le_mul_of_nonneg_left hM2.le hT0.le
  have h2M : 2 * (M : ℝ) ≤ T * M := mul_le_mul_of_nonneg_right hT2 (Nat.cast_nonneg M)
  have hNTL : (N : ℝ) ≤ T * (L ^ 2 + 2) := by linarith
  have hNp : N < p := by
    have : (N : ℝ) < p := by rw [hpL]; linarith [Real.exp_pos (L - 1)]
    exact_mod_cast this
  have hM1' : 1 ≤ M := by
    have : (1 : ℝ) ≤ M := by linarith
    exact_mod_cast this
  have hMN : M ≤ N := by
    have : (M : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hN2' : 2 ≤ N := by
    have : (2 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hMp : M < p := lt_of_le_of_lt hMN hNp
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogN : Real.log N ≤ P + 2 + 2 * ℓ := by
    rw [Real.log_le_iff_le_exp hNpos]; exact hNTL.trans hTL
  -- `K_*`
  have hAs : s ^ 2 ≤ A' * s ^ 2 := le_mul_of_one_le_left (by positivity) hA'1
  set E := Real.exp (A' * s ^ 2) with hEdef
  set Ks := ⌈E⌉₊
  have hKs1 : E ≤ Ks := Nat.le_ceil _
  have hKs2 : (Ks : ℝ) < E + 1 := Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hE4 : (6 : ℝ) ≤ E := six_le_exp (by linarith)
  have hKs6 : 6 ≤ Ks := by
    have : (6 : ℝ) ≤ Ks := hE4.trans hKs1
    exact_mod_cast this
  have h7P : P + 2 * ℓ + 4 ≤ A' * s ^ 2 := by
    have : 7 * P ≤ s ^ 2 := hR4.trans hs2ge
    linarith
  have h3TL : 3 * (T * (L ^ 2 + 2)) ≤ E := by
    calc 3 * (T * (L ^ 2 + 2)) ≤ Real.exp 2 * Real.exp (P + 2 + 2 * ℓ) := by
          apply mul_le_mul _ hTL (by positivity) (Real.exp_pos _).le
          have := Real.add_one_le_exp (2 : ℝ); linarith
      _ = Real.exp (P + 2 * ℓ + 4) := by rw [← Real.exp_add]; ring_nf
      _ ≤ E := Real.exp_le_exp.mpr h7P
  have hNKs : 2 * N + 1 ≤ Ks := by
    have : ((2 * N + 1 : ℕ) : ℝ) ≤ Ks := by
      push_cast
      have := mul_le_mul_of_nonneg_right hT2 (by positivity : (0 : ℝ) ≤ L ^ 2 + 2)
      linarith
    exact_mod_cast this
  -- `K = KW34 p`
  set V := Real.exp (L * (3 / 4)) * L ^ 4
  have hKWe : KW34 p = ⌊V⌋₊ := by
    show KWθ (3 / 4) p = _
    unfold KWθ; rw [hpL, ← Real.exp_mul, Real.log_exp]
  have hV0 : 0 ≤ V := by positivity
  have hK1 : (KW34 p : ℝ) ≤ V := by rw [hKWe]; exact Nat.floor_le hV0
  have hK2 : V < KW34 p + 1 := by rw [hKWe]; exact Nat.lt_floor_add_one V
  have hEL2 : Real.exp (L / 2) ≤ V :=
    (Real.exp_le_exp.mpr (by linarith)).trans
      (le_mul_of_one_le_right (Real.exp_pos _).le (one_le_pow₀ (by linarith)))
  have hVbig : 2 ≤ V := by
    have := Real.add_one_le_exp (L / 2); linarith
  have hV20 : V * 20 ≤ Real.exp L := by
    have h1 : V = Real.exp (L * (3 / 4) + 4 * ℓ) := by
      rw [Real.exp_add, show (4 : ℝ) * ℓ = Real.log (L ^ 4) by rw [Real.log_pow, ← hℓdef]; norm_num,
        Real.exp_log (pow_pos hLpos 4)]
    have h2 : Real.exp (L * (3 / 4) + 4 * ℓ) * Real.exp 3 ≤ Real.exp L := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    rw [h1]
    exact (mul_le_mul_of_nonneg_left exp_three_ge (Real.exp_pos _).le).trans h2
  have hKpos' : (0 : ℝ) < KW34 p := by linarith
  have hKp : KW34 p ≤ p := by
    have : (KW34 p : ℝ) ≤ p := by rw [hpL]; linarith
    exact_mod_cast this
  have hK2p : 2 * KW34 p < p := by
    have : ((2 * KW34 p : ℕ) : ℝ) < p := by push_cast; rw [hpL]; linarith
    exact_mod_cast this
  have hKsK : Ks ≤ KW34 p := by
    have hAL : A' * s ^ 2 + 1 ≤ L / 2 := by
      have := mul_le_mul_of_nonneg_left hs2le (by linarith : (0 : ℝ) ≤ A'); linarith
    have h2E : E * 2 ≤ Real.exp (L / 2) := by
      calc E * 2 ≤ E * Real.exp 1 := by
            apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
            have := Real.add_one_le_exp (1 : ℝ); linarith
        _ = Real.exp (A' * s ^ 2 + 1) := by rw [Real.exp_add]
        _ ≤ Real.exp (L / 2) := Real.exp_le_exp.mpr hAL
    have : (Ks : ℝ) < KW34 p + 1 := by linarith
    have : Ks < KW34 p + 1 := by exact_mod_cast this
    omega
  -- the Bourgain–Garaev threshold
  set E₀ := Real.exp (A * L ^ (2 / 3 : ℝ) * ℓ ^ (8 / 3 : ℝ))
  have hE₀ : E₀ ≤ (Ks : ℝ) / 3 := by
    have e : A * L ^ (2 / 3 : ℝ) * ℓ ^ (8 / 3 : ℝ) = A * s ^ 2 := by rw [hs2]; ring
    rw [le_div_iff₀ (by norm_num)]
    calc E₀ * 3 ≤ Real.exp (A * s ^ 2) * Real.exp (s ^ 2) := by
          simp only [E₀]; rw [e]
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          have := Real.add_one_le_exp (s ^ 2); linarith
      _ = Real.exp ((A + 1) * s ^ 2) := by rw [← Real.exp_add]; ring_nf
      _ ≤ E := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hAA (by positivity))
      _ ≤ Ks := hKs1
  -- `J`
  set J := ⌈2 * L⌉₊
  have hJ1 : 2 * L ≤ J := Nat.le_ceil _
  have hJ2 : (J : ℝ) < 2 * L + 1 := Nat.ceil_lt_add_one (by positivity)
  have hKJ : KW34 p ≤ 2 ^ J * Ks := by
    have h1 : Real.exp L ≤ (2 : ℝ) ^ J := by
      have : Real.exp L ≤ Real.exp (J * Real.log 2) := by
        apply Real.exp_le_exp.mpr
        have h1 := mul_le_mul_of_nonneg_right hJ1 (Real.log_pos one_lt_two).le
        have h2 := mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le hLpos.le
        linarith
      rw [show Real.exp (J * Real.log 2) = (2 : ℝ) ^ J by
        rw [← Real.log_pow, Real.exp_log (by positivity)]] at this
      exact this
    have : (KW34 p : ℝ) ≤ 2 ^ J * Ks := by
      have hKs1' : (1 : ℝ) ≤ Ks := by exact_mod_cast (by omega : 1 ≤ Ks)
      have : (KW34 p : ℝ) ≤ Real.exp L := by rw [← hpL]; exact_mod_cast hKp
      have := le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ 2 ^ J) hKs1'
      linarith
    exact_mod_cast this
  -- `I`
  set I := Nat.log 2 (KW34 p) + 1
  have hKpos : 0 < KW34 p := by exact_mod_cast hKpos'
  have hI1 : KW34 p < 2 ^ I := Nat.lt_pow_succ_log_self (by norm_num) _
  have hI2 : 2 ^ (I - 1) ≤ KW34 p := by
    simp only [I, Nat.add_sub_cancel]; exact Nat.pow_log_le_self 2 hKpos.ne'
  have hIL : (I : ℝ) ≤ 2 * L := by
    have h1 : ((I - 1 : ℕ) : ℝ) * Real.log 2 ≤ L := by
      rw [← Real.log_pow]
      have : ((2 : ℝ) ^ (I - 1)) ≤ Real.exp L := by
        rw [← hpL]; have : (2 : ℝ) ^ (I - 1) ≤ KW34 p := by exact_mod_cast hI2
        have : (KW34 p : ℝ) ≤ p := by exact_mod_cast hKp
        linarith
      calc Real.log ((2 : ℝ) ^ (I - 1)) ≤ Real.log (Real.exp L) := Real.log_le_log (by positivity) this
        _ = L := Real.log_exp L
    have hI1' : ((I - 1 : ℕ) : ℝ) = I - 1 := by
      rw [Nat.cast_sub (by simp only [I]; omega)]; simp
    rw [hI1'] at h1
    have hI0 : (0 : ℝ) ≤ I - 1 := by rw [← hI1']; exact Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le hI0
    linarith
  -- the tails
  have hTI : (KW34 p : ℝ) ≤ T * 2 ^ I := by
    have : (KW34 p : ℝ) ≤ 2 ^ I := by exact_mod_cast hI1.le
    have := le_mul_of_one_le_left (by positivity : (0 : ℝ) ≤ 2 ^ I) (by linarith : (1 : ℝ) ≤ T)
    linarith
  have hpI : (p : ℝ) * 2 ^ I + M ≤ (p : ℝ) ^ 2 := by
    have hI2' : (2 : ℝ) ^ I ≤ 2 * KW34 p := by
      have : 2 ^ I ≤ 2 * KW34 p := by
        have e : I = (I - 1) + 1 := by simp only [I]; omega
        rw [e, pow_succ]; omega
      exact_mod_cast this
    have hK8 : (KW34 p : ℝ) * 8 ≤ p := by rw [hpL]; linarith
    have hMp' : (M : ℝ) ≤ p := by exact_mod_cast hMp.le
    have hp4 : (4 : ℝ) ≤ p := by exact_mod_cast (by omega : 4 ≤ p)
    have h1 := mul_le_mul_of_nonneg_left (by linarith : (2 : ℝ) ^ I ≤ p / 4) hp0.le
    have h2 := mul_le_mul_of_nonneg_right hp4 hp0.le
    linarith
  have hdiv : ∀ k ∈ (Ioo (N + 1) (KW34 p)).filter Odd, (k : ℤ) ∣ 2 * p * uInv p k - 1 := by
    intro k hk
    simp only [mem_filter, mem_Ioo] at hk
    apply uInv_spec p k (by omega)
    have hcop : Nat.Coprime p k := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]; intro h; have := Nat.le_of_dvd (by omega) h; omega
    exact Nat.coprime_mul_iff_left.mpr ⟨Nat.coprime_two_left.mpr hk.2, hcop⟩
  have htail := hL₀ p hp hLL₀ M N (KW34 p) I (uInv p) hM1' hMN hN2' hMp hT2 hTI hpI hM1 hN1 hKp hdiv
  -- the Bourgain–Garaev input with `C' = max C 0`
  have hBG' : ∀ b : ZMod p, b ≠ 0 → ∀ N' : ℕ, E₀ ≤ N' → N' < p → ‖Tsum p b N'‖ ≤ bgB C' p N' := by
    intro b hb N' hN' hN'p
    refine (hBGp b hb N' hN' hN'p).trans ?_
    unfold bgB
    have hlN' : 0 ≤ Real.log N' := Real.log_natCast_nonneg N'
    have hY : 0 ≤ ℓ ^ 3 * L * Real.log N' ^ (-(3 / 2 : ℝ)) * N' := by positivity
    have e1 : C * ℓ ^ 3 * L * Real.log N' ^ (-(3 / 2 : ℝ)) * N' =
        C * (ℓ ^ 3 * L * Real.log N' ^ (-(3 / 2 : ℝ)) * N') := by ring
    have e2 : C' * ℓ ^ 3 * L * Real.log N' ^ (-(3 / 2 : ℝ)) * N' =
        C' * (ℓ ^ 3 * L * Real.log N' ^ (-(3 / 2 : ℝ)) * N') := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hY
  have hRb := R_boundG hV_holds C' hC' p hp hp5 E₀ hBG' (KW34 p) N M Ks J (by omega) hM1' hMp hNp
    hKs6 hNKs hKsK hK2p hE₀ hKJ _ htail
  -- the dyadic sum
  have hKs0 : (0 : ℝ) < Ks := by exact_mod_cast (by omega : 0 < Ks)
  have hlogKs1 : A' * s ^ 2 ≤ Real.log (Ks : ℝ) := by
    rw [Real.le_log_iff_exp_le hKs0, ← hEdef]; exact hKs1
  have hlam : s ^ 2 / 2 ≤ Real.log ((Ks : ℝ) / 3) := by
    rw [Real.log_div hKs0.ne' (by norm_num)]
    have := log_three_lt
    linarith
  have hsum := sum_dyadic_pow Ks J (by linarith)
  have hsqrt : s / 2 ≤ Real.sqrt (Real.log ((Ks : ℝ) / 3)) := by
    rw [Real.le_sqrt (by positivity) (by linarith)]
    nlinarith
  have hJl : 1 + Real.log ((J : ℝ) + 1) ≤ 4 * ℓ := by
    have hJ0 : (0 : ℝ) < J + 1 := by positivity
    have h1 : Real.log ((J : ℝ) + 1) ≤ Real.log (3 * L) :=
      Real.log_le_log hJ0 (by linarith)
    rw [Real.log_mul (by norm_num) hLpos.ne'] at h1
    have := log_three_lt
    linarith
  have hSig : ∑ j ∈ range J, Real.log (((2 ^ j * Ks : ℕ) : ℝ) / 3) ^ (-(3 / 2 : ℝ)) ≤ 16 * ℓ / s := by
    refine hsum.trans ?_
    have hq : 0 < Real.sqrt (Real.log ((Ks : ℝ) / 3)) := by linarith
    calc 2 * (1 + Real.log ((J : ℝ) + 1)) / Real.sqrt (Real.log ((Ks : ℝ) / 3))
        ≤ 2 * (4 * ℓ) / Real.sqrt (Real.log ((Ks : ℝ) / 3)) :=
          div_le_div_of_nonneg_right (by linarith) hq.le
      _ ≤ 2 * (4 * ℓ) / (s / 2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hsqrt
      _ = 16 * ℓ / s := by field_simp; ring
  have hSig0 : 0 ≤ ∑ j ∈ range J, Real.log (((2 ^ j * Ks : ℕ) : ℝ) / 3) ^ (-(3 / 2 : ℝ)) := by
    apply sum_nonneg; intro j _
    apply Real.rpow_nonneg
    apply Real.log_nonneg
    have : (6 : ℝ) ≤ ((2 ^ j * Ks : ℕ) : ℝ) := by
      exact_mod_cast le_trans hKs6 (Nat.le_mul_of_pos_left Ks (by positivity))
    rw [le_div_iff₀ (by norm_num)]; linarith
  -- bounding the four terms
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have hN7 : 2 + Real.log N ≤ 7 * P := by linarith
  have hlKs : 1 + Real.log (Ks : ℝ) ≤ (A' + 1) * s ^ 2 := by
    have : Real.log (Ks : ℝ) ≤ A' * s ^ 2 + 1 := by
      rw [Real.log_le_iff_le_exp hKs0, Real.exp_add, ← hEdef]
      have : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
      have hE2 : E * 2 ≤ E * Real.exp 1 := mul_le_mul_of_nonneg_left this (by linarith)
      linarith
    have : s ^ 2 * 1 ≤ s ^ 2 * 2 := by linarith
    linarith
  have hlKs0 : 0 ≤ 1 + Real.log (Ks : ℝ) := by
    have := Real.log_natCast_nonneg Ks; linarith
  have hlK : Real.log (KW34 p : ℝ) ≤ L := by
    have := Real.log_le_log hKpos' (show (KW34 p : ℝ) ≤ p by exact_mod_cast hKp)
    rwa [← hLdef] at this
  have hlK0 : 0 ≤ 1 + Real.log (KW34 p : ℝ) := by
    have := Real.log_natCast_nonneg (KW34 p); linarith
  have hPL : P ≤ L := by linarith
  have hML : L ^ 2 ≤ (M : ℝ) + 1 := by linarith
  have hHs0 : 0 ≤ ∑ h ∈ Icc 1 M, 4 / (Real.pi * h) + 4 := by
    have : 0 ≤ ∑ h ∈ Icc 1 M, 4 / (Real.pi * h) := sum_nonneg (fun h _ => by positivity)
    linarith
  have hHs : ∑ h ∈ Icc 1 M, 4 / (Real.pi * h) + 4 ≤ 12 * ℓ := by
    have hHsum : ∑ h ∈ Icc 1 M, 4 / (Real.pi * h) = 4 / Real.pi * ∑ h ∈ Icc 1 M, (1 / h : ℝ) := by
      rw [mul_sum]; apply sum_congr rfl; intro h _; rw [mul_one_div, div_div]
    rw [hHsum]
    have h1 := sum_inv_le_log (M + 1) (Icc 1 M) (fun k hk => by simp only [mem_Icc] at hk; omega)
    push_cast at h1
    have h2 : Real.log ((M : ℝ) + 1) ≤ Real.log 2 + 2 * ℓ := by
      rw [hℓdef, ← Real.log_rpow (by linarith), ← Real.log_mul (by norm_num) (by positivity)]
      apply Real.log_le_log (by positivity)
      rw [show L ^ (2 : ℝ) = L ^ 2 by norm_cast]
      linarith
    have h3 := Real.log_two_lt_d9
    have hs0 : 0 ≤ ∑ h ∈ Icc 1 M, (1 / h : ℝ) := sum_nonneg (fun h _ => by positivity)
    have h5 : 4 / Real.pi ≤ 4 / 3 := by gcongr
    have h6 : 4 / Real.pi * ∑ h ∈ Icc 1 M, (1 / h : ℝ) ≤ 4 / 3 * ∑ h ∈ Icc 1 M, (1 / h : ℝ) :=
      mul_le_mul_of_nonneg_right h5 hs0
    linarith
  have he : T ^ (-(γ₁ / 4)) = Real.exp (-(γ₁ * P / 4)) := by
    rw [hTdef, ← Real.exp_mul]; congr 1; ring
  have htl : L / Real.pi * (2 * M * I * T ^ (-(γ₁ / 4))) ≤ 1 := by
    rw [he]
    exact tail_small γ₁ L P M I (by linarith) hR6 hℓ1 (Nat.cast_nonneg _) (by linarith)
      (Nat.cast_nonneg _) hIL
  exact hRb.trans (rhsC_le A' C' L ℓ P s _ _ _ _ _ _ _ hL1000 hℓ1 hP1 hPL hlP hs0 hs4 hs3 hA'1 hC'
    hlogN0 hN7 hlKs0 hlKs hlK0 hlK hML hHs0 hHs hSig0 hSig htl)

/-- **Theorem C** of arXiv:2501.03234 (asymptotic formula), conditional on (HBGfull): for every
`0 < γ₀ < 2/3` there are `c, C` with
  `|S(p) - (p/2) log p - c p| ≤ C p (log p)^{2/3+γ₀} (log log p)^{8/3}` for all large primes `p`. -/
theorem theorem_C (hBGfull : HBGfull) : ∀ γ₀ : ℝ, 0 < γ₀ → γ₀ < 2 / 3 → ∃ c C : ℝ,
    ∀ᶠ p : ℕ in Filter.atTop, p.Prime →
      |(S p : ℝ) - p / 2 * Real.log p - c * p| ≤
        C * p * Real.log p ^ (2 / 3 + γ₀) * Real.log (Real.log p) ^ (8 / 3 : ℝ) := by
  intro γ₀ hγ hγ1
  obtain ⟨C₂, hC₂, hR⟩ := R_thmC hBGfull hγ hγ1
  obtain ⟨c, C₀, hB⟩ := hBweak34
  refine ⟨c, |C₀| + 4 / Real.pi * C₂, ?_⟩
  filter_upwards [hR, hB] with p hRp hBp hp
  obtain ⟨h1, h2⟩ := hRp hp
  have hB' := hBp hp
  set W := Real.log p ^ (2 / 3 + γ₀) * Real.log (Real.log p) ^ (8 / 3 : ℝ)
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hpi := Real.pi_pos
  set X := (S p : ℝ) - p / 2 * Real.log p - c * p
  set Y := 4 * (p : ℝ) / Real.pi * RsumK (KW34 p) p
  have hY : |Y| ≤ 4 * p / Real.pi * (C₂ * W) := by
    simp only [Y]
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hXY : |X - Y| ≤ C₀ * p := by simpa only [X, Y, RsumK] using hB'
  have htri : |X| ≤ |X - Y| + |Y| := by
    have := abs_sub_le X Y 0
    simpa only [sub_zero] using this
  have hC0 : C₀ * p ≤ |C₀| * p * W := by
    have h3 : C₀ * p ≤ |C₀| * p := mul_le_mul_of_nonneg_right (le_abs_self C₀) hp0
    have h4 : |C₀| * p ≤ |C₀| * p * W := le_mul_of_one_le_right (by positivity) h1
    linarith
  calc |X| ≤ |X - Y| + |Y| := htri
    _ ≤ |C₀| * p * W + 4 * p / Real.pi * (C₂ * W) := by linarith
    _ = (|C₀| + 4 / Real.pi * C₂) * p * W := by ring
    _ = _ := by simp only [W]; ring

end ThetaSum

#print axioms ThetaSum.R_thmC
#print axioms ThetaSum.theorem_C
