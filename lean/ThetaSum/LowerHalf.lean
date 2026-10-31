import ThetaSum.RBound
import ThetaSum.Asym2

/-!
# The lower half of Conjecture 3.3, from (HB), (HV), (HBG)

`lower_half : HB → HV → HBG → ∀ n, ∀ᶠ k in atTop, k.Prime → n·k < S k`,
with `S` the formal-conjectures definition (verbatim, `Hypotheses.lean`).

Parameters, with `L = log p`: `T = exp(L^{1/20})`, `M = H = ⌈L²⌉`, `N = ⌈T M⌉`,
`K_* = ⌈exp(L^{9/10})⌉`, `J = ⌈2L⌉`, `I = ⌊log₂ K_W⌋ + 1`.
-/

open Finset Filter

namespace ThetaSum

/-- The real inequalities (in `L = log p`) used to check all side conditions. -/
def Good2 (L₀ C' c L : ℝ) : Prop :=
  max L₀ 1000 ≤ L ∧ L ^ (1 / 20 : ℝ) + 2 + 2 * Real.log L ≤ L - 1 ∧ 4 * Real.log L + 3 ≤ L / 4 ∧
    L ^ (1 / 20 : ℝ) + 2 * Real.log L + 4 ≤ L ^ (9 / 10 : ℝ) ∧ L ^ (9 / 10 : ℝ) + 1 ≤ L / 2 ∧
    4 ≤ L ^ (9 / 10 : ℝ) ∧ 4 / Real.pi * Gb C' L + c < L / 2

lemma eventually_good2 (L₀ C' c : ℝ) (hC : 0 ≤ C') : ∀ᶠ L : ℝ in atTop, Good2 L₀ C' c L := by
  have a1 := ev_rpow_le 4 (show (1 / 20 : ℝ) < 1 by norm_num)
  have a2 := ev_log_pow_le 1 8 (show (0 : ℝ) < 1 by norm_num)
  have a3 := ev_log_pow_le 1 16 (show (0 : ℝ) < 1 by norm_num)
  have a4 := ev_rpow_le 3 (show (1 / 20 : ℝ) < 9 / 10 by norm_num)
  have a5 := ev_log_pow_le 1 6 (show (0 : ℝ) < 9 / 10 by norm_num)
  have a6 := ev_rpow_le 12 (show (0 : ℝ) < 9 / 10 by norm_num)
  have a7 := ev_rpow_le 4 (show (9 / 10 : ℝ) < 1 by norm_num)
  have a8 := ev_log_pow_le 1 32 (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [a1, a2, a3, a4, a5, a6, a7, Gb_small C' c hC, eventually_ge_atTop (max L₀ 1000), a8]
    with L h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp only [pow_one, Real.rpow_one, Real.rpow_zero, mul_one] at h1 h2 h3 h4 h5 h6 h7 h10
  have hL : 1000 ≤ L := le_trans (le_max_right _ _) h9
  refine ⟨h9, by linarith, by linarith, by linarith, by linarith, by linarith, h8⟩

lemma six_le_exp {x : ℝ} (hx : 4 ≤ x) : (6 : ℝ) ≤ Real.exp x := by
  have h1 : Real.exp 2 ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have := Real.exp_one_gt_d9
  nlinarith

lemma exp_three_ge : (20 : ℝ) ≤ Real.exp 3 := by
  have e : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have := Real.exp_one_gt_d9
  rw [e]; nlinarith

lemma log_three_lt : Real.log 3 < 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have := Real.exp_one_gt_d9
  rw [e]; nlinarith

/-- The right-hand side of `R_bound`, with the parameters of `lower_half`, is at most `Gb C' L`. -/
lemma rhs_le_Gb (C' L lN lKs H lK J Hs Y M I e : ℝ) (hC : 0 ≤ C') (hL : 1000 ≤ L)
    (hlN0 : 0 ≤ lN) (hlN : 2 + lN ≤ Aterm L) (hlKs0 : 0 ≤ 1 + lKs)
    (hlKs : 1 + lKs ≤ L ^ (9 / 10 : ℝ) + 2) (hH : L ^ 2 ≤ H) (hlK0 : 0 ≤ 1 + lK) (hlK : lK ≤ L)
    (hJ : J ≤ 2 * L + 1) (hHs0 : 0 ≤ Hs + 4) (hHs : Hs + 4 ≤ 8 + 4 * Real.log L)
    (hY0 : 0 ≤ Y) (hY : Y ≤ (L ^ (9 / 10 : ℝ) / 2) ^ (-(3 / 2 : ℝ)))
    (hM : M ≤ 2 * L ^ 2) (hI0 : 0 ≤ I) (hI : I ≤ 2 * L) (he0 : 0 ≤ e)
    (he : e ≤ Real.exp (-(L ^ (1 / 20 : ℝ) / 80))) :
    2 / Real.pi * (2 + lN) * (1 + lKs) + 2 / (H + 1) * (2 / Real.pi * (2 + lN) * (1 + lK)) +
      J * ((Hs + 4) * (16 / Real.pi * (2 + lN) * (C' * (Real.log L ^ 3 * L) * Y))) +
      2 * Real.pi * (1 + 1 / L) + L / Real.pi * (2 * M * I * e) ≤ Gb C' L := by
  have hpi := Real.pi_pos
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hL0 : 0 ≤ L := by linarith
  have hA : 0 ≤ Aterm L := by linarith
  have hA2 : 0 ≤ 2 / Real.pi * Aterm L := mul_nonneg (by positivity) hA
  have hA16 : 0 ≤ 16 / Real.pi * Aterm L := mul_nonneg (by positivity) hA
  have hX : 0 ≤ C' * (Real.log L ^ 3 * L) := by positivity
  have hHL : L ^ 2 ≤ H + 1 := by linarith
  have hL2 : 0 < L ^ 2 := by positivity
  have t1 : 2 / Real.pi * (2 + lN) * (1 + lKs) ≤ 2 / Real.pi * Aterm L * (L ^ (9 / 10 : ℝ) + 2) := by
    gcongr
  have t2 : 2 / (H + 1) * (2 / Real.pi * (2 + lN) * (1 + lK)) ≤
      2 / L ^ 2 * (2 / Real.pi * Aterm L * (1 + L)) := by
    gcongr
  have t3 : J * ((Hs + 4) * (16 / Real.pi * (2 + lN) * (C' * (Real.log L ^ 3 * L) * Y))) ≤
      (2 * L + 1) * ((8 + 4 * Real.log L) * (16 / Real.pi * Aterm L *
        (C' * (Real.log L ^ 3 * L) * (L ^ (9 / 10 : ℝ) / 2) ^ (-(3 / 2 : ℝ))))) := by
    gcongr
  have t5 : L / Real.pi * (2 * M * I * e) ≤
      L / Real.pi * (2 * (2 * L ^ 2) * (2 * L) * Real.exp (-(L ^ (1 / 20 : ℝ) / 80))) := by
    gcongr
  unfold Gb
  linarith

set_option maxHeartbeats 1000000 in
/-- **The lower half of Conjecture 3.3** with the cutoff `K = ⌊p^θ (log p)^4⌋`, `1/2 ≤ θ ≤ 3/4`,
conditional on the corresponding one-sided Theorem B, (HV) and (HBG). -/
theorem lower_half_gen (θ : ℝ) (hθ1 : 1 / 2 ≤ θ) (hθ2 : θ ≤ 3 / 4)
    (hB : ∃ C : ℝ, ∀ᶠ p : ℕ in Filter.atTop, p.Prime →
      (p : ℝ) / 2 * Real.log p + 4 * p / Real.pi * RsumK (KWθ θ p) p - C * p ≤ (S p : ℝ))
    (hV : HV) (hBG : HBG) :
    ∀ n : ℕ, ∀ᶠ k in Filter.atTop, k.Prime → (n : ℤ) * k < S k := by
  intro n
  obtain ⟨C1, hC1⟩ := hB
  obtain ⟨C, hC⟩ := hBG
  set C' := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  obtain ⟨L₀, hL₀⟩ := tails_sum_explicit (γ₀ := 1 / 20) (by norm_num) (by norm_num)
  have hlogt : Tendsto (fun p : ℕ => Real.log p) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev := hlogt.eventually (eventually_good2 L₀ C' (C1 + n) hC')
  filter_upwards [hev, hC1, hC] with p hG hS hBGp hp
  obtain ⟨hL0, hR1, hR2, hR4, hR5, hR3, hfin⟩ := hG
  have hS := hS hp
  have hBGp := hBGp hp
  set L := Real.log p with hLdef
  have hpi := Real.pi_pos
  have hL1000 : 1000 ≤ L := le_trans (le_max_right _ _) hL0
  have hLL₀ : L₀ ≤ L := le_trans (le_max_left _ _) hL0
  have hLpos : 0 < L := by linarith
  have hL2 : 1000 * L ≤ L ^ 2 := by rw [sq]; exact mul_le_mul_of_nonneg_right hL1000 hLpos.le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpL : (p : ℝ) = Real.exp L := (Real.exp_log hp0).symm
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have heL : (100 : ℝ) ≤ Real.exp L := by
    have := Real.add_one_le_exp L; linarith
  have hp5 : 5 ≤ p := by
    have : (5 : ℝ) ≤ p := by rw [hpL]; linarith
    exact_mod_cast this
  have hp2 : p ≠ 2 := by omega
  -- `T`
  set T := Real.exp (L ^ (1 / 20 : ℝ)) with hTdef
  have hT1 : 1 ≤ L ^ (1 / 20 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hT2 : 2 ≤ T := by
    have := Real.add_one_le_exp (L ^ (1 / 20 : ℝ)); linarith
  have hT0 : 0 < T := Real.exp_pos _
  -- `T (L² + 2) ≤ exp(L - 1)`
  have hlogL2 : Real.log (L ^ 2 + 2) ≤ 2 + 2 * Real.log L := by
    have h1 : L ^ 2 + 2 ≤ Real.exp 2 * L ^ 2 := by
      have : (2 : ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp (2 : ℝ); linarith
      have := mul_le_mul_of_nonneg_right this (sq_nonneg L)
      linarith
    calc Real.log (L ^ 2 + 2) ≤ Real.log (Real.exp 2 * L ^ 2) := Real.log_le_log (by positivity) h1
      _ = 2 + 2 * Real.log L := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow]; push_cast; ring
  have hTL : T * (L ^ 2 + 2) ≤ Real.exp (L ^ (1 / 20 : ℝ) + 2 + 2 * Real.log L) := by
    rw [show L ^ (1 / 20 : ℝ) + 2 + 2 * Real.log L = L ^ (1 / 20 : ℝ) + (2 + 2 * Real.log L) by ring,
      Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hT0.le
    calc L ^ 2 + 2 = Real.exp (Real.log (L ^ 2 + 2)) := (Real.exp_log (by positivity)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlogL2
  have hTLp : T * (L ^ 2 + 2) ≤ Real.exp (L - 1) := hTL.trans (Real.exp_le_exp.mpr hR1)
  have hexpL1 : Real.exp (L - 1) * 2 ≤ Real.exp L := by
    rw [show L = (L - 1) + 1 by ring, Real.exp_add]; simp only [add_sub_cancel_right]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have := Real.add_one_le_exp (1 : ℝ); linarith
  -- `M`, `N`, `H`
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
  have hlogN : Real.log N ≤ L ^ (1 / 20 : ℝ) + 2 + 2 * Real.log L := by
    rw [Real.log_le_iff_le_exp hNpos]; exact hNTL.trans hTL
  -- `K_*`
  set E := Real.exp (L ^ (9 / 10 : ℝ))
  set Ks := ⌈E⌉₊
  have hKs1 : E ≤ Ks := Nat.le_ceil _
  have hKs2 : (Ks : ℝ) < E + 1 := Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hE4 : (6 : ℝ) ≤ E := six_le_exp hR3
  have hKs6 : 6 ≤ Ks := by
    have : (6 : ℝ) ≤ Ks := hE4.trans hKs1
    exact_mod_cast this
  have h3TL : 3 * (T * (L ^ 2 + 2)) ≤ E := by
    calc 3 * (T * (L ^ 2 + 2)) ≤ Real.exp 2 * Real.exp (L ^ (1 / 20 : ℝ) + 2 + 2 * Real.log L) := by
          apply mul_le_mul _ hTL (by positivity) (Real.exp_pos _).le
          have := Real.add_one_le_exp (2 : ℝ); linarith
      _ = Real.exp (L ^ (1 / 20 : ℝ) + 2 * Real.log L + 4) := by rw [← Real.exp_add]; ring_nf
      _ ≤ E := Real.exp_le_exp.mpr hR4
  have hNKs : 2 * N + 1 ≤ Ks := by
    have : ((2 * N + 1 : ℕ) : ℝ) ≤ Ks := by
      push_cast
      have := mul_le_mul_of_nonneg_right hT2 (by positivity : (0 : ℝ) ≤ L ^ 2 + 2)
      linarith
    exact_mod_cast this
  -- `K = K_W`
  set V := Real.exp (L * θ) * L ^ 4
  have hKWe : KWθ θ p = ⌊V⌋₊ := by
    unfold KWθ; rw [hpL, ← Real.exp_mul, Real.log_exp]
  have hV0 : 0 ≤ V := by positivity
  have hK1 : (KWθ θ p : ℝ) ≤ V := by rw [hKWe]; exact Nat.floor_le hV0
  have hK2 : V < KWθ θ p + 1 := by rw [hKWe]; exact Nat.lt_floor_add_one V
  have hLθ1 : L / 2 ≤ L * θ := by
    have := mul_le_mul_of_nonneg_left hθ1 hLpos.le; linarith
  have hLθ2 : L * θ ≤ L * (3 / 4) := mul_le_mul_of_nonneg_left hθ2 hLpos.le
  have hEL2 : Real.exp (L / 2) ≤ V :=
    (Real.exp_le_exp.mpr hLθ1).trans
      (le_mul_of_one_le_right (Real.exp_pos _).le (one_le_pow₀ (by linarith)))
  have hVbig : 2 ≤ V := by
    have := Real.add_one_le_exp (L / 2); linarith
  have hV20 : V * 20 ≤ Real.exp L := by
    have h1 : V = Real.exp (L * θ + 4 * Real.log L) := by
      rw [Real.exp_add, show (4 : ℝ) * Real.log L = Real.log (L ^ 4) by rw [Real.log_pow]; norm_num,
        Real.exp_log (pow_pos hLpos 4)]
    have h2 : Real.exp (L * θ + 4 * Real.log L) * Real.exp 3 ≤ Real.exp L := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    rw [h1]
    exact (mul_le_mul_of_nonneg_left exp_three_ge (Real.exp_pos _).le).trans h2
  have hKpos' : (0 : ℝ) < KWθ θ p := by linarith
  have hK8 : (KWθ θ p : ℝ) * 8 ≤ p := by rw [hpL]; linarith
  have hKp : KWθ θ p ≤ p := by
    have : (KWθ θ p : ℝ) ≤ p := by linarith
    exact_mod_cast this
  have hK2p : 2 * KWθ θ p < p := by
    have : ((2 * KWθ θ p : ℕ) : ℝ) < p := by push_cast; linarith
    exact_mod_cast this
  have hKsK : Ks ≤ KWθ θ p := by
    have h2E : E * 2 ≤ Real.exp (L / 2) := by
      calc E * 2 ≤ E * Real.exp 1 := by
            apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
            have := Real.add_one_le_exp (1 : ℝ); linarith
        _ = Real.exp (L ^ (9 / 10 : ℝ) + 1) := by rw [Real.exp_add]
        _ ≤ Real.exp (L / 2) := Real.exp_le_exp.mpr hR5
    have : (Ks : ℝ) < KWθ θ p + 1 := by linarith
    have : Ks < KWθ θ p + 1 := by exact_mod_cast this
    omega
  have hlogKs : L ^ (9 / 10 : ℝ) / 2 ≤ Real.log ((Ks : ℝ) / 3) := by
    have h1 : L ^ (9 / 10 : ℝ) / 2 + Real.log 3 ≤ L ^ (9 / 10 : ℝ) := by
      have := log_three_lt
      linarith
    rw [Real.log_div (by positivity) (by norm_num)]
    have : L ^ (9 / 10 : ℝ) ≤ Real.log Ks := by
      rw [Real.le_log_iff_exp_le (by positivity)]; exact hKs1
    linarith
  have hlogKs' : Real.log p ^ (9 / 10 : ℝ) / 2 ≤ Real.log ((Ks : ℝ) / 3) := hlogKs
  -- `J`
  set J := ⌈2 * L⌉₊
  have hJ1 : 2 * L ≤ J := Nat.le_ceil _
  have hJ2 : (J : ℝ) < 2 * L + 1 := Nat.ceil_lt_add_one (by positivity)
  have hKJ : KWθ θ p ≤ 2 ^ J * Ks := by
    have h1 : Real.exp L ≤ (2 : ℝ) ^ J := by
      have : Real.exp L ≤ Real.exp (J * Real.log 2) := by
        apply Real.exp_le_exp.mpr
        have h1 := mul_le_mul_of_nonneg_right hJ1 (Real.log_pos one_lt_two).le
        have h2 := mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le hLpos.le
        linarith
      rw [show Real.exp (J * Real.log 2) = (2 : ℝ) ^ J by
        rw [← Real.log_pow, Real.exp_log (by positivity)]] at this
      exact this
    have : (KWθ θ p : ℝ) ≤ 2 ^ J * Ks := by
      have hKs1' : (1 : ℝ) ≤ Ks := by exact_mod_cast (by omega : 1 ≤ Ks)
      have : (KWθ θ p : ℝ) ≤ Real.exp L := by rw [← hpL]; exact_mod_cast hKp
      have := le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ 2 ^ J) hKs1'
      linarith
    exact_mod_cast this
  -- `I`
  set I := Nat.log 2 (KWθ θ p) + 1
  have hKpos : 0 < KWθ θ p := by exact_mod_cast hKpos'
  have hI1 : KWθ θ p < 2 ^ I := Nat.lt_pow_succ_log_self (by norm_num) _
  have hI2 : 2 ^ (I - 1) ≤ KWθ θ p := by
    simp only [I, Nat.add_sub_cancel]; exact Nat.pow_log_le_self 2 hKpos.ne'
  have hI2' : (2 : ℝ) ^ I ≤ 2 * KWθ θ p := by
    have : 2 ^ I ≤ 2 * KWθ θ p := by
      have e : I = (I - 1) + 1 := by simp only [I]; omega
      rw [e, pow_succ]; omega
    exact_mod_cast this
  have hIL : (I : ℝ) ≤ 2 * L := by
    have h1 : ((I - 1 : ℕ) : ℝ) * Real.log 2 ≤ L := by
      rw [← Real.log_pow]
      have : ((2 : ℝ) ^ (I - 1)) ≤ Real.exp L := by
        rw [← hpL]; have : (2 : ℝ) ^ (I - 1) ≤ KWθ θ p := by exact_mod_cast hI2
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
  have hTI : (KWθ θ p : ℝ) ≤ T * 2 ^ I := by
    have : (KWθ θ p : ℝ) ≤ 2 ^ I := by exact_mod_cast hI1.le
    have := le_mul_of_one_le_left (by positivity : (0 : ℝ) ≤ 2 ^ I) (by linarith : (1 : ℝ) ≤ T)
    linarith
  have hpI : (p : ℝ) * 2 ^ I + M ≤ (p : ℝ) ^ 2 := by
    have hMp' : (M : ℝ) ≤ p := by exact_mod_cast hMp.le
    have hp4 : (4 : ℝ) ≤ p := by exact_mod_cast (by omega : 4 ≤ p)
    have h1 := mul_le_mul_of_nonneg_left (by linarith : (2 : ℝ) ^ I ≤ p / 4) hp0.le
    have h2 := mul_le_mul_of_nonneg_right hp4 hp0.le
    linarith
  have hdiv : ∀ k ∈ (Ioo (N + 1) (KWθ θ p)).filter Odd, (k : ℤ) ∣ 2 * p * uInv p k - 1 := by
    intro k hk
    simp only [mem_filter, mem_Ioo] at hk
    apply uInv_spec p k (by omega)
    have hcop : Nat.Coprime p k := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]; intro h; have := Nat.le_of_dvd (by omega) h; omega
    exact Nat.coprime_mul_iff_left.mpr ⟨Nat.coprime_two_left.mpr hk.2, hcop⟩
  have htail := hL₀ p hp hLL₀ M N (KWθ θ p) I (uInv p) hM1' hMN hN2' hMp hT2 hTI hpI hM1 hN1 hKp hdiv
  rw [← hLdef, ← hTdef] at htail
  -- the Bourgain–Garaev input with `C' = max C 0`
  have hBG' : ∀ b : ZMod p, b ≠ 0 → ∀ N' : ℕ, Real.log p ^ (9 / 10 : ℝ) / 2 ≤ Real.log N' → N' < p →
      ‖Tsum p b N'‖ ≤ bgB C' p N' := by
    intro b hb N' hN' hN'p
    refine (hBGp b hb N' hN' hN'p).trans ?_
    unfold bgB
    have hlN' : 0 ≤ Real.log N' := le_trans (by positivity) hN'
    have hY : 0 ≤ Real.log (Real.log p) ^ 3 * Real.log p * Real.log N' ^ (-(3 / 2 : ℝ)) * N' := by
      have : 0 ≤ Real.log p := by linarith
      positivity
    have e1 : C * Real.log (Real.log p) ^ 3 * Real.log p * Real.log N' ^ (-(3 / 2 : ℝ)) * N' =
        C * (Real.log (Real.log p) ^ 3 * Real.log p * Real.log N' ^ (-(3 / 2 : ℝ)) * N') := by ring
    have e2 : C' * Real.log (Real.log p) ^ 3 * Real.log p * Real.log N' ^ (-(3 / 2 : ℝ)) * N' =
        C' * (Real.log (Real.log p) ^ 3 * Real.log p * Real.log N' ^ (-(3 / 2 : ℝ)) * N') := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hY
  have hRb := R_bound hV C' hC' p hp hp5 hBG' (KWθ θ p) N M Ks J (by omega) hM1' hMp hNp hKs6 hNKs hKsK hK2p
    hlogKs' hKJ _ htail
  -- bounding the right-hand side by `Gb C' L`
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have hAt : 2 + Real.log N ≤ Aterm L := by unfold Aterm; linarith
  have hKs0 : (0 : ℝ) < Ks := by exact_mod_cast (by omega : 0 < Ks)
  have hlKs : 1 + Real.log (Ks : ℝ) ≤ L ^ (9 / 10 : ℝ) + 2 := by
    have : Real.log (Ks : ℝ) ≤ L ^ (9 / 10 : ℝ) + 1 := by
      rw [Real.log_le_iff_le_exp hKs0, Real.exp_add]
      have : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
      have : (1 : ℝ) ≤ E := by linarith
      change (Ks : ℝ) ≤ E * Real.exp 1
      have hE2 : E * 2 ≤ E * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (by assumption) (by linarith)
      linarith
    linarith
  have hlKs0 : 0 ≤ 1 + Real.log (Ks : ℝ) := by
    have := Real.log_natCast_nonneg Ks; linarith
  have hlK : Real.log (KWθ θ p : ℝ) ≤ L :=
    Real.log_le_log hKpos' (by exact_mod_cast hKp)
  have hlK0 : 0 ≤ 1 + Real.log (KWθ θ p : ℝ) := by
    have := Real.log_natCast_nonneg (KWθ θ p); linarith
  have hHsum : ∑ h ∈ Icc 1 M, 4 / (Real.pi * h) = 4 / Real.pi * ∑ h ∈ Icc 1 M, (1 / h : ℝ) := by
    rw [mul_sum]; apply sum_congr rfl; intro h _; rw [mul_one_div, div_div]
  have hHs0 : 0 ≤ ∑ h ∈ Icc 1 M, 4 / (Real.pi * h) + 4 := by
    have : 0 ≤ ∑ h ∈ Icc 1 M, 4 / (Real.pi * h) := sum_nonneg (fun h _ => by positivity)
    linarith
  have hHs : ∑ h ∈ Icc 1 M, 4 / (Real.pi * h) + 4 ≤ 8 + 4 * Real.log L := by
    rw [hHsum]
    have h1 := sum_inv_le_log (M + 1) (Icc 1 M) (fun k hk => by simp only [mem_Icc] at hk; omega)
    push_cast at h1
    have h2 : Real.log ((M : ℝ) + 1) ≤ Real.log 2 + 2 * Real.log L := by
      rw [← Real.log_rpow (by linarith), ← Real.log_mul (by norm_num) (by positivity)]
      apply Real.log_le_log (by positivity)
      rw [show L ^ (2 : ℝ) = L ^ 2 by norm_cast]
      linarith
    have h3 := Real.log_two_lt_d9
    have h4 := Real.pi_gt_three
    have hs0 : 0 ≤ ∑ h ∈ Icc 1 M, (1 / h : ℝ) := sum_nonneg (fun h _ => by positivity)
    have h5 : 4 / Real.pi ≤ 4 / 3 := by gcongr
    have h6 : 4 / Real.pi * ∑ h ∈ Icc 1 M, (1 / h : ℝ) ≤ 4 / 3 * ∑ h ∈ Icc 1 M, (1 / h : ℝ) :=
      mul_le_mul_of_nonneg_right h5 hs0
    linarith
  have hL9 : 0 < L ^ (9 / 10 : ℝ) / 2 := by linarith
  have hY0 : 0 ≤ Real.log ((Ks : ℝ) / 3) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hY : Real.log ((Ks : ℝ) / 3) ^ (-(3 / 2 : ℝ)) ≤ (L ^ (9 / 10 : ℝ) / 2) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hL9 hlogKs (by norm_num)
  have hM2' : (M : ℝ) ≤ 2 * L ^ 2 := by linarith
  have he : T ^ (-(1 / 20 / 4 : ℝ)) = Real.exp (-(L ^ (1 / 20 : ℝ) / 80)) := by
    change Real.exp (L ^ (1 / 20 : ℝ)) ^ (-(1 / 20 / 4 : ℝ)) = _
    rw [← Real.exp_mul]; congr 1; ring
  have key := rhs_le_Gb C' L (Real.log N) (Real.log Ks) M (Real.log (KWθ θ p)) J
    (∑ h ∈ Icc 1 M, 4 / (Real.pi * h)) (Real.log ((Ks : ℝ) / 3) ^ (-(3 / 2 : ℝ))) M I
    (T ^ (-(1 / 20 / 4 : ℝ))) hC' hL1000 hlogN0 hAt hlKs0 hlKs hM1 hlK0 hlK
    hJ2.le hHs0 hHs hY0 hY hM2' (Nat.cast_nonneg _) hIL
    (Real.rpow_nonneg hT0.le _) he.le
  have hR : |RsumK (KWθ θ p) p| ≤ Gb C' L := by
    refine hRb.trans (le_trans (le_of_eq ?_) key)
    ring
  -- conclusion
  have hR' : -Gb C' L ≤ RsumK (KWθ θ p) p := (abs_le.mp hR).1
  have h1 : 4 * (p : ℝ) / Real.pi * (-Gb C' L) ≤ 4 * (p : ℝ) / Real.pi * RsumK (KWθ θ p) p :=
    mul_le_mul_of_nonneg_left hR' (by positivity)
  have h2 : (p : ℝ) * (4 / Real.pi * Gb C' L + (C1 + n)) < p * (L / 2) :=
    mul_lt_mul_of_pos_left hfin hp0
  have h3 : ((n : ℤ) * p : ℝ) < (S p : ℝ) := by
    have e1 : 4 * (p : ℝ) / Real.pi * (-Gb C' L) = -((p : ℝ) * (4 / Real.pi * Gb C' L)) := by ring
    rw [e1] at h1
    have e2 : (p : ℝ) * (4 / Real.pi * Gb C' L + (C1 + n)) =
        (p : ℝ) * (4 / Real.pi * Gb C' L) + C1 * p + n * p := by ring
    rw [e2] at h2
    have e3 : (p : ℝ) / 2 * L = (p : ℝ) * (L / 2) := by ring
    push_cast
    linarith
  exact_mod_cast h3

/-- **The lower half of Conjecture 3.3**, conditional on (HB), (HV), (HBG). -/
theorem lower_half (hB : HB) (hV : HV) (hBG : HBG) :
    ∀ n : ℕ, ∀ᶠ k in Filter.atTop, k.Prime → (n : ℤ) * k < S k := by
  refine lower_half_gen (1 / 2) le_rfl (by norm_num) ?_ hV hBG
  obtain ⟨C, hC⟩ := hB
  refine ⟨C, ?_⟩
  filter_upwards [hC] with p hp
  rw [← KW_eq]; exact hp

/-- **The lower half of Conjecture 3.3** with the cutoff `KW34`, conditional on (HB34), (HV), (HBG). -/
theorem lower_half34 (hB : HB34) (hV : HV) (hBG : HBG) :
    ∀ n : ℕ, ∀ᶠ k in Filter.atTop, k.Prime → (n : ℤ) * k < S k :=
  lower_half_gen (3 / 4) (by norm_num) le_rfl hB hV hBG

end ThetaSum
