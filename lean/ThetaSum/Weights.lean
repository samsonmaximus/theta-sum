import Mathlib

/-
Tools for the heads (Lemma 6.6):

* `x2cot_monotoneOn`: `x ↦ x² cot x` is increasing on `(0, π/4]`.
* `weight_antitone`: for `n ≥ 1` and `2n ≤ k ≤ k'`,
  `cot(π n/(2k'))/k'² ≤ cot(π n/(2k))/k²` (the weights of the heads decrease in `k`).
* `abel_antitone`: Abel's inequality `‖∑_{a ≤ k < b} w_k z_k‖ ≤ w_a · max_x ‖∑_{a ≤ k < x} z_k‖`
  for nonnegative decreasing weights.
-/

open Finset

namespace ThetaSum

lemma x2cot_hasDerivAt {x : ℝ} (hs : Real.sin x ≠ 0) :
    HasDerivAt (fun x => x ^ 2 * Real.cos x / Real.sin x)
      (((2 * x * Real.cos x - x ^ 2 * Real.sin x) * Real.sin x - x ^ 2 * Real.cos x * Real.cos x) /
        Real.sin x ^ 2) x := by
  have h1 : HasDerivAt (fun x => x ^ 2 * Real.cos x) (2 * x * Real.cos x - x ^ 2 * Real.sin x) x := by
    have := ((hasDerivAt_pow 2 x).mul (Real.hasDerivAt_cos x))
    convert this using 1; push_cast; ring
  exact h1.div (Real.hasDerivAt_sin x) hs

theorem x2cot_monotoneOn :
    MonotoneOn (fun x => x ^ 2 * Real.cos x / Real.sin x) (Set.Ioc 0 (Real.pi / 4)) := by
  have hpi := Real.pi_pos
  have hsin : ∀ x ∈ Set.Ioc (0 : ℝ) (Real.pi / 4), Real.sin x ≠ 0 := by
    intro x hx
    exact (Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2])).ne'
  apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 (Real.pi / 4))
  · intro x hx
    exact (x2cot_hasDerivAt (hsin x hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    exact (x2cot_hasDerivAt (hsin x ⟨hx.1, hx.2.le⟩)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    rw [(x2cot_hasDerivAt (hsin x ⟨hx.1, hx.2.le⟩)).deriv]
    apply div_nonneg _ (sq_nonneg _)
    have hx0 := hx.1
    have h2 : 2 / Real.pi * (2 * x) ≤ Real.sin (2 * x) :=
      Real.mul_le_sin (by linarith) (by linarith [hx.2])
    have h3 : x ≤ 2 / Real.pi * (2 * x) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hpi]
      nlinarith [Real.pi_lt_four]
    have hsc : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := Real.sin_two_mul x
    have hpy := Real.sin_sq_add_cos_sq x
    have e : (2 * x * Real.cos x - x ^ 2 * Real.sin x) * Real.sin x -
        x ^ 2 * Real.cos x * Real.cos x = x * (2 * Real.sin x * Real.cos x - x) := by
      have : x ^ 2 * Real.sin x * Real.sin x + x ^ 2 * Real.cos x * Real.cos x = x ^ 2 := by
        have e' : x ^ 2 * Real.sin x * Real.sin x + x ^ 2 * Real.cos x * Real.cos x =
            x ^ 2 * (Real.sin x ^ 2 + Real.cos x ^ 2) := by ring
        rw [e', hpy, mul_one]
      nlinarith [this]
    rw [e]
    apply mul_nonneg hx0.le
    linarith

/-- The weights `cot(π n/(2k))/k²` decrease in `k` for `k ≥ 2n`. -/
theorem weight_antitone (n k k' : ℕ) (hn : 1 ≤ n) (hk : 2 * n ≤ k) (hkk : k ≤ k') :
    Real.cot (Real.pi * n / (2 * k')) / (k' : ℝ) ^ 2 ≤ Real.cot (Real.pi * n / (2 * k)) / (k : ℝ) ^ 2 := by
  have hpi := Real.pi_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk0' : (0 : ℝ) < k' := by exact_mod_cast (by omega : 0 < k')
  set x := Real.pi * n / (2 * k)
  set x' := Real.pi * n / (2 * k')
  have hx : x ∈ Set.Ioc 0 (Real.pi / 4) := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2 * n : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hx' : x' ∈ Set.Ioc 0 (Real.pi / 4) := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2 * n : ℝ) ≤ k' := by exact_mod_cast (le_trans hk hkk)
    nlinarith
  have hxx : x' ≤ x := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have : (k : ℝ) ≤ k' := by exact_mod_cast hkk
    linarith
  have hmono := x2cot_monotoneOn hx' hx hxx
  simp only at hmono
  -- `cot x / k² = (4/(π² n²)) x² cot x`
  have e : ∀ (kk : ℕ), (0 : ℝ) < kk → Real.cot (Real.pi * n / (2 * kk)) / (kk : ℝ) ^ 2 =
      4 / (Real.pi ^ 2 * n ^ 2) * ((Real.pi * n / (2 * kk)) ^ 2 * Real.cos (Real.pi * n / (2 * kk)) /
        Real.sin (Real.pi * n / (2 * kk))) := by
    intro kk hkk0
    rw [Real.cot_eq_cos_div_sin]
    field_simp
    ring
  rw [e k' hk0', e k hk0]
  exact mul_le_mul_of_nonneg_left hmono (by positivity)

/-- Summation by parts: `∑_{a ≤ k < b} w_k z_k = w_b P_b + ∑_{a ≤ k < b} (w_k - w_{k+1}) P_{k+1}`,
`P_x = ∑_{a ≤ i < x} z_i`. -/
lemma abel_identity (w : ℕ → ℝ) (z : ℕ → ℂ) (a : ℕ) : ∀ b, a ≤ b →
    ∑ k ∈ Ico a b, (w k : ℂ) * z k =
      (w b : ℂ) * ∑ i ∈ Ico a b, z i + ∑ k ∈ Ico a b, ((w k - w (k + 1) : ℝ) : ℂ) * ∑ i ∈ Ico a (k + 1), z i := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [sum_Ico_succ_top hab (f := fun k => (w k : ℂ) * z k), ih,
      sum_Ico_succ_top hab (f := fun k => ((w k - w (k + 1) : ℝ) : ℂ) * ∑ i ∈ Ico a (k + 1), z i),
      sum_Ico_succ_top hab (f := z)]
    push_cast; ring

/-- **Abel's inequality** for nonnegative decreasing weights. -/
theorem abel_antitone (w : ℕ → ℝ) (z : ℕ → ℂ) (a b : ℕ) (hab : a ≤ b) (M : ℝ)
    (hw : ∀ k, a ≤ k → k < b → w (k + 1) ≤ w k) (hwb : 0 ≤ w b)
    (hM : ∀ x, a ≤ x → x ≤ b → ‖∑ i ∈ Ico a x, z i‖ ≤ M) :
    ‖∑ k ∈ Ico a b, (w k : ℂ) * z k‖ ≤ w a * M := by
  rw [abel_identity w z a b hab]
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM a le_rfl hab)
  have htel' : ∀ b', a ≤ b' → ∑ k ∈ Ico a b', (w k - w (k + 1)) = w a - w b' := by
    intro b' hb'
    induction b', hb' using Nat.le_induction with
    | base => simp
    | succ b' hab' ih => rw [sum_Ico_succ_top hab', ih]; ring
  have htel := htel' b hab
  calc ‖(w b : ℂ) * ∑ i ∈ Ico a b, z i + ∑ k ∈ Ico a b, ((w k - w (k + 1) : ℝ) : ℂ) * ∑ i ∈ Ico a (k + 1), z i‖
      ≤ ‖(w b : ℂ) * ∑ i ∈ Ico a b, z i‖ +
          ∑ k ∈ Ico a b, ‖((w k - w (k + 1) : ℝ) : ℂ) * ∑ i ∈ Ico a (k + 1), z i‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ w b * M + ∑ k ∈ Ico a b, (w k - w (k + 1)) * M := by
        apply add_le_add
        · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hwb]
          exact mul_le_mul_of_nonneg_left (hM b hab le_rfl) hwb
        · apply sum_le_sum; intro k hk
          rw [mem_Ico] at hk
          have hd : 0 ≤ w k - w (k + 1) := by linarith [hw k hk.1 hk.2]
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hd]
          exact mul_le_mul_of_nonneg_left (hM (k + 1) (by omega) (by omega)) hd
    _ = w a * M := by rw [← sum_mul, htel]; ring

end ThetaSum

#print axioms ThetaSum.weight_antitone
#print axioms ThetaSum.abel_antitone
