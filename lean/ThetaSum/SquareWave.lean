import ThetaSum.Hypotheses

/-
**Lemma 6.3** (the square wave), derived from Vaaler's lemma (HV).

`g(y) = 2((y + 1/2)) - 2((y))` for all real `y`, so for `y, y + 1/2 ∉ ℤ`
  `|g(y) - ∑_{h=1}^H b_h sin(2π h y)| ≤ (2/(H+1)) (1 + ∑_{h=1}^H d_h cos(2π h y))`
with `|b_h| ≤ 4/(π h)` and `0 ≤ d_h ≤ 2`.
-/

open Finset

namespace ThetaSum

lemma gsq_eq_sawtooth (y : ℝ) :
    gsq y = 2 * ((y + 1 / 2) - ⌊y + 1 / 2⌋ - 1 / 2) - 2 * (y - ⌊y⌋ - 1 / 2) := by
  unfold gsq
  have hf : Int.fract y = y - ⌊y⌋ := rfl
  have h0 := Int.fract_nonneg y
  have h1 := Int.fract_lt_one y
  split_ifs with h
  · have : ⌊y + 1 / 2⌋ = ⌊y⌋ := by
      rw [Int.floor_eq_iff]; constructor <;> linarith [Int.floor_le y]
    rw [this]; ring
  · rw [not_lt] at h
    have : ⌊y + 1 / 2⌋ = ⌊y⌋ + 1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [this]; push_cast; ring

theorem square_wave (hV : HV) (H : ℕ) (hH : 1 ≤ H) :
    ∃ b d : ℕ → ℝ, (∀ h, 1 ≤ h → h ≤ H → |b h| ≤ 4 / (Real.pi * h)) ∧
      (∀ h, h ≤ H → 0 ≤ d h ∧ d h ≤ 2) ∧
      ∀ y : ℝ, (∀ m : ℤ, y ≠ m) → (∀ m : ℤ, y + 1 / 2 ≠ m) →
        |gsq y - ∑ h ∈ Icc 1 H, b h * Real.sin (2 * Real.pi * h * y)| ≤
          2 / (H + 1) * (1 + ∑ h ∈ Icc 1 H, d h * Real.cos (2 * Real.pi * h * y)) := by
  obtain ⟨c, hc, hV'⟩ := hV H hH
  refine ⟨fun h => 2 * c h * ((-1) ^ h - 1), fun h => (1 - (h : ℝ) / (H + 1)) * ((-1) ^ h + 1),
    ?_, ?_, ?_⟩
  · intro h h1 hh
    have := hc h h1 hh
    have hb : |((-1 : ℝ) ^ h - 1)| ≤ 2 := by
      rcases neg_one_pow_eq_or ℝ h with e | e <;> rw [e] <;> norm_num
    show |2 * c h * ((-1) ^ h - 1)| ≤ _
    rw [abs_mul, abs_mul, abs_two]
    calc 2 * |c h| * |(-1 : ℝ) ^ h - 1| ≤ 2 * (1 / (Real.pi * h)) * 2 := by
          apply mul_le_mul (by linarith) hb (abs_nonneg _) (by positivity)
      _ = 4 / (Real.pi * h) := by ring
  · intro h hh
    have hh' : (h : ℝ) ≤ H + 1 := by
      have : (h : ℝ) ≤ H := by exact_mod_cast hh
      linarith
    have h1 : 0 ≤ 1 - (h : ℝ) / (H + 1) := by
      rw [sub_nonneg, div_le_one (by positivity)]; exact hh'
    have h2 : 1 - (h : ℝ) / (H + 1) ≤ 1 := by
      have : 0 ≤ (h : ℝ) / (H + 1) := by positivity
      linarith
    show 0 ≤ (1 - (h : ℝ) / (H + 1)) * ((-1) ^ h + 1) ∧ (1 - (h : ℝ) / (H + 1)) * ((-1) ^ h + 1) ≤ 2
    rcases neg_one_pow_eq_or ℝ h with e | e <;> rw [e]
    · constructor <;> nlinarith
    · simp
  · intro y hy hy2
    have hA := hV' (y + 1 / 2) hy2
    have hB := hV' y hy
    set cc : ℕ → ℝ := fun h => 1 - (h : ℝ) / (H + 1)
    have hsin : ∀ h : ℕ, Real.sin (2 * Real.pi * h * (y + 1 / 2)) =
        (-1) ^ h * Real.sin (2 * Real.pi * h * y) := by
      intro h
      rw [show 2 * Real.pi * h * (y + 1 / 2) = 2 * Real.pi * h * y + h * Real.pi by ring,
        Real.sin_add_nat_mul_pi]
    have hcos : ∀ h : ℕ, Real.cos (2 * Real.pi * h * (y + 1 / 2)) =
        (-1) ^ h * Real.cos (2 * Real.pi * h * y) := by
      intro h
      rw [show 2 * Real.pi * h * (y + 1 / 2) = 2 * Real.pi * h * y + h * Real.pi by ring,
        Real.cos_add_nat_mul_pi]
    simp only [hsin, hcos] at hA
    rw [gsq_eq_sawtooth]
    set A := (y + 1 / 2) - ⌊y + 1 / 2⌋ - 1 / 2
    set B := y - ⌊y⌋ - 1 / 2
    set Ssin := fun (f : ℕ → ℝ) => ∑ h ∈ Icc 1 H, f h * Real.sin (2 * Real.pi * h * y)
    have e1 : 2 * A - 2 * B - ∑ h ∈ Icc 1 H, 2 * c h * ((-1) ^ h - 1) * Real.sin (2 * Real.pi * h * y) =
        2 * (A - ∑ h ∈ Icc 1 H, c h * ((-1) ^ h * Real.sin (2 * Real.pi * h * y))) -
          2 * (B - ∑ h ∈ Icc 1 H, c h * Real.sin (2 * Real.pi * h * y)) := by
      have : ∑ h ∈ Icc 1 H, 2 * c h * ((-1) ^ h - 1) * Real.sin (2 * Real.pi * h * y) =
          ∑ h ∈ Icc 1 H, 2 * (c h * ((-1) ^ h * Real.sin (2 * Real.pi * h * y))) -
            ∑ h ∈ Icc 1 H, 2 * (c h * Real.sin (2 * Real.pi * h * y)) := by
        rw [← sum_sub_distrib]; apply sum_congr rfl; intro h _; ring
      rw [this, ← mul_sum, ← mul_sum]; ring
    have e2 : 2 / ((H : ℝ) + 1) *
        (1 + ∑ h ∈ Icc 1 H, (1 - (h : ℝ) / (H + 1)) * ((-1) ^ h + 1) * Real.cos (2 * Real.pi * h * y)) =
        2 * (1 / (2 * H + 2) * (1 + 2 * ∑ h ∈ Icc 1 H, (1 - (h : ℝ) / (H + 1)) *
          ((-1) ^ h * Real.cos (2 * Real.pi * h * y)))) +
        2 * (1 / (2 * H + 2) * (1 + 2 * ∑ h ∈ Icc 1 H, (1 - (h : ℝ) / (H + 1)) *
          Real.cos (2 * Real.pi * h * y))) := by
      have hs : ∑ h ∈ Icc 1 H, (1 - (h : ℝ) / (H + 1)) * ((-1) ^ h + 1) * Real.cos (2 * Real.pi * h * y) =
          ∑ h ∈ Icc 1 H, (1 - (h : ℝ) / (H + 1)) * ((-1) ^ h * Real.cos (2 * Real.pi * h * y)) +
            ∑ h ∈ Icc 1 H, (1 - (h : ℝ) / (H + 1)) * Real.cos (2 * Real.pi * h * y) := by
        rw [← sum_add_distrib]; apply sum_congr rfl; intro h _; ring
      rw [hs]
      have hH0 : (0 : ℝ) < H + 1 := by positivity
      set S1 := ∑ h ∈ Icc 1 H, (1 - (h : ℝ) / (H + 1)) * ((-1) ^ h * Real.cos (2 * Real.pi * h * y))
      set S2 := ∑ h ∈ Icc 1 H, (1 - (h : ℝ) / (H + 1)) * Real.cos (2 * Real.pi * h * y)
      rw [show (2 * (H : ℝ) + 2) = 2 * (H + 1) by ring]
      field_simp
      ring
    show |2 * A - 2 * B - ∑ h ∈ Icc 1 H, 2 * c h * ((-1) ^ h - 1) * Real.sin (2 * Real.pi * h * y)| ≤
      2 / ((H : ℝ) + 1) *
        (1 + ∑ h ∈ Icc 1 H, (1 - (h : ℝ) / (H + 1)) * ((-1) ^ h + 1) * Real.cos (2 * Real.pi * h * y))
    rw [e1, e2]
    calc _ ≤ |2 * (A - ∑ h ∈ Icc 1 H, c h * ((-1) ^ h * Real.sin (2 * Real.pi * h * y)))| +
          |2 * (B - ∑ h ∈ Icc 1 H, c h * Real.sin (2 * Real.pi * h * y))| := abs_sub _ _
      _ = 2 * |A - ∑ h ∈ Icc 1 H, c h * ((-1) ^ h * Real.sin (2 * Real.pi * h * y))| +
          2 * |B - ∑ h ∈ Icc 1 H, c h * Real.sin (2 * Real.pi * h * y)| := by
          rw [abs_mul, abs_mul, abs_two]
      _ ≤ _ := by linarith

end ThetaSum

#print axioms ThetaSum.square_wave
