import ThetaSum.Hypotheses

/-
**Lemma 6.4** (in the form needed here). For a prime `p`, `c ∈ 𝔽_p` and `1 ≤ a ≤ x`, the sum of
`e(c (2k)^{-1}/p)` over the odd `k ∈ [a, x)` is a combination of four initial sums
`T_b(N) = ∑_{n=1}^N e(b n^{-1}/p)` with `b = c/2` and `b = c/4`:
for odd `k`, `(2k)^{-1} = 2^{-1} k^{-1}`, and the even `k = 2j` have `(2k)^{-1} = 4^{-1} j^{-1}`.
-/

open Finset

namespace ThetaSum

/-- The initial Kloosterman sum `T_b(N) = ∑_{n=1}^N e(b n^{-1}/p)`. -/
noncomputable def Tsum (p : ℕ) (b : ZMod p) (N : ℕ) : ℂ :=
  ∑ n ∈ Icc 1 N, psiP p (b * (n : ZMod p)⁻¹)

lemma Ico_sum_eq_Tdiff {β : Type*} [AddCommGroup β] (g : ℕ → β) (A B : ℕ) (hA : 1 ≤ A)
    (hAB : A ≤ B) :
    ∑ k ∈ Ico A B, g k = ∑ k ∈ Icc 1 (B - 1), g k - ∑ k ∈ Icc 1 (A - 1), g k := by
  have h1 : Icc 1 (B - 1) = Ico 1 B := by ext x; simp only [mem_Icc, mem_Ico]; omega
  have h2 : Icc 1 (A - 1) = Ico 1 A := by ext x; simp only [mem_Icc, mem_Ico]; omega
  rw [h1, h2, ← sum_Ico_consecutive g hA hAB]
  abel

lemma even_filter_sum {β : Type*} [AddCommMonoid β] (f : ℕ → β) (a x : ℕ) :
    ∑ k ∈ (Ico a x).filter Even, f k = ∑ j ∈ Ico ((a + 1) / 2) ((x + 1) / 2), f (2 * j) := by
  symm
  apply sum_nbij (fun j => 2 * j)
  · intro j hj; simp only [mem_Ico, mem_filter] at hj ⊢
    exact ⟨⟨by omega, by omega⟩, ⟨j, by ring⟩⟩
  · intro j _ j' _ h; simp only at h; omega
  · intro k hk
    simp only [coe_filter, mem_Ico, Set.mem_setOf_eq] at hk
    obtain ⟨⟨h1, h2⟩, ⟨j, hj⟩⟩ := hk
    refine ⟨j, ?_, by simp only; omega⟩
    simp only [coe_Ico, Set.mem_Ico]; omega
  · intro j _; rfl

theorem odd_interval_sum (p : ℕ) (hp : p.Prime) (c : ZMod p) (a x : ℕ) (ha : 1 ≤ a) (hax : a ≤ x) :
    ∑ k ∈ (Ico a x).filter Odd, psiP p (c * ((2 * k : ℕ) : ZMod p)⁻¹) =
      (Tsum p (c * 2⁻¹) (x - 1) - Tsum p (c * 2⁻¹) (a - 1)) -
        (Tsum p (c * 4⁻¹) ((x + 1) / 2 - 1) - Tsum p (c * 4⁻¹) ((a + 1) / 2 - 1)) := by
  haveI := Fact.mk hp
  set f : ℕ → ℂ := fun k => psiP p (c * ((2 * k : ℕ) : ZMod p)⁻¹)
  have hsplit := sum_filter_add_sum_filter_not (Ico a x) Odd f
  have hnot : ∑ k ∈ (Ico a x).filter (fun k => ¬ Odd k), f k = ∑ k ∈ (Ico a x).filter Even, f k := by
    apply sum_congr _ (fun _ _ => rfl)
    ext k; simp only [mem_filter, Nat.not_odd_iff_even]
  rw [hnot, even_filter_sum] at hsplit
  have hall : ∑ k ∈ Ico a x, f k = Tsum p (c * 2⁻¹) (x - 1) - Tsum p (c * 2⁻¹) (a - 1) := by
    rw [Ico_sum_eq_Tdiff f a x ha hax]
    unfold Tsum
    congr 1 <;> apply sum_congr rfl <;> intro k _ <;> simp only [f] <;> congr 1 <;> push_cast <;>
      rw [mul_inv] <;> ring
  have heven : ∑ j ∈ Ico ((a + 1) / 2) ((x + 1) / 2), f (2 * j) =
      Tsum p (c * 4⁻¹) ((x + 1) / 2 - 1) - Tsum p (c * 4⁻¹) ((a + 1) / 2 - 1) := by
    rw [Ico_sum_eq_Tdiff (fun j => f (2 * j)) _ _ (by omega) (by omega)]
    unfold Tsum
    congr 1 <;> apply sum_congr rfl <;> intro k _ <;> simp only [f] <;> congr 1 <;> push_cast <;>
      rw [show (2 : ZMod p) * (2 * k) = 4 * k by ring, mul_inv] <;> ring
  show ∑ k ∈ (Ico a x).filter Odd, f k = _
  rw [← hall, ← heven, ← hsplit]; ring

/-- Bound form: the sum over odd `k ∈ [a, x)` is at most the sum of four initial sums. -/
theorem odd_interval_bound (p : ℕ) (hp : p.Prime) (c : ZMod p) (a x : ℕ) (ha : 1 ≤ a) (hax : a ≤ x) :
    ‖∑ k ∈ (Ico a x).filter Odd, psiP p (c * ((2 * k : ℕ) : ZMod p)⁻¹)‖ ≤
      ‖Tsum p (c * 2⁻¹) (x - 1)‖ + ‖Tsum p (c * 2⁻¹) (a - 1)‖ +
        ‖Tsum p (c * 4⁻¹) ((x + 1) / 2 - 1)‖ + ‖Tsum p (c * 4⁻¹) ((a + 1) / 2 - 1)‖ := by
  rw [odd_interval_sum p hp c a x ha hax]
  calc _ ≤ ‖Tsum p (c * 2⁻¹) (x - 1) - Tsum p (c * 2⁻¹) (a - 1)‖ +
        ‖Tsum p (c * 4⁻¹) ((x + 1) / 2 - 1) - Tsum p (c * 4⁻¹) ((a + 1) / 2 - 1)‖ := norm_sub_le _ _
    _ ≤ _ := by
        have h1 := norm_sub_le (Tsum p (c * 2⁻¹) (x - 1)) (Tsum p (c * 2⁻¹) (a - 1))
        have h2 := norm_sub_le (Tsum p (c * 4⁻¹) ((x + 1) / 2 - 1)) (Tsum p (c * 4⁻¹) ((a + 1) / 2 - 1))
        linarith

end ThetaSum

#print axioms ThetaSum.odd_interval_bound
