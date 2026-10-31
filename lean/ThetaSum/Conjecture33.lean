import ThetaSum.UpperHalf
import ThetaSum.LowerHalfFinal

/-!
# Conjecture 3.3 of arXiv:2501.03234

For any fixed `C₁, C₂, ε > 0`, `C₁ k < S(k) < C₂ k^{1+ε}` for all sufficiently large primes `k`.
The upper half is unconditional (`UpperHalf.lean`, Appendix A of the paper). The lower half is
conditional on (HBweak) and (HBG) (`Hypotheses.lean`, `LowerHalfFinal.lean`).
-/

namespace ThetaSum

/-- **Conjecture 3.3, upper half** (unconditional). -/
theorem conjecture_3_3_upper : ∀ C₂ ε : ℝ, 0 < C₂ → 0 < ε →
    ∀ᶠ k : ℕ in Filter.atTop, k.Prime → (S k : ℝ) < C₂ * (k : ℝ) ^ (1 + ε) :=
  fun C₂ ε hC hε => Upper.conjecture_3_3_upper C₂ hC ε hε

/-- From `n k < S k` eventually for every `n` to `C₁ k < S k` eventually for every real `C₁`. -/
lemma lower_real (h : ∀ n : ℕ, ∀ᶠ k in Filter.atTop, k.Prime → (n : ℤ) * k < S k) (C₁ : ℝ) :
    ∀ᶠ k : ℕ in Filter.atTop, k.Prime → C₁ * k < (S k : ℝ) := by
  filter_upwards [h ⌈C₁⌉₊] with k hk hp
  have h1 : ((⌈C₁⌉₊ : ℤ) * k : ℝ) < (S k : ℝ) := by exact_mod_cast hk hp
  push_cast at h1
  have h2 : C₁ * k ≤ (⌈C₁⌉₊ : ℝ) * k :=
    mul_le_mul_of_nonneg_right (Nat.le_ceil C₁) (Nat.cast_nonneg k)
  linarith

/-- Conjecture 3.3 from any eventual lower half. -/
lemma conj_of_lower (h : ∀ n : ℕ, ∀ᶠ k in Filter.atTop, k.Prime → (n : ℤ) * k < S k) :
    ∀ C₁ C₂ ε : ℝ, 0 < C₁ → 0 < C₂ → 0 < ε →
      ∀ᶠ k : ℕ in Filter.atTop, k.Prime →
        C₁ * k < (S k : ℝ) ∧ (S k : ℝ) < C₂ * (k : ℝ) ^ (1 + ε) := by
  intro C₁ C₂ ε _ hC₂ hε
  filter_upwards [lower_real h C₁, conjecture_3_3_upper C₂ ε hC₂ hε] with k h1 h2 hp
  exact ⟨h1 hp, h2 hp⟩

/-- **Conjecture 3.3, lower half**, conditional on (HBweak) and (HBG). -/
theorem conjecture_3_3_lower (hB : HBweak) (hBG : HBG) : ∀ C₁ : ℝ,
    ∀ᶠ k : ℕ in Filter.atTop, k.Prime → C₁ * k < (S k : ℝ) :=
  lower_real (lower_half_HBweak_HBG hB hBG)

/-- **Conjecture 3.3** of arXiv:2501.03234, conditional on (HBweak) and (HBG). -/
theorem conjecture_3_3 (hB : HBweak) (hBG : HBG) : ∀ C₁ C₂ ε : ℝ, 0 < C₁ → 0 < C₂ → 0 < ε →
    ∀ᶠ k : ℕ in Filter.atTop, k.Prime →
      C₁ * k < (S k : ℝ) ∧ (S k : ℝ) < C₂ * (k : ℝ) ^ (1 + ε) :=
  conj_of_lower (lower_half_HBweak_HBG hB hBG)

/-- **Conjecture 3.3**, conditional on (HBweak34) (cutoff `p^{3/4} (log p)^4`) and (HBG). -/
theorem conjecture_3_3_34 (hB : HBweak34) (hBG : HBG) : ∀ C₁ C₂ ε : ℝ, 0 < C₁ → 0 < C₂ → 0 < ε →
    ∀ᶠ k : ℕ in Filter.atTop, k.Prime →
      C₁ * k < (S k : ℝ) ∧ (S k : ℝ) < C₂ * (k : ℝ) ^ (1 + ε) :=
  conj_of_lower (lower_half_HBweak34_HBG hB hBG)

/-- Conjecture 1.1, for all large primes: `S(k) > 0`. Conditional on (HBweak) and (HBG). -/
theorem conjecture_1_1_eventually (hB : HBweak) (hBG : HBG) :
    ∀ᶠ k : ℕ in Filter.atTop, k.Prime → 0 < S k := by
  filter_upwards [lower_half_HBweak_HBG hB hBG 0] with k hk hp
  simpa using hk hp

/-- Conjecture 3.1, for all large primes: `S(k) > 2k`. Conditional on (HBweak) and (HBG). -/
theorem conjecture_3_1_eventually (hB : HBweak) (hBG : HBG) :
    ∀ᶠ k : ℕ in Filter.atTop, k.Prime → 2 * (k : ℤ) < S k := by
  simpa using lower_half_HBweak_HBG hB hBG 2

/-- Conjecture 3.2, for all large primes: `S(k) > 3k`. Conditional on (HBweak) and (HBG). -/
theorem conjecture_3_2_eventually (hB : HBweak) (hBG : HBG) :
    ∀ᶠ k : ℕ in Filter.atTop, k.Prime → 3 * (k : ℤ) < S k := by
  simpa using lower_half_HBweak_HBG hB hBG 3

end ThetaSum

#print axioms ThetaSum.conjecture_3_3_upper
#print axioms ThetaSum.conjecture_3_3
#print axioms ThetaSum.conjecture_3_3_34
#print axioms ThetaSum.conjecture_1_1_eventually
#print axioms ThetaSum.conjecture_3_1_eventually
#print axioms ThetaSum.conjecture_3_2_eventually
