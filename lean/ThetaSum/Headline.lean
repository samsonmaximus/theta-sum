import Upper.TheoremB
import ThetaSum.Conjecture33
import ThetaSum.Kloosterman

/-!
# Headline: Conjecture 3.3 of arXiv:2501.03234 conditional on (HBG) only

Bridges between the vocabulary of the companion project (`Upper/*`, namespaces
`Arxiv.«2501.03234»` and `TheoremB`) and that of `ThetaSum`, then the headline theorems:
Theorem B with Kloosterman's bound (`TheoremB.HBweak34_of_HK34`) applied to the proved
Kloosterman bound `ThetaSum.hK34` discharges (HBweak34), leaving (HBG) as the only hypothesis.
-/

namespace ThetaSum

/-- Both `S` are the verbatim formal-conjectures definition. -/
theorem S_bridge (k : ℕ) : Arxiv.«2501.03234».S k = ThetaSum.S k := rfl

/-- The tangent sums agree (the companion `Fsum` takes an integer argument). -/
theorem Fsum_bridge (k p : ℕ) : Arxiv.«2501.03234».Fsum k (p : ℤ) = ThetaSum.Fsum k p := by
  unfold Arxiv.«2501.03234».Fsum ThetaSum.Fsum
  push_cast
  rfl

theorem KW34_bridge : TheoremB.KW34 = ThetaSum.KW34 := rfl

theorem psiP_eq (p : ℕ) (x : ZMod p) :
    psiP p x = Complex.exp (2 * Real.pi * Complex.I * ((x.val : ℂ) / p)) := by
  unfold psiP
  push_cast
  rfl

/-- The two statements of Kloosterman's `2 p^{3/4}` bound agree. -/
theorem HK34_bridge : ThetaSum.HK34 ↔ TheoremB.HK34 := by
  constructor
  · intro h p hp
    haveI : Fact p.Prime := ⟨hp⟩
    intro b ℓ hb
    have := h p b ℓ hb
    simp only [psiP_eq] at this
    exact this
  · intro h p _ b ℓ hb
    have := h p Fact.out b ℓ hb
    simp only [psiP_eq]
    exact this

theorem HBweak34_bridge : TheoremB.HBweak34 → ThetaSum.HBweak34 := by
  rintro ⟨c, C, h⟩
  refine ⟨c, C, ?_⟩
  filter_upwards [h] with p hp hpr
  have := hp hpr
  simp only [S_bridge, KW34_bridge, Fsum_bridge] at this
  exact this

/-- (HBweak34) holds unconditionally: Theorem B (Kloosterman form) + Kloosterman's bound. -/
theorem hBweak34 : ThetaSum.HBweak34 :=
  HBweak34_bridge (TheoremB.HBweak34_of_HK34 (HK34_bridge.mp hK34))

/-- **Conjecture 3.3** of arXiv:2501.03234, conditional only on (HBG). -/
theorem conjecture_3_3_of_BG (hBG : HBG) : ∀ C₁ C₂ ε : ℝ, 0 < C₁ → 0 < C₂ → 0 < ε →
    ∀ᶠ k : ℕ in Filter.atTop, k.Prime →
      C₁ * k < (S k : ℝ) ∧ (S k : ℝ) < C₂ * (k : ℝ) ^ (1 + ε) :=
  conjecture_3_3_34 hBweak34 hBG

/-- Conjecture 1.1, for all large primes: `S(k) > 0`. Conditional only on (HBG). -/
theorem conjecture_1_1_eventually_of_BG (hBG : HBG) :
    ∀ᶠ k : ℕ in Filter.atTop, k.Prime → 0 < S k := by
  filter_upwards [lower_half_HBweak34_HBG hBweak34 hBG 0] with k hk hp
  simpa using hk hp

/-- Conjecture 3.1, for all large primes: `S(k) > 2k`. Conditional only on (HBG). -/
theorem conjecture_3_1_eventually_of_BG (hBG : HBG) :
    ∀ᶠ k : ℕ in Filter.atTop, k.Prime → 2 * (k : ℤ) < S k := by
  simpa using lower_half_HBweak34_HBG hBweak34 hBG 2

/-- Conjecture 3.2, for all large primes: `S(k) > 3k`. Conditional only on (HBG). -/
theorem conjecture_3_2_eventually_of_BG (hBG : HBG) :
    ∀ᶠ k : ℕ in Filter.atTop, k.Prime → 3 * (k : ℤ) < S k := by
  simpa using lower_half_HBweak34_HBG hBweak34 hBG 3

end ThetaSum

#print axioms ThetaSum.HK34_bridge
#print axioms ThetaSum.hBweak34
#print axioms ThetaSum.conjecture_3_3_of_BG
#print axioms ThetaSum.conjecture_1_1_eventually_of_BG
#print axioms ThetaSum.conjecture_3_1_eventually_of_BG
#print axioms ThetaSum.conjecture_3_2_eventually_of_BG
