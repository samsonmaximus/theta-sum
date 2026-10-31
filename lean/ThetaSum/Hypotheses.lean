import ThetaSum.SignForm

/-!
# The three analytic inputs of the lower half of Conjecture 3.3

Each hypothesis is a `Prop`; `ThetaSum.lower_half` (in `LowerHalf.lean`) derives the lower half
of Conjecture 3.3 from them, with everything else proved.  Each hypothesis is a (weakened) form
of a published theorem; none is stronger than its source.

The definitions `S'` and `S` are copied verbatim from the google-deepmind formal-conjectures
repository, file `FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean`.
-/

open Finset

namespace ThetaSum

/-- `S'(h, k) = ∑_{j=1}^{k-1} (-1)^{j + 1 + ⌊hj/k⌋}` (formal-conjectures, verbatim). -/
def S' (h k : ℕ) : ℤ := ∑ j ∈ Finset.Ico 1 k, (-1 : ℤ) ^ (j + 1 + ⌊(h * j : ℚ) / k⌋₊)

/-- `S(k) = ∑_{h=1}^{k-1} S'(h, k)` (formal-conjectures, verbatim). -/
def S (k : ℕ) : ℤ := ∑ h ∈ Finset.Ico 1 k, S' h k

/-- The Weil cutoff `K_W = ⌊√p (log p)^4⌋`. -/
noncomputable def KW (p : ℕ) : ℕ := ⌊Real.sqrt p * Real.log p ^ 4⌋₊

/-- The cutoff `K = ⌊p^θ (log p)^4⌋`; `θ = 1/2` is `KW`, `θ = 3/4` is `KW34`. -/
noncomputable def KWθ (θ : ℝ) (p : ℕ) : ℕ := ⌊(p : ℝ) ^ θ * Real.log p ^ 4⌋₊

/-- The cutoff `K = ⌊p^{3/4} (log p)^4⌋` (for use with Kloosterman's bound instead of Weil's). -/
noncomputable def KW34 (p : ℕ) : ℕ := ⌊(p : ℝ) ^ (3 / 4 : ℝ) * Real.log p ^ 4⌋₊

lemma KW_eq (p : ℕ) : KW p = KWθ (1 / 2) p := by
  unfold KW KWθ; rw [Real.sqrt_eq_rpow]

lemma KW34_eq (p : ℕ) : KW34 p = KWθ (3 / 4) p := rfl

/-- `R_K(p) = ∑_{3 ≤ k < K, k odd} F_k(p)/k²`. -/
noncomputable def RsumK (K p : ℕ) : ℝ :=
  ∑ k ∈ (Ico 3 K).filter Odd, Fsum k p / (k : ℝ) ^ 2

/-- `R_{K_W}(p) = ∑_{3 ≤ k < K_W, k odd} F_k(p)/k²`, with `F_k(p) = ∑_{t=1}^{(k-1)/2} tan(π p t/k)`
(`Fsum`). -/
noncomputable def Rsum (p : ℕ) : ℝ :=
  ∑ k ∈ (Ico 3 (KW p)).filter Odd, Fsum k p / (k : ℝ) ^ 2

/-- **(HB)** One-sided form of Theorem B(ii) of the paper with `K = K_W`:
  `S(p) ≥ (p/2) log p + (4p/π) R_{K_W}(p) - C p` for all large primes `p`.
Theorem B(ii) states `S(p) = (p/2) log p + c₀ p + (4p/π) R_K(p) + O(p / log p)` for
`√p (log p)^4 ≤ K ≤ p^{9/10}`; this implies (HB) with any `C > |c₀|` (and is much stronger).
Its proof uses only Weil's bound for Kloosterman sums (paper §3–§5). -/
def HB : Prop :=
  ∃ C : ℝ, ∀ᶠ p : ℕ in Filter.atTop, p.Prime →
    (p : ℝ) / 2 * Real.log p + 4 * p / Real.pi * Rsum p - C * p ≤ (S p : ℝ)

/-- **(HBweak)** The two-sided form of Theorem B(ii) with `K = K_W` and an unspecified error `O(p)`:
  `|S(p) - (p/2) log p - c p - (4p/π) R_{K_W}(p)| ≤ C p` for all large primes `p`.
This is the statement the companion project derives from Weil's bound; it implies (HB). -/
def HBweak : Prop :=
  ∃ c C : ℝ, ∀ᶠ p : ℕ in Filter.atTop, p.Prime →
    |(S p : ℝ) - p / 2 * Real.log p - c * p -
        4 * p / Real.pi * ∑ k ∈ (Finset.Ico 3 (KW p)).filter Odd, Fsum k p / (k : ℝ) ^ 2| ≤ C * p

theorem HB_of_HBweak (h : HBweak) : HB := by
  obtain ⟨c, C, hC⟩ := h
  refine ⟨C + |c|, ?_⟩
  filter_upwards [hC] with p hp hpr
  have h1 := (abs_le.mp (hp hpr)).1
  have h2 : -|c| * p ≤ c * p := mul_le_mul_of_nonneg_right (neg_abs_le c) (Nat.cast_nonneg p)
  unfold Rsum
  rw [add_mul]
  linarith

/-- **(HB34)** (HB) with the cutoff `KW34` in place of `KW`. -/
def HB34 : Prop :=
  ∃ C : ℝ, ∀ᶠ p : ℕ in Filter.atTop, p.Prime →
    (p : ℝ) / 2 * Real.log p + 4 * p / Real.pi * RsumK (KW34 p) p - C * p ≤ (S p : ℝ)

/-- **(HBweak34)** (HBweak) with the cutoff `KW34 = ⌊p^{3/4} (log p)^4⌋` in place of `KW`. -/
def HBweak34 : Prop :=
  ∃ c C : ℝ, ∀ᶠ p : ℕ in Filter.atTop, p.Prime →
    |(S p : ℝ) - p / 2 * Real.log p - c * p -
        4 * p / Real.pi * ∑ k ∈ (Finset.Ico 3 (KW34 p)).filter Odd, Fsum k p / (k : ℝ) ^ 2| ≤ C * p

theorem HB34_of_HBweak34 (h : HBweak34) : HB34 := by
  obtain ⟨c, C, hC⟩ := h
  refine ⟨C + |c|, ?_⟩
  filter_upwards [hC] with p hp hpr
  have h1 := (abs_le.mp (hp hpr)).1
  have h2 : -|c| * p ≤ c * p := mul_le_mul_of_nonneg_right (neg_abs_le c) (Nat.cast_nonneg p)
  unfold RsumK
  rw [add_mul]
  linarith

/-- **(HV)** Vaaler's lemma (J. D. Vaaler, *Some extremal functions in Fourier analysis*,
Bull. AMS 12 (1985), Thm. 18; Graham–Kolesnik, *Van der Corput's method of exponential sums*,
Thm. A.6), in its real (sine-polynomial) form and only at non-integers: for every `H ≥ 1` there
are real `c_h` (`1 ≤ h ≤ H`), `|c_h| ≤ 1/(π h)`, such that for every real `x ∉ ℤ`
  `|((x)) - ∑_{h=1}^H c_h sin(2π h x)| ≤ (1/(2H+2)) (1 + 2 ∑_{h=1}^H (1 - h/(H+1)) cos(2π h x))`,
where `((x)) = x - ⌊x⌋ - 1/2`. (Vaaler's polynomial is
`-(1/π) ∑ V(h/(H+1)) sin(2π h x)/h` with `0 ≤ V ≤ 1`, and the right side is
`(1/(2H+2)) ∑_{|h| ≤ H} (1 - |h|/(H+1)) e(hx)`.)
(HV) is proved, as `ThetaSum.hV_holds` in `HVProof.lean`, from the formalized Vaaler lemma. -/
def HV : Prop :=
  ∀ H : ℕ, 1 ≤ H → ∃ c : ℕ → ℝ, (∀ h, 1 ≤ h → h ≤ H → |c h| ≤ 1 / (Real.pi * h)) ∧
    ∀ x : ℝ, (∀ m : ℤ, x ≠ m) →
      |(x - ⌊x⌋ - 1 / 2) - ∑ h ∈ Icc 1 H, c h * Real.sin (2 * Real.pi * h * x)| ≤
        1 / (2 * H + 2) *
          (1 + 2 * ∑ h ∈ Icc 1 H, (1 - (h : ℝ) / (H + 1)) * Real.cos (2 * Real.pi * h * x))

/-- The additive character `e(x/p)` of `ZMod p`. -/
noncomputable def psiP (p : ℕ) (x : ZMod p) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((x.val : ℝ) / p))

/-- **(HBG)** The Bourgain–Garaev bound for short Kloosterman sums (J. Bourgain and
M. Z. Garaev, *Sumsets of reciprocals in prime fields and multilinear Kloosterman sums*,
Izv. Math. 78 (2014); arXiv:1211.4184, Theorem 16), stated only in the range
`log N ≥ (log p)^{9/10} / 2`. Their proof (§12.2) covers
`log N ≥ A (log p)^{2/3} (log log p)^{8/3}` for an absolute `A`, which contains this range for all
large `p` (see the paper, Lemma 6.5): for all large primes `p`, all `b ≢ 0 (mod p)` and all `N < p`
with `log N ≥ (log p)^{9/10}/2`,
  `|∑_{n=1}^N e(b n^*/p)| ≤ C (log log p)^3 (log p) (log N)^{-3/2} N`. -/
def HBG : Prop :=
  ∃ C : ℝ, ∀ᶠ p : ℕ in Filter.atTop, p.Prime →
    ∀ b : ZMod p, b ≠ 0 → ∀ N : ℕ, Real.log p ^ (9 / 10 : ℝ) / 2 ≤ Real.log N → N < p →
      ‖∑ n ∈ Icc 1 N, psiP p (b * (n : ZMod p)⁻¹)‖ ≤
        C * Real.log (Real.log p) ^ 3 * Real.log p * Real.log N ^ (-(3 / 2 : ℝ)) * N

end ThetaSum
