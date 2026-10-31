import ThetaSum.Hypotheses

/-!
# Kloosterman's bound `|K(b, ℓ)| ≤ 2 p^{3/4}` (Kloosterman 1926)

For a prime `p` and `b ≠ 0`, the Kloosterman sum `K(b, ℓ) = ∑_{z ≠ 0} e((b z⁻¹ + ℓ z)/p)` satisfies
`|K(b, ℓ)|⁴ ≤ 3 p³`, hence `|K(b, ℓ)| ≤ 3^{1/4} p^{3/4} ≤ 2 p^{3/4}`.

Proof (fourth moment):
* `K(b, ℓ) = K(1, bℓ)` for `b ≠ 0` (substitute `z = b w`);
* `∑_{b, ℓ} |K(b, ℓ)|⁴ = p² · #{x ∈ (𝔽_p^×)⁴ : x₁ + x₂ = x₃ + x₄, x₁⁻¹ + x₂⁻¹ = x₃⁻¹ + x₄⁻¹}`
  (orthogonality of additive characters);
* the solutions are `(a, c, a, c)`, `(a, c, c, a)` and `(a, -a, c, -c)`, so there are at most
  `3 (p - 1)²`;
* the `p - 1` pairs `(b', b'⁻¹ a)`, `b' ≠ 0`, all have `K = K(1, a)`, so
  `(p - 1) |K(1, a)|⁴ ≤ 3 p² (p - 1)²`.
-/

open Finset

namespace ThetaSum

section Kloosterman

variable {p : ℕ} [hp : Fact p.Prime]

lemma psiP_eq_std (x : ZMod p) : psiP p x = ZMod.stdAddChar x := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]; unfold psiP; congr 1; push_cast; ring

/-- The nonzero residues. -/
noncomputable abbrev Unz (p : ℕ) [Fact p.Prime] : Finset (ZMod p) := univ.filter (· ≠ 0)

lemma card_Unz : (Unz p).card = p - 1 := by
  rw [Unz, filter_ne', card_erase_of_mem (mem_univ _), card_univ, ZMod.card]

/-- The Kloosterman sum `K(b, ℓ) = ∑_{z ≠ 0} e((b z⁻¹ + ℓ z)/p)`. -/
noncomputable def kl (b ℓ : ZMod p) : ℂ :=
  ∑ z ∈ Unz p, ZMod.stdAddChar (b * z⁻¹ + ℓ * z)

lemma kl_eq (b ℓ : ZMod p) (hb : b ≠ 0) : kl b ℓ = kl 1 (b * ℓ) := by
  unfold kl
  symm
  apply Finset.sum_nbij' (fun w => b * w) (fun z => b⁻¹ * z)
  · intro w hw; simp only [mem_filter, mem_univ, true_and] at hw ⊢; exact mul_ne_zero hb hw
  · intro z hz; simp only [mem_filter, mem_univ, true_and] at hz ⊢
    exact mul_ne_zero (inv_ne_zero hb) hz
  · intro w _; rw [← mul_assoc, inv_mul_cancel₀ hb, one_mul]
  · intro z _; rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul]
  · intro w _
    congr 1
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hb]; ring

/-- The two equations of the fourth moment, as residues: `A = x₁⁻¹ + x₂⁻¹ - x₃⁻¹ - x₄⁻¹`. -/
def eqA (x : ZMod p × ZMod p × ZMod p × ZMod p) : ZMod p :=
  x.1⁻¹ + x.2.1⁻¹ - x.2.2.1⁻¹ - x.2.2.2⁻¹

/-- `B = x₁ + x₂ - x₃ - x₄`. -/
def eqB (x : ZMod p × ZMod p × ZMod p × ZMod p) : ZMod p :=
  x.1 + x.2.1 - x.2.2.1 - x.2.2.2

lemma conj_kl (b ℓ : ZMod p) :
    (starRingEnd ℂ) (kl b ℓ) = ∑ z ∈ Unz p, ZMod.stdAddChar (-(b * z⁻¹ + ℓ * z)) := by
  unfold kl; rw [map_sum]
  exact sum_congr rfl fun z _ => (AddChar.map_neg_eq_conj _ _).symm

lemma kl_four (b ℓ : ZMod p) :
    ((‖kl b ℓ‖ ^ 4 : ℝ) : ℂ) =
      ∑ x ∈ Unz p ×ˢ Unz p ×ˢ Unz p ×ˢ Unz p, ZMod.stdAddChar (b * eqA x + ℓ * eqB x) := by
  have h1 : ((‖kl b ℓ‖ ^ 4 : ℝ) : ℂ) =
      (starRingEnd ℂ) (kl b ℓ) * (starRingEnd ℂ) (kl b ℓ) * kl b ℓ * kl b ℓ := by
    have := Complex.mul_conj (kl b ℓ)
    rw [Complex.normSq_eq_norm_sq] at this
    calc ((‖kl b ℓ‖ ^ 4 : ℝ) : ℂ) = ((‖kl b ℓ‖ ^ 2 : ℝ) : ℂ) * ((‖kl b ℓ‖ ^ 2 : ℝ) : ℂ) := by
          push_cast; ring
      _ = _ := by rw [← this]; ring
  rw [h1, conj_kl]
  unfold kl
  simp only [sum_product, sum_mul, mul_sum]
  refine sum_congr rfl fun x1 _ => sum_congr rfl fun x2 _ => sum_congr rfl fun x3 _ =>
    sum_congr rfl fun x4 _ => ?_
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  unfold eqA eqB; ring

/-- The solutions of `x₁ + x₂ = x₃ + x₄`, `x₁⁻¹ + x₂⁻¹ = x₃⁻¹ + x₄⁻¹` in `(𝔽_p^×)⁴`. -/
noncomputable def Sol (p : ℕ) [Fact p.Prime] : Finset (ZMod p × ZMod p × ZMod p × ZMod p) :=
  (Unz p ×ˢ Unz p ×ˢ Unz p ×ˢ Unz p).filter (fun x => eqA x = 0 ∧ eqB x = 0)

lemma moment :
    ∑ b : ZMod p, ∑ ℓ : ZMod p, ‖kl b ℓ‖ ^ 4 = (p : ℝ) ^ 2 * (Sol p).card := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, kl_four]
  have hψ := ZMod.isPrimitive_stdAddChar p
  calc ∑ b : ZMod p, ∑ ℓ : ZMod p, ∑ x ∈ Unz p ×ˢ Unz p ×ˢ Unz p ×ˢ Unz p,
        ZMod.stdAddChar (b * eqA x + ℓ * eqB x)
      = ∑ b : ZMod p, ∑ x ∈ Unz p ×ˢ Unz p ×ˢ Unz p ×ˢ Unz p, ∑ ℓ : ZMod p,
        ZMod.stdAddChar (b * eqA x + ℓ * eqB x) := sum_congr rfl fun b _ => sum_comm
    _ = ∑ x ∈ Unz p ×ˢ Unz p ×ˢ Unz p ×ˢ Unz p, ∑ b : ZMod p, ∑ ℓ : ZMod p,
        ZMod.stdAddChar (b * eqA x + ℓ * eqB x) := sum_comm
    _ = ∑ x ∈ Unz p ×ˢ Unz p ×ˢ Unz p ×ˢ Unz p, (∑ b : ZMod p, ZMod.stdAddChar (b * eqA x)) *
        ∑ ℓ : ZMod p, ZMod.stdAddChar (ℓ * eqB x) := by
          refine sum_congr rfl fun x _ => ?_
          rw [sum_mul_sum]
          exact sum_congr rfl fun b _ => sum_congr rfl fun ℓ _ => AddChar.map_add_eq_mul _ _ _
    _ = ∑ x ∈ Unz p ×ˢ Unz p ×ˢ Unz p ×ˢ Unz p,
        if eqA x = 0 ∧ eqB x = 0 then ((p : ℂ) ^ 2) else 0 := by
          refine sum_congr rfl fun x _ => ?_
          rw [AddChar.sum_mulShift _ hψ, AddChar.sum_mulShift _ hψ, ZMod.card]
          by_cases hA : eqA x = 0 <;> by_cases hB : eqB x = 0 <;> simp [hA, hB, sq]
    _ = _ := by
          rw [← sum_filter, sum_const, nsmul_eq_mul]; unfold Sol; push_cast; ring

lemma Sol_subset : Sol p ⊆
    ((Unz p ×ˢ Unz p).image fun y => (y.1, y.2, y.1, y.2)) ∪
    ((Unz p ×ˢ Unz p).image fun y => (y.1, y.2, y.2, y.1)) ∪
    ((Unz p ×ˢ Unz p).image fun y => (y.1, -y.1, y.2, -y.2)) := by
  rintro ⟨x1, x2, x3, x4⟩ hx
  unfold Sol at hx
  rw [mem_filter] at hx
  simp only [mem_product, Unz, mem_filter, mem_univ, true_and, eqA, eqB] at hx
  obtain ⟨⟨h1, h2, h3, h4⟩, hA, hB⟩ := hx
  simp only [mem_union, mem_image, mem_product, mem_filter, mem_univ, true_and, ne_eq,
    Prod.exists, Prod.mk.injEq]
  by_cases hs : x1 + x2 = 0
  · right
    refine ⟨x1, x3, ⟨h1, h3⟩, rfl, ?_, rfl, ?_⟩
    · linear_combination -hs
    · linear_combination hB - hs
  · left
    have hA' : (x1 + x2) * (x3 * x4 - x1 * x2) = 0 := by
      field_simp at hA
      linear_combination hA - (x1 * x2) * hB
    have hP : x3 * x4 = x1 * x2 := by
      have := (mul_eq_zero.mp hA').resolve_left hs
      linear_combination this
    have hq : (x3 - x1) * (x3 - x2) = 0 := by linear_combination (-x3) * hB - hP
    rcases mul_eq_zero.mp hq with h | h
    · left
      refine ⟨x1, x2, ⟨h1, h2⟩, rfl, rfl, ?_, ?_⟩
      · linear_combination -h
      · linear_combination hB + h
    · right
      refine ⟨x1, x2, ⟨h1, h2⟩, rfl, rfl, ?_, ?_⟩
      · linear_combination -h
      · linear_combination hB + h

lemma card_Sol : (Sol p).card ≤ 3 * (p - 1) ^ 2 := by
  refine (card_le_card Sol_subset).trans ?_
  refine (card_union_le _ _).trans ?_
  have hc : (Unz p ×ˢ Unz p).card = (p - 1) ^ 2 := by rw [card_product, card_Unz, sq]
  have e1 := card_image_le (s := Unz p ×ˢ Unz p) (f := fun y => (y.1, y.2, y.1, y.2))
  have e2 := card_image_le (s := Unz p ×ˢ Unz p) (f := fun y => (y.1, y.2, y.2, y.1))
  have e3 := card_image_le (s := Unz p ×ˢ Unz p) (f := fun y => (y.1, -y.1, y.2, -y.2))
  have e12 := card_union_le ((Unz p ×ˢ Unz p).image fun y => (y.1, y.2, y.1, y.2))
    ((Unz p ×ˢ Unz p).image fun y => (y.1, y.2, y.2, y.1))
  omega

/-- **Kloosterman's bound, fourth-power form**: `|K(b, ℓ)|⁴ ≤ 3 p³` for `b ≠ 0`. -/
theorem kl_four_le (b ℓ : ZMod p) (hb : b ≠ 0) : ‖kl b ℓ‖ ^ 4 ≤ 3 * (p : ℝ) ^ 3 := by
  have hp2 := hp.out.two_le
  have hp1R : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  set a := b * ℓ
  have hnn : ∀ b' ℓ' : ZMod p, 0 ≤ ‖kl b' ℓ'‖ ^ 4 := fun _ _ => by positivity
  have key : ((p : ℝ) - 1) * ‖kl 1 a‖ ^ 4 ≤ (p : ℝ) ^ 2 * (3 * ((p : ℝ) - 1) ^ 2) := by
    calc ((p : ℝ) - 1) * ‖kl 1 a‖ ^ 4 = ∑ b' ∈ Unz p, ‖kl b' (b'⁻¹ * a)‖ ^ 4 := by
          rw [sum_congr rfl fun b' hb' => by
            rw [kl_eq b' _ (by simpa using hb'), ← mul_assoc,
              mul_inv_cancel₀ (by simpa using hb'), one_mul]]
          rw [sum_const, card_Unz, nsmul_eq_mul, hp1R]
      _ ≤ ∑ b' ∈ Unz p, ∑ ℓ' : ZMod p, ‖kl b' ℓ'‖ ^ 4 :=
          sum_le_sum fun b' _ => single_le_sum (fun ℓ' _ => hnn b' ℓ') (mem_univ _)
      _ ≤ ∑ b' : ZMod p, ∑ ℓ' : ZMod p, ‖kl b' ℓ'‖ ^ 4 :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _)
            fun b' _ _ => sum_nonneg fun ℓ' _ => hnn b' ℓ'
      _ = (p : ℝ) ^ 2 * (Sol p).card := moment
      _ ≤ (p : ℝ) ^ 2 * (3 * ((p : ℝ) - 1) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h := card_Sol (p := p)
          have : ((Sol p).card : ℝ) ≤ ((3 * (p - 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast h
          rw [Nat.cast_mul, Nat.cast_pow, hp1R] at this
          exact_mod_cast this
  have h2 : ‖kl 1 a‖ ^ 4 ≤ 3 * (p : ℝ) ^ 2 * ((p : ℝ) - 1) := by
    refine le_of_mul_le_mul_left ?_ hpos
    calc ((p : ℝ) - 1) * ‖kl 1 a‖ ^ 4 ≤ (p : ℝ) ^ 2 * (3 * ((p : ℝ) - 1) ^ 2) := key
      _ = ((p : ℝ) - 1) * (3 * (p : ℝ) ^ 2 * ((p : ℝ) - 1)) := by ring
  rw [kl_eq b ℓ hb]
  calc ‖kl 1 a‖ ^ 4 ≤ 3 * (p : ℝ) ^ 2 * ((p : ℝ) - 1) := h2
    _ ≤ 3 * (p : ℝ) ^ 3 := by
        have : (0 : ℝ) ≤ 3 * (p : ℝ) ^ 2 := by positivity
        nlinarith

/-- **Kloosterman's bound** (Kloosterman 1926): for a prime `p`, `b ≢ 0` and any `ℓ`,
`|∑_{z ≠ 0} e((b z⁻¹ + ℓ z)/p)| ≤ 2 p^{3/4}` (in fact `≤ 3^{1/4} p^{3/4}`). -/
theorem kloosterman_bound (b ℓ : ZMod p) (hb : b ≠ 0) :
    ‖∑ z ∈ univ.filter (· ≠ (0 : ZMod p)), psiP p (b * z⁻¹ + ℓ * z)‖ ≤
      2 * (p : ℝ) ^ (3 / 4 : ℝ) := by
  have e : ∑ z ∈ univ.filter (· ≠ (0 : ZMod p)), psiP p (b * z⁻¹ + ℓ * z) = kl b ℓ := by
    unfold kl; exact sum_congr rfl fun z _ => psiP_eq_std _
  rw [e]
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have h16 : (2 * (p : ℝ) ^ (3 / 4 : ℝ)) ^ 4 = 16 * (p : ℝ) ^ 3 := by
    rw [mul_pow, ← Real.rpow_natCast ((p : ℝ) ^ (3 / 4 : ℝ)), ← Real.rpow_mul hp0]
    norm_num
  have hle : ‖kl b ℓ‖ ^ 4 ≤ (2 * (p : ℝ) ^ (3 / 4 : ℝ)) ^ 4 := by
    rw [h16]; have := kl_four_le b ℓ hb; have : (0 : ℝ) ≤ (p : ℝ) ^ 3 := by positivity
    linarith
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hle

end Kloosterman

/-- **(HK34)** Kloosterman's bound `|K(b, ℓ)| ≤ 2 p^{3/4}` (proved: `hK34`). -/
def HK34 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (b ℓ : ZMod p), b ≠ 0 →
    ‖∑ z ∈ Finset.univ.filter (· ≠ (0 : ZMod p)), psiP p (b * z⁻¹ + ℓ * z)‖ ≤
      2 * (p : ℝ) ^ (3 / 4 : ℝ)

theorem hK34 : HK34 := fun _ _ b ℓ hb => kloosterman_bound b ℓ hb

end ThetaSum

#print axioms ThetaSum.kl_four_le
#print axioms ThetaSum.hK34
