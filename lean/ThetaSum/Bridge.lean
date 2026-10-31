import ThetaSum.Hypotheses

/-
The bridge between the two descriptions of the signs in Lemma 6.1.

For an odd prime `p`, odd `k < p`, `u` with `k ∣ 2pu - 1` (so `θ_k = u/k`) and `w` with
`p ∣ 2kw - 1` (so `w ≡ (2k)^{-1} mod p`), and odd `n` with `1 ≤ n < k`:
  `g(n u / k) = g(n w / p)`.
Thus the sign form of Lemma 6.1 can be written with the Kloosterman fractions `n (2k)^{-1} / p`,
whose sums over `k` are the incomplete Kloosterman sums of Lemmas 6.4–6.6.
(Proof: `2pu + 2kw - 1 = pkm` with `m` odd, so `nu/k = nm/2 + n/(2pk) - nw/p`.)
-/

open Finset

namespace ThetaSum

theorem bridge (p k n : ℕ) (u : ℤ) (w : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k)
    (hkp : k < p) (hu : (k : ℤ) ∣ 2 * p * u - 1) (hw : (p : ℤ) ∣ 2 * k * w - 1)
    (hn : Odd n) (hnk : n < k) :
    gsq (n * ((u : ℝ) / k)) = gsq (n * (w : ℝ) / p) := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hn1 : 1 ≤ n := by obtain ⟨r, hr⟩ := hn; omega
  -- `X = 2pu + 2kw - 1 = kpm`, `m` odd
  have hkX : (k : ℤ) ∣ 2 * p * u + 2 * k * w - 1 := by
    have : 2 * (p : ℤ) * u + 2 * k * w - 1 = (2 * p * u - 1) + k * (2 * w) := by ring
    rw [this]; exact dvd_add hu (dvd_mul_right _ _)
  have hpX : (p : ℤ) ∣ 2 * p * u + 2 * k * w - 1 := by
    have : 2 * (p : ℤ) * u + 2 * k * w - 1 = (2 * k * w - 1) + p * (2 * u) := by ring
    rw [this]; exact dvd_add hw (dvd_mul_right _ _)
  have hcop : IsCoprime (k : ℤ) (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : Nat.Coprime k p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro h; have := Nat.le_of_dvd (by omega) h; omega
    exact_mod_cast this
  obtain ⟨m, hm⟩ := hcop.mul_dvd hkX hpX
  have hmodd : Odd m := by
    rcases Int.even_or_odd m with ⟨r, hr⟩ | h
    · exfalso
      have h1 : (1 : ℤ) = 2 * (p * u + k * w - k * p * r) := by
        have : 2 * (p : ℤ) * u + 2 * k * w - 1 = 2 * (k * p * r) := by rw [hm, hr]; ring
        linarith
      obtain ⟨t, ht⟩ : ∃ t : ℤ, (1 : ℤ) = 2 * t := ⟨_, h1⟩
      omega
    · exact h
  obtain ⟨r, hr⟩ := hmodd
  obtain ⟨n2, hn2⟩ := hn
  -- `n m = 2 s + 1`
  set s : ℤ := 2 * n2 * r + n2 + r
  have hnm : (n : ℤ) * m = 2 * s + 1 := by rw [hr]; push_cast [hn2]; ring
  -- `n w = p q + j`
  set q := n * w / p
  set j := n * w % p
  have hnw : n * w = p * q + j := (Nat.div_add_mod _ _).symm
  have hjp : j < p := Nat.mod_lt _ hp0
  have hj0 : 1 ≤ j := by
    by_contra h
    have hj : j = 0 := by omega
    have hdvd : p ∣ n * w := Nat.dvd_of_mod_eq_zero hj
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
    · have := Nat.le_of_dvd (by omega) h1; omega
    · -- `p ∣ w` contradicts `p ∣ 2kw - 1`
      obtain ⟨c, hc⟩ := h1
      have : (p : ℤ) ∣ 1 := by
        have e : (1 : ℤ) = 2 * k * w - (2 * k * w - 1) := by ring
        rw [e]; refine dvd_sub ?_ hw
        rw [hc]; push_cast; exact ⟨2 * k * c, by ring⟩
      have := Int.eq_one_of_dvd_one (by positivity) this
      have : p = 1 := by exact_mod_cast this
      exact hp.one_lt.ne' this
  have hj2 : 2 * j ≠ p := by
    intro h; obtain ⟨t, ht⟩ := hpodd; omega
  -- the two real numbers
  have hy1 : (n : ℝ) * ((u : ℝ) / k) =
      (s - q : ℤ) + (1 / 2 + n / (2 * p * k) - j / p) := by
    have hX : (2 * (p : ℝ) * u) = (k * p * m : ℤ) + 1 - 2 * k * w := by
      have : (2 * (p : ℤ) * u) = k * p * m + 1 - 2 * k * w := by linarith
      exact_mod_cast this
    have hnmR : (n : ℝ) * m = 2 * s + 1 := by exact_mod_cast hnm
    have hnwR : (n : ℝ) * w = p * q + j := by exact_mod_cast hnw
    have hXR : 2 * (p : ℝ) * u = k * p * m + 1 - 2 * k * w := by push_cast at hX; exact hX
    have e : (n : ℝ) * ((u : ℝ) / k) = n * (2 * p * u) / (2 * p * k) := by
      field_simp
    have key : (n : ℝ) * ((u : ℝ) / k) = n * m / 2 + n / (2 * p * k) - n * w / p := by
      rw [e, hXR]; field_simp
    rw [key, hnmR, hnwR]
    push_cast
    field_simp
    ring
  have hy2 : (n : ℝ) * w / p = (q : ℤ) + (j : ℝ) / p := by
    have hnwR : (n : ℝ) * w = p * q + j := by exact_mod_cast hnw
    rw [hnwR]; push_cast; field_simp
  have hδ0 : (0 : ℝ) < n / (2 * p * k) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn1
    positivity
  have hδ1 : (n : ℝ) / (2 * p * k) < 1 / (2 * p) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have : (n : ℝ) < k := by exact_mod_cast hnk
    nlinarith
  have hjR1 : (1 : ℝ) ≤ j := by exact_mod_cast hj0
  have hjRp : (j : ℝ) < p := by exact_mod_cast hjp
  unfold gsq
  have hf2 : Int.fract ((n : ℝ) * w / p) = j / p := by
    rw [hy2, Int.fract_intCast_add, Int.fract_eq_self]
    exact ⟨by positivity, by rw [div_lt_one hpR]; exact hjRp⟩
  rcases Nat.lt_or_gt_of_ne hj2 with hlt | hgt
  · -- `2j < p`: both are `< 1/2`
    have hjR : 2 * (j : ℝ) < p := by exact_mod_cast hlt
    have hf1 : Int.fract ((n : ℝ) * ((u : ℝ) / k)) = 1 / 2 + n / (2 * p * k) - j / p := by
      rw [hy1, Int.fract_intCast_add, Int.fract_eq_self]
      constructor
      · have : (j : ℝ) / p ≤ 1 / 2 - 1 / (2 * p) := by
          rw [div_le_iff₀ hpR]; field_simp
          have : 2 * (j : ℝ) + 1 ≤ p := by exact_mod_cast hlt
          linarith
        linarith
      · have : (1 : ℝ) / p ≤ j / p := div_le_div_of_nonneg_right hjR1 hpR.le
        have : 1 / (2 * (p : ℝ)) ≤ 1 / p := by
          apply div_le_div_of_nonneg_left (by norm_num) hpR; linarith
        linarith
    have h1 : 1 / 2 + (n : ℝ) / (2 * p * k) - j / p < 1 / 2 := by
      have : (1 : ℝ) / p ≤ j / p := div_le_div_of_nonneg_right hjR1 hpR.le
      have : 1 / (2 * (p : ℝ)) ≤ 1 / p := by
        apply div_le_div_of_nonneg_left (by norm_num) hpR; linarith
      linarith
    have h2 : (j : ℝ) / p < 1 / 2 := by rw [div_lt_iff₀ hpR]; linarith
    rw [hf1, hf2, if_pos h1, if_pos h2]
  · -- `2j > p`: both are `≥ 1/2`
    have hjR : (p : ℝ) + 1 ≤ 2 * j := by exact_mod_cast hgt
    have hf1 : Int.fract ((n : ℝ) * ((u : ℝ) / k)) = 3 / 2 + n / (2 * p * k) - j / p := by
      have e : ((s - q : ℤ) : ℝ) + (1 / 2 + n / (2 * p * k) - j / p) =
          ((s - q - 1 : ℤ) : ℝ) + (3 / 2 + n / (2 * p * k) - j / p) := by push_cast; ring
      rw [hy1, e, Int.fract_intCast_add, Int.fract_eq_self]
      have hjp1 : (j : ℝ) / p < 1 := by rw [div_lt_one hpR]; exact hjRp
      have hjp2 : 1 / 2 + 1 / (2 * (p : ℝ)) ≤ j / p := by
        rw [le_div_iff₀ hpR]; field_simp; linarith
      constructor <;> linarith
    have h1 : ¬ (3 / 2 + (n : ℝ) / (2 * p * k) - j / p < 1 / 2) := by
      have hjp1 : (j : ℝ) / p < 1 := by rw [div_lt_one hpR]; exact hjRp
      linarith
    have h2 : ¬ ((j : ℝ) / p < 1 / 2) := by
      rw [not_lt, le_div_iff₀ hpR]; linarith
    rw [hf1, hf2, if_neg h1, if_neg h2]

/-- An inverse of `2p` modulo `k`: `k ∣ 2 p u_k - 1` for `k` coprime to `2p`. -/
noncomputable def uInv (p k : ℕ) : ℤ := ((((2 * p : ℕ) : ZMod k))⁻¹).val

lemma uInv_spec (p k : ℕ) (hk : 0 < k) (h : Nat.Coprime (2 * p) k) :
    (k : ℤ) ∣ 2 * p * uInv p k - 1 := by
  haveI : NeZero k := ⟨by omega⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h1 := ZMod.coe_mul_inv_eq_one (2 * p) h
  unfold uInv
  push_cast
  rw [ZMod.natCast_zmod_val]
  rw [show ((2 : ZMod k) * p) = ((2 * p : ℕ) : ZMod k) by push_cast; ring, h1]
  ring

/-- `w_k = ((2k)^{-1} mod p)` as a natural number in `[0, p)`. -/
noncomputable def wInv (p k : ℕ) : ℕ := ((((2 * k : ℕ) : ZMod p))⁻¹).val

lemma wInv_spec (p k : ℕ) (hp : p.Prime) (h : ¬ p ∣ 2 * k) : (p : ℤ) ∣ 2 * k * wInv p k - 1 := by
  haveI := Fact.mk hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hne : ((2 * k : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact h
  unfold wInv
  push_cast
  rw [ZMod.natCast_zmod_val]
  rw [show ((2 : ZMod p) * k) = ((2 * k : ℕ) : ZMod p) by push_cast; ring, mul_inv_cancel₀ hne]
  ring

end ThetaSum

#print axioms ThetaSum.bridge
