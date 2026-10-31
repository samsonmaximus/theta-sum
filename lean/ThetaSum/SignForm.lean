import Mathlib

/-
**Lemma 6.1** of the paper (sign form of the tangent sums). Let `k ≥ 3` be odd, `p` coprime
to `k`, and `u` an integer with `k ∣ 2 p u - 1` (so `θ_k = u/k` modulo 1). Then
  `F_k(p) = ∑_{t=1}^{(k-1)/2} tan(π p t / k) = - ∑_{0<n<k, n odd} cot(π n / (2k)) · g(n θ_k)`,
where `g(y) = sgn(1/2 - {y})` (`= 1` if `{y} < 1/2`, `= -1` otherwise; `n θ_k ∉ ½ℤ` here).
-/

open Finset

namespace ThetaSum

/-- `F_k(p) = ∑_{t=1}^{(k-1)/2} tan(π p t / k)`. -/
noncomputable def Fsum (k p : ℕ) : ℝ := ∑ t ∈ Icc 1 ((k - 1) / 2), Real.tan (Real.pi * p * t / k)

/-- The square wave `g(y) = sgn(1/2 - {y})`, with value `-1` at `{y} = 1/2`. -/
noncomputable def gsq (y : ℝ) : ℝ := if Int.fract y < 1 / 2 then 1 else -1

lemma fract_div (m : ℤ) (k : ℕ) (hk : 0 < k) :
    Int.fract ((m : ℝ) / k) = ((m % (k : ℤ) : ℤ) : ℝ) / k := by
  have := Int.fract_div_intCast_eq_div_intCast_mod (k := ℝ) (m := m) (n := k)
  simpa using this

/-- **Lemma 6.1.** -/
theorem sign_form (k p : ℕ) (u : ℤ) (hk : 3 ≤ k) (hodd : Odd k) (hcop : Nat.Coprime p k)
    (hu : (k : ℤ) ∣ 2 * p * u - 1) :
    Fsum k p = -∑ n ∈ (Ioo 0 k).filter Odd,
      Real.cot (Real.pi * n / (2 * k)) * gsq (n * (u : ℝ) / k) := by
  obtain ⟨h, hh⟩ := hodd
  have hhk : (k - 1) / 2 = h := by omega
  have hk0 : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hpi := Real.pi_pos
  -- `x t = p t mod k`, the sign `s t` and the index `n t`
  set x : ℕ → ℕ := fun t => p * t % k
  set nn : ℕ → ℕ := fun t => if x t ≤ h then k - 2 * x t else 2 * x t - k
  set s : ℕ → ℝ := fun t => if x t ≤ h then 1 else -1
  have hx_pos : ∀ t ∈ Icc 1 h, 1 ≤ x t := by
    intro t ht
    simp only [mem_Icc] at ht
    by_contra hc
    have h0 : p * t % k = 0 := by simp only [x] at hc; omega
    have hdvd : k ∣ p * t := Nat.dvd_of_mod_eq_zero h0
    have : k ∣ t := (Nat.Coprime.dvd_of_dvd_mul_left hcop.symm hdvd)
    have := Nat.le_of_dvd (by omega) this
    omega
  have hx_lt : ∀ t, x t < k := fun t => Nat.mod_lt _ hk0
  -- Claim A: each tangent equals `s t · cot(π n_t / 2k)`
  have hA : ∀ t ∈ Icc 1 h, Real.tan (Real.pi * p * t / k) =
      s t * Real.cot (Real.pi * (nn t) / (2 * k)) := by
    intro t ht
    have hx1 := hx_pos t ht
    have hxk := hx_lt t
    have hdec : p * t = k * (p * t / k) + x t := (Nat.div_add_mod (p * t) k).symm
    have hper : Real.tan (Real.pi * p * t / k) = Real.tan (Real.pi * (x t) / k) := by
      have e : Real.pi * p * t / k = Real.pi * (x t) / k + ((p * t / k : ℕ) : ℝ) * Real.pi := by
        have : ((p * t : ℕ) : ℝ) = k * ((p * t / k : ℕ) : ℝ) + (x t : ℝ) := by
          exact_mod_cast hdec
        push_cast at this
        field_simp
        linarith
      rw [e, Real.tan_add_nat_mul_pi]
    rw [hper]
    simp only [s, nn]
    split_ifs with hxh
    · -- `π x / k = π/2 - z`, `z = π (k - 2x) / (2k)`
      have e : Real.pi * (x t) / k = Real.pi / 2 - Real.pi * ((k - 2 * x t : ℕ) : ℝ) / (2 * k) := by
        have : ((k - 2 * x t : ℕ) : ℝ) = k - 2 * x t := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [this]; field_simp; ring
      rw [e, Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub,
        Real.cot_eq_cos_div_sin, one_mul]
    · have e : Real.pi * (x t) / k = Real.pi * ((2 * x t - k : ℕ) : ℝ) / (2 * k) + Real.pi / 2 := by
        have : ((2 * x t - k : ℕ) : ℝ) = 2 * x t - k := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [this]; field_simp; ring
      rw [e, Real.tan_eq_sin_div_cos, Real.sin_add_pi_div_two, Real.cos_add_pi_div_two,
        Real.cot_eq_cos_div_sin]
      rw [div_neg, neg_one_mul]
  -- Claim B: `s t = - g(n_t u / k)`
  have hB : ∀ t ∈ Icc 1 h, s t = -gsq ((nn t : ℕ) * (u : ℝ) / k) := by
    intro t ht
    have ht' := ht
    simp only [mem_Icc] at ht'
    have hx1 := hx_pos t ht
    have hxk := hx_lt t
    -- `2 x u ≡ t (mod k)`
    have hxmod : ((k : ℤ)) ∣ 2 * (x t : ℤ) * u - t := by
      have hdec : ((p * t : ℕ) : ℤ) = k * ((p * t / k : ℕ) : ℤ) + (x t : ℤ) := by
        exact_mod_cast (Nat.div_add_mod (p * t) k).symm
      push_cast at hdec
      have e : 2 * (x t : ℤ) * u - t = t * (2 * p * u - 1) - k * (2 * ((p : ℤ) * t / k) * u) := by
        have : (x t : ℤ) = p * t - k * ((p : ℤ) * t / k) := by linarith
        rw [this]; ring
      rw [e]
      exact dvd_sub (dvd_mul_of_dvd_right hu _) (dvd_mul_right _ _)
    simp only [s, nn, gsq]
    split_ifs with hxh hf hf
    · -- `n u ≡ -t`, so `{n u / k} = (k - t)/k ≥ 1/2`: contradiction with `hf`
      exfalso
      have hm : ((((k - 2 * x t : ℕ) : ℤ) * u) % (k : ℤ)) = k - t := by
        have hc : ((k - 2 * x t : ℕ) : ℤ) = k - 2 * x t := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [hc]
        obtain ⟨c, hc⟩ := hxmod
        have e : ((k : ℤ) - 2 * x t) * u = (k - t) + k * (u - 1 - c) := by
          linear_combination (-1 : ℤ) * hc
        rw [e, Int.add_mul_emod_self_left]
        apply Int.emod_eq_of_lt (by omega) (by omega)
      have hf' := hf
      rw [show ((k - 2 * x t : ℕ) : ℝ) * (u : ℝ) / k = ((((k - 2 * x t : ℕ) : ℤ) * u : ℤ) : ℝ) / k by
        push_cast; ring, fract_div _ k hk0, hm] at hf'
      push_cast at hf'
      rw [div_lt_iff₀ hkR] at hf'
      have : (t : ℝ) ≤ h := by exact_mod_cast ht'.2
      have hkh : (k : ℝ) = 2 * h + 1 := by exact_mod_cast hh
      linarith
    · norm_num
    · norm_num
    · -- `n u ≡ t`, so `{n u / k} = t/k < 1/2`: contradiction with `hf`
      exfalso
      have hm : ((((2 * x t - k : ℕ) : ℤ) * u) % (k : ℤ)) = t := by
        have hc : ((2 * x t - k : ℕ) : ℤ) = 2 * x t - k := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [hc]
        obtain ⟨c, hc⟩ := hxmod
        have e : (2 * (x t : ℤ) - k) * u = t + k * (c - u) := by linear_combination hc
        rw [e, Int.add_mul_emod_self_left]
        apply Int.emod_eq_of_lt (by omega) (by omega)
      rw [show ((2 * x t - k : ℕ) : ℝ) * (u : ℝ) / k = ((((2 * x t - k : ℕ) : ℤ) * u : ℤ) : ℝ) / k by
        push_cast; ring, fract_div _ k hk0, hm] at hf
      push_cast at hf
      rw [div_lt_iff₀ hkR] at hf
      have : (t : ℝ) ≤ h := by exact_mod_cast ht'.2
      have hkh : (k : ℝ) = 2 * h + 1 := by exact_mod_cast hh
      apply hf; linarith
  -- Claim C: `t ↦ n t` is a bijection `[1, h] → {odd n ∈ (0, k)}`
  have hmaps : ∀ t ∈ Icc 1 h, nn t ∈ (Ioo 0 k).filter Odd := by
    intro t ht
    have hx1 := hx_pos t ht
    have hxk := hx_lt t
    simp only [mem_filter, mem_Ioo, nn]
    split_ifs with hxh
    · refine ⟨⟨by omega, by omega⟩, ⟨h - x t, by omega⟩⟩
    · refine ⟨⟨by omega, by omega⟩, ⟨x t - h - 1, by omega⟩⟩
  have hinj : Set.InjOn nn (Icc 1 h : Set ℕ) := by
    intro t ht t' ht' heq
    simp only [coe_Icc, Set.mem_Icc] at ht ht'
    have hx1 := hx_pos t (by simp [ht.1, ht.2])
    have hx1' := hx_pos t' (by simp [ht'.1, ht'.2])
    have hxk := hx_lt t
    have hxk' := hx_lt t'
    -- either `x t = x t'` or `x t + x t' = k`
    have hcase : x t = x t' ∨ x t + x t' = k := by
      simp only [nn] at heq
      split_ifs at heq <;> omega
    have hdvd : (k : ℤ) ∣ (p : ℤ) * ((t : ℤ) - t') ∨ (k : ℤ) ∣ (p : ℤ) * ((t : ℤ) + t') := by
      have d1 : ((p * t : ℕ) : ℤ) = k * ((p * t / k : ℕ) : ℤ) + (x t : ℤ) := by
        exact_mod_cast (Nat.div_add_mod (p * t) k).symm
      have d2 : ((p * t' : ℕ) : ℤ) = k * ((p * t' / k : ℕ) : ℤ) + (x t' : ℤ) := by
        exact_mod_cast (Nat.div_add_mod (p * t') k).symm
      push_cast at d1 d2
      rcases hcase with hc | hc
      · left
        refine ⟨((p : ℤ) * t / k) - ((p : ℤ) * t' / k), ?_⟩
        have : (x t : ℤ) = x t' := by exact_mod_cast hc
        linarith
      · right
        refine ⟨((p : ℤ) * t / k) + ((p : ℤ) * t' / k) + 1, ?_⟩
        have : (x t : ℤ) + x t' = k := by exact_mod_cast hc
        linarith
    have hcopZ : IsCoprime (k : ℤ) (p : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast hcop.symm
    rcases hdvd with hd | hd
    · have := hcopZ.dvd_of_dvd_mul_left hd
      obtain ⟨c, hc⟩ := this
      have hlt : |(t : ℤ) - t'| < k := by rw [abs_lt]; constructor <;> omega
      rcases lt_trichotomy c 0 with hc0 | hc0 | hc0
      · have : (t : ℤ) - t' ≤ -k := by nlinarith
        omega
      · subst hc0; simp at hc; omega
      · have : (k : ℤ) ≤ (t : ℤ) - t' := by nlinarith
        omega
    · have := hcopZ.dvd_of_dvd_mul_left hd
      have hpos : (0 : ℤ) < (t : ℤ) + t' := by omega
      have := Int.le_of_dvd hpos this
      omega
  have hcard : ((Ioo 0 k).filter Odd).card ≤ (Icc 1 h).card := by
    have hsub : (Ioo 0 k).filter Odd ⊆ (range h).image (fun i => 2 * i + 1) := by
      intro n hn
      simp only [mem_filter, mem_Ioo] at hn
      obtain ⟨⟨_, hnk⟩, ⟨m, hm⟩⟩ := hn
      rw [mem_image]; exact ⟨m, mem_range.mpr (by omega), by omega⟩
    calc ((Ioo 0 k).filter Odd).card ≤ ((range h).image (fun i => 2 * i + 1)).card :=
          card_le_card hsub
      _ ≤ (range h).card := card_image_le
      _ = (Icc 1 h).card := by simp
  have hsurj : Set.SurjOn nn (Icc 1 h : Set ℕ) (((Ioo 0 k).filter Odd : Finset ℕ) : Set ℕ) :=
    Finset.surjOn_of_injOn_of_card_le nn hmaps hinj hcard
  -- assemble
  unfold Fsum
  rw [hhk, ← sum_neg_distrib]
  apply sum_nbij nn hmaps hinj hsurj
  intro t ht
  rw [hA t ht, hB t ht]; ring

end ThetaSum

#print axioms ThetaSum.sign_form
