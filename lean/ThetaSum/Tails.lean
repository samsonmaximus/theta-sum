import ThetaSum.Asymptotics

/-
The non-generic tails of §8 of the paper.

For a prime `p` and an odd modulus `k < p` let `u_k` be an integer with `2 p u_k ≡ 1 (mod k)` and
`θ_k = u_k / k`.  A modulus `k > M` is *non-generic* if `‖2 m θ_k‖ < 1/T` for some `1 ≤ m ≤ M`.

* `witness` (Lemma 6.9): such a `k` divides `p r - m` for some integer `r` with `0 < |r| < k/T`.
* `nongeneric_mass`: the `1/k`-mass of the non-generic moduli below `K` is at most
  `∑_{m ≤ M} ∑_{i < I} (Δ(A⁺_{m,2^i}; T 2^i) + Δ(A⁻_{m,2^i}; T 2^i))`, where
  `A^±_{m,R} = {p t ∓ m : R ≤ t < 2R}` and `K ≤ T 2^I`.
* `nongeneric_mass_D`: combined with Theorem D, this mass is at most `2 M I T^{-γ₀/4}` for
  `T = exp((log p)^γ₀)` and `log p` large.
-/

open Finset

namespace ThetaSum

/-- Distance to the nearest integer, `‖x‖`. -/
noncomputable def dnear (x : ℝ) : ℝ := |x - round x|

/-- **Lemma 6.9** (witnesses). If `k ∣ 2 p u - 1`, `1 ≤ m < k` and `‖2 m u / k‖ < η`, then there
is an integer `r ≠ 0` with `|r| < η k` and `k ∣ p r - m`. -/
theorem witness (p k m : ℕ) (u : ℤ) {η : ℝ} (hk : 0 < k) (hm1 : 1 ≤ m) (hmk : m < k)
    (hu : (k : ℤ) ∣ 2 * p * u - 1) (hη : dnear (2 * m * ((u : ℝ) / k)) < η) :
    ∃ r : ℤ, r ≠ 0 ∧ (|(r : ℝ)|) < η * k ∧ (k : ℤ) ∣ p * r - m := by
  set b := round (2 * m * ((u : ℝ) / k))
  have hdiv : (k : ℤ) ∣ p * (2 * m * u - b * k) - m := by
    have e : (p : ℤ) * (2 * m * u - b * k) - m = m * (2 * p * u - 1) - k * (p * b) := by ring
    rw [e]
    exact dvd_sub (dvd_mul_of_dvd_right hu _) (dvd_mul_right _ _)
  refine ⟨2 * m * u - b * k, ?_, ?_, hdiv⟩
  · intro h0
    rw [h0, mul_zero, zero_sub, dvd_neg] at hdiv
    have := Int.le_of_dvd (by exact_mod_cast hm1) hdiv
    have : k ≤ m := by exact_mod_cast this
    omega
  · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have e : (((2 * m * u - b * k : ℤ)) : ℝ) = k * (2 * m * ((u : ℝ) / k) - b) := by
      push_cast; field_simp
    rw [e, abs_mul, abs_of_pos hk']
    unfold dnear at hη
    calc (k : ℝ) * |2 * m * ((u : ℝ) / k) - b| < k * η := mul_lt_mul_of_pos_left hη hk'
      _ = η * k := by ring

/-- `1/k` if `k ∣ n` and `k > Y`, else `0`. -/
noncomputable def gk (k : ℕ) (n : ℤ) (Y : ℝ) : ℝ :=
  open Classical in if k ∣ n.natAbs ∧ Y < (k : ℝ) then 1 / k else 0

lemma gk_nonneg (k : ℕ) (n : ℤ) (Y : ℝ) : 0 ≤ gk k n Y := by
  unfold gk; split_ifs <;> positivity

open Classical in
lemma sum_gk_le (K : ℕ) (n : ℤ) (hn : n ≠ 0) (Y : ℝ) :
    ∑ k ∈ range K, gk k n Y ≤
      ∑ d ∈ n.natAbs.divisors.filter (fun d : ℕ => Y < (d : ℝ)), (1 / d : ℝ) := by
  unfold gk
  rw [← sum_filter]
  apply sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [mem_filter, mem_range, Nat.mem_divisors] at hk ⊢
    exact ⟨⟨hk.2.1, Int.natAbs_ne_zero.mpr hn⟩, hk.2.2⟩
  · intro _ _ _; positivity

/-- The majorant of `1/k` used for the double counting. -/
noncomputable def Fk (p M I : ℕ) (T : ℝ) (k : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 M, ∑ i ∈ range I, ∑ t ∈ Ico ((2 : ℤ) ^ i) (2 ^ (i + 1)),
    (gk k (-(m : ℤ) + p * t) (T * 2 ^ i) + gk k ((m : ℤ) + p * t) (T * 2 ^ i))

lemma Fk_nonneg (p M I : ℕ) (T : ℝ) (k : ℕ) : 0 ≤ Fk p M I T k := by
  unfold Fk
  apply sum_nonneg; intro m _; apply sum_nonneg; intro i _; apply sum_nonneg; intro t _
  exact add_nonneg (gk_nonneg _ _ _) (gk_nonneg _ _ _)

/-- **Non-generic tail mass.** Let `p` be a natural number, `M < p`, `T > 0`, and `K ≤ T 2^I`.
Let `S ⊆ [0, K)` be a set of moduli `k > M` such that `k ∣ 2 p u_k - 1` and `‖2 m u_k / k‖ < 1/T`
for some `1 ≤ m ≤ M`. Then
  `∑_{k ∈ S} 1/k ≤ ∑_{m=1}^{M} ∑_{i<I} (Δ(A⁺_{m,2^i}; T 2^i) + Δ(A⁻_{m,2^i}; T 2^i))`
with `A^±_{m,R} = {p t ∓ m : R ≤ t < 2R}`. -/
theorem nongeneric_mass (p M K I : ℕ) (u : ℕ → ℤ) {T : ℝ} (hT : 0 < T) (hMp : M < p)
    (hKI : (K : ℝ) ≤ T * 2 ^ I) (S : Finset ℕ) (hS : S ⊆ range K)
    (hSk : ∀ k ∈ S, M < k ∧ (k : ℤ) ∣ 2 * p * u k - 1 ∧
      ∃ m ∈ Icc 1 M, dnear (2 * m * ((u k : ℝ) / k)) < 1 / T) :
    ∑ k ∈ S, (1 / k : ℝ) ≤
      ∑ m ∈ Icc 1 M, ∑ i ∈ range I,
        (Delta p (-(m : ℤ)) (Ico ((2 : ℤ) ^ i) (2 ^ (i + 1))) (T * 2 ^ i) +
          Delta p (m : ℤ) (Ico ((2 : ℤ) ^ i) (2 ^ (i + 1))) (T * 2 ^ i)) := by
  -- Step 1: `1/k ≤ F(k)` for `k ∈ S`.
  have step1 : ∀ k ∈ S, (1 / k : ℝ) ≤ Fk p M I T k := by
    intro k hk
    obtain ⟨hMk, hu, m, hm, hθ⟩ := hSk k hk
    have hkK : k < K := mem_range.mp (hS hk)
    simp only [mem_Icc] at hm
    have hk0 : 0 < k := by omega
    obtain ⟨r, hr0, hrk, hdiv⟩ := witness p k m (u k) hk0 hm.1 (by omega) hu hθ
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
    set a := r.natAbs
    have ha0 : 0 < a := Int.natAbs_pos.mpr hr0
    have har : ((a : ℕ) : ℝ) = |(r : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    set i := Nat.log 2 a
    have hi1 : 2 ^ i ≤ a := Nat.pow_log_le_self 2 ha0.ne'
    have hi2 : a < 2 ^ (i + 1) := Nat.lt_pow_succ_log_self (by norm_num) a
    have hTa : T * a < k := by
      rw [har]
      have := hrk
      rw [one_div, inv_mul_eq_div, lt_div_iff₀ hT] at this
      linarith
    have hiI : i < I := by
      have h1 : T * (2 : ℝ) ^ i < T * 2 ^ I := by
        have : (2 : ℝ) ^ i ≤ a := by exact_mod_cast hi1
        have hkK' : (k : ℝ) < K := by exact_mod_cast hkK
        nlinarith
      have h2 : (2 : ℝ) ^ i < 2 ^ I := lt_of_mul_lt_mul_left h1 hT.le
      exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h2
    have hY : T * 2 ^ i < (k : ℝ) := by
      have : (2 : ℝ) ^ i ≤ a := by exact_mod_cast hi1
      nlinarith
    have hmI : m ∈ Icc 1 M := mem_Icc.mpr hm
    have hiR : i ∈ range I := mem_range.mpr hiI
    have hat : (a : ℤ) ∈ Ico ((2 : ℤ) ^ i) (2 ^ (i + 1)) := by
      simp only [mem_Ico]; constructor <;> exact_mod_cast (by omega : _)
    -- the summand at `(m, i, t = |r|)` is `1/k`
    have hterm : (1 / k : ℝ) ≤
        gk k (-(m : ℤ) + p * (a : ℤ)) (T * 2 ^ i) + gk k ((m : ℤ) + p * (a : ℤ)) (T * 2 ^ i) := by
      rcases lt_or_gt_of_ne hr0 with hneg | hpos
      · have hra : (a : ℤ) = -r := by simp only [a]; omega
        have hd : k ∣ ((m : ℤ) + p * (a : ℤ)).natAbs := by
          rw [← Int.natCast_dvd]
          have e : (m : ℤ) + p * (a : ℤ) = -(p * r - m) := by rw [hra]; ring
          rw [e, dvd_neg]; exact hdiv
        have : gk k ((m : ℤ) + p * (a : ℤ)) (T * 2 ^ i) = 1 / k := by
          unfold gk; rw [if_pos ⟨hd, hY⟩]
        rw [this]; linarith [gk_nonneg k (-(m : ℤ) + p * (a : ℤ)) (T * 2 ^ i)]
      · have hra : (a : ℤ) = r := by simp only [a]; omega
        have hd : k ∣ (-(m : ℤ) + p * (a : ℤ)).natAbs := by
          rw [← Int.natCast_dvd]
          have e : -(m : ℤ) + p * (a : ℤ) = p * r - m := by rw [hra]; ring
          rw [e]; exact hdiv
        have : gk k (-(m : ℤ) + p * (a : ℤ)) (T * 2 ^ i) = 1 / k := by
          unfold gk; rw [if_pos ⟨hd, hY⟩]
        rw [this]; linarith [gk_nonneg k ((m : ℤ) + p * (a : ℤ)) (T * 2 ^ i)]
    unfold Fk
    refine hterm.trans ?_
    refine le_trans ?_ (single_le_sum (f := fun m : ℕ => ∑ i ∈ range I, ∑ t ∈ Ico ((2 : ℤ) ^ i) (2 ^ (i + 1)),
      (gk k (-(m : ℤ) + p * t) (T * 2 ^ i) + gk k ((m : ℤ) + p * t) (T * 2 ^ i)))
      (fun m _ => sum_nonneg fun i _ => sum_nonneg fun t _ =>
        add_nonneg (gk_nonneg _ _ _) (gk_nonneg _ _ _)) hmI)
    refine le_trans ?_ (single_le_sum (f := fun i : ℕ => ∑ t ∈ Ico ((2 : ℤ) ^ i) (2 ^ (i + 1)),
      (gk k (-(m : ℤ) + p * t) (T * 2 ^ i) + gk k ((m : ℤ) + p * t) (T * 2 ^ i)))
      (fun i _ => sum_nonneg fun t _ => add_nonneg (gk_nonneg _ _ _) (gk_nonneg _ _ _)) hiR)
    exact single_le_sum (f := fun t : ℤ =>
      (gk k (-(m : ℤ) + p * t) (T * 2 ^ i) + gk k ((m : ℤ) + p * t) (T * 2 ^ i)))
      (fun t _ => add_nonneg (gk_nonneg _ _ _) (gk_nonneg _ _ _)) hat
  -- Step 2: sum over `k`, swap, and compare with the divisor sums.
  calc ∑ k ∈ S, (1 / k : ℝ) ≤ ∑ k ∈ S, Fk p M I T k := sum_le_sum step1
    _ ≤ ∑ k ∈ range K, Fk p M I T k :=
        sum_le_sum_of_subset_of_nonneg hS (fun k _ _ => Fk_nonneg p M I T k)
    _ = ∑ m ∈ Icc 1 M, ∑ i ∈ range I, ∑ t ∈ Ico ((2 : ℤ) ^ i) (2 ^ (i + 1)),
          ∑ k ∈ range K,
            (gk k (-(m : ℤ) + p * t) (T * 2 ^ i) + gk k ((m : ℤ) + p * t) (T * 2 ^ i)) := by
        unfold Fk
        rw [sum_comm]
        apply sum_congr rfl; intro m _
        rw [sum_comm]
        apply sum_congr rfl; intro i _
        rw [sum_comm]
    _ ≤ _ := by
        apply sum_le_sum; intro m hm; apply sum_le_sum; intro i _
        simp only [mem_Icc] at hm
        unfold Delta
        rw [← sum_add_distrib]
        apply sum_le_sum; intro t ht
        simp only [mem_Ico] at ht
        have ht1 : (1 : ℤ) ≤ t := le_trans (one_le_pow₀ (by norm_num)) ht.1
        rw [sum_add_distrib]
        apply add_le_add
        · apply sum_gk_le
          have : (m : ℤ) < p := by exact_mod_cast (by omega : m < p)
          nlinarith
        · apply sum_gk_le
          have : (0 : ℤ) < p := by exact_mod_cast (by omega : 0 < p)
          nlinarith

/-- **Non-generic tails via Theorem D.** For `0 < γ₀ < 1` there is `L₀` such that for every
prime `p` with `log p ≥ L₀`, putting `T = exp((log p)^γ₀)`: if `M < p`, `K ≤ T 2^I`,
`p 2^I + M ≤ p²`, and `S ⊆ [0, K)` is a set of non-generic moduli as in `nongeneric_mass`, then
  `∑_{k ∈ S} 1/k ≤ 2 M I T^{-γ₀/4}`. -/
theorem nongeneric_mass_D {γ₀ : ℝ} (hγ : 0 < γ₀) (hγ1 : γ₀ < 1) :
    ∃ L₀ : ℝ, ∀ p : ℕ, p.Prime → L₀ ≤ Real.log p →
      ∀ (M K I : ℕ) (u : ℕ → ℤ), M < p →
        (K : ℝ) ≤ Real.exp (Real.log p ^ γ₀) * 2 ^ I →
        (p : ℝ) * 2 ^ I + M ≤ (p : ℝ) ^ 2 →
        ∀ S : Finset ℕ, S ⊆ range K →
          (∀ k ∈ S, M < k ∧ (k : ℤ) ∣ 2 * p * u k - 1 ∧
            ∃ m ∈ Icc 1 M, dnear (2 * m * ((u k : ℝ) / k)) < 1 / Real.exp (Real.log p ^ γ₀)) →
          ∑ k ∈ S, (1 / k : ℝ) ≤
            2 * M * I * Real.exp (Real.log p ^ γ₀) ^ (-(γ₀ / 4)) := by
  obtain ⟨L₀, hL₀⟩ := theorem_D hγ hγ1
  refine ⟨L₀, fun p hp hpL M K I u hMp hKI hpI S hS hSk => ?_⟩
  set T := Real.exp (Real.log p ^ γ₀)
  have hT : 0 < T := Real.exp_pos _
  refine (nongeneric_mass p M K I u hT hMp hKI S hS hSk).trans ?_
  set B := T ^ (-(γ₀ / 4))
  have hD : ∀ m ∈ Icc 1 M, ∀ i ∈ range I, ∀ s : ℤ, (s = -(m : ℤ) ∨ s = (m : ℤ)) →
      Delta p s (Ico ((2 : ℤ) ^ i) (2 ^ (i + 1))) (T * 2 ^ i) ≤ B := by
    intro m hm i hi s hs
    simp only [mem_Icc] at hm
    simp only [mem_range] at hi
    have hmp : m < p := by omega
    have hcop : Int.gcd s p = 1 := by
      have hc : Nat.Coprime m p := by
        rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
        intro h; have := Nat.le_of_dvd (by omega) h; omega
      rcases hs with rfl | rfl
      · rw [Int.neg_gcd]; exact_mod_cast hc
      · exact_mod_cast hc
    have hIco : Ico ((2 : ℤ) ^ i) (2 ^ (i + 1)) = Ico ((2 : ℤ) ^ i) (2 ^ i + ((2 ^ i : ℕ) : ℤ)) := by
      congr 1; push_cast; ring
    rw [hIco]
    have hR1 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
    have hpos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hpI' : (p : ℝ) * 2 ^ (i + 1) ≤ p * 2 ^ I := by
      apply mul_le_mul_of_nonneg_left _ hpos.le
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    refine hL₀ p hpL s (2 ^ i) (2 ^ i) (2 ^ i) hcop hR1 (by push_cast; rfl) ?_
    intro t ht
    simp only [mem_Ico] at ht
    have ht1 : (1 : ℤ) ≤ t := le_trans (one_le_pow₀ (by norm_num)) ht.1
    have ht2 : t < 2 ^ (i + 1) := by push_cast at ht; rw [pow_succ]; linarith [ht.2]
    have hmZ : (m : ℤ) < p := by exact_mod_cast hmp
    have hpos' : (0 : ℤ) < (p : ℤ) * t - m := by nlinarith
    have hbound : ((p : ℤ) * t + m : ℝ) ≤ (p : ℝ) ^ 2 := by
      have htR : (t : ℝ) ≤ 2 ^ (i + 1) := by
        have : t ≤ 2 ^ (i + 1) := ht2.le
        exact_mod_cast this
      have hM' : ((m : ℤ) : ℝ) ≤ M := by push_cast; exact_mod_cast hm.2
      have : (p : ℝ) * t ≤ p * 2 ^ (i + 1) := mul_le_mul_of_nonneg_left htR hpos.le
      push_cast at hM' ⊢
      linarith
    rcases hs with rfl | rfl
    · refine ⟨by omega, ?_⟩
      have e : ((-(m : ℤ) + p * t).natAbs : ℝ) = ((p : ℤ) * t - m : ℤ) := by
        rw [Nat.cast_natAbs]
        have : -(m : ℤ) + p * t = (p : ℤ) * t - m := by ring
        rw [this, abs_of_pos hpos']
      rw [e]; push_cast at hbound ⊢
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    · refine ⟨by omega, ?_⟩
      have hpos'' : (0 : ℤ) < (m : ℤ) + p * t := by omega
      have e : (((m : ℤ) + p * t).natAbs : ℝ) = ((p : ℤ) * t + m : ℤ) := by
        rw [Nat.cast_natAbs, abs_of_pos hpos'']; ring_nf
      rw [e]; push_cast at hbound ⊢; linarith
  calc ∑ m ∈ Icc 1 M, ∑ i ∈ range I,
        (Delta p (-(m : ℤ)) (Ico ((2 : ℤ) ^ i) (2 ^ (i + 1))) (T * 2 ^ i) +
          Delta p (m : ℤ) (Ico ((2 : ℤ) ^ i) (2 ^ (i + 1))) (T * 2 ^ i))
      ≤ ∑ m ∈ Icc 1 M, ∑ i ∈ range I, (B + B) := by
        apply sum_le_sum; intro m hm; apply sum_le_sum; intro i hi
        exact add_le_add (hD m hm i hi _ (Or.inl rfl)) (hD m hm i hi _ (Or.inr rfl))
    _ = 2 * M * I * B := by
        simp only [sum_const, card_range, Nat.card_Icc, nsmul_eq_mul]
        push_cast; ring

end ThetaSum

#print axioms ThetaSum.witness
#print axioms ThetaSum.nongeneric_mass
#print axioms ThetaSum.nongeneric_mass_D
