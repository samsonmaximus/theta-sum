import ThetaSum.TailsAll
import ThetaSum.TheoremDStar

/-!
# The tails of §8 with Theorem D\* in place of Theorem D

`nongeneric_mass_Dstar`, `tails_sum_star`, `tails_sum_star_explicit`: the statements of
`nongeneric_mass_D`, `tails_sum`, `tails_sum_explicit` for any `T ≥ 2` with
`log T ≥ (log log p)^3` (and `log log p ≥ 1000`), with the non-generic mass
`exp(-log T / (4 log log p))` from `theorem_D_star`.
-/

open Finset

namespace ThetaSum

/-- **Non-generic tails via Theorem D\*.** If `log log p ≥ 1000` and `log T ≥ (log log p)^3`, then
for `S` as in `nongeneric_mass`, `∑_{k ∈ S} 1/k ≤ 2 M I exp(-log T / (4 log log p))`. -/
theorem nongeneric_mass_Dstar (p : ℕ) (hp : p.Prime) (hq : 1000 ≤ Real.log (Real.log p)) (T : ℝ)
    (hT : 0 < T) (hTq : Real.log (Real.log p) ^ 3 ≤ Real.log T) (M K I : ℕ) (u : ℕ → ℤ)
    (hMp : M < p) (hKI : (K : ℝ) ≤ T * 2 ^ I) (hpI : (p : ℝ) * 2 ^ I + M ≤ (p : ℝ) ^ 2)
    (S : Finset ℕ) (hS : S ⊆ range K)
    (hSk : ∀ k ∈ S, M < k ∧ (k : ℤ) ∣ 2 * p * u k - 1 ∧
      ∃ m ∈ Icc 1 M, dnear (2 * m * ((u k : ℝ) / k)) < 1 / T) :
    ∑ k ∈ S, (1 / k : ℝ) ≤ 2 * M * I * Real.exp (-(Real.log T / (4 * Real.log (Real.log p)))) := by
  refine (nongeneric_mass p M K I u hT hMp hKI S hS hSk).trans ?_
  set B := Real.exp (-(Real.log T / (4 * Real.log (Real.log p))))
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
    refine theorem_D_star p hq T hT hTq s (2 ^ i) (2 ^ i) (2 ^ i) hcop hR1 (by push_cast; rfl) ?_
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


/-- **Summed tails of §8 with Theorem D\*** (any `T ≥ 2` with `log T ≥ (log log p)^3`). -/
theorem tails_sum_star (p : ℕ) (hp : p.Prime) (hq : 1000 ≤ Real.log (Real.log p)) (T : ℝ)
    (hT2 : 2 ≤ T) (hTq : Real.log (Real.log p) ^ 3 ≤ Real.log T)
    (M N K I : ℕ) (u : ℕ → ℤ) (hM1 : 1 ≤ M) (hMN : M ≤ N) (hN : 2 ≤ N) (hMp : M < p)
    (hKI : (K : ℝ) ≤ T * 2 ^ I) (hpI : (p : ℝ) * 2 ^ I + M ≤ (p : ℝ) ^ 2)
    (hu : ∀ k ∈ (Ioo (N + 1) K).filter Odd, (k : ℤ) ∣ 2 * p * u k - 1) :
    ∑ k ∈ (Ioo (N + 1) K).filter Odd, (1 / k : ℝ) * |phiTail k N (u k)| ≤
      Real.pi / 2 * (3 / M + T / N) * (Real.log K * (1 + Real.log K)) +
        Real.log K / Real.pi *
          (2 * M * I * Real.exp (-(Real.log T / (4 * Real.log (Real.log p))))) := by
  classical
  set η : ℝ := 1 / T
  have hT0 : 0 < T := by linarith
  have hη : 0 < η := by positivity
  have hη2 : η ≤ 1 / 2 := by
    simp only [η]; rw [div_le_div_iff₀ hT0 (by norm_num)]; linarith
  set A := (Ioo (N + 1) K).filter Odd
  set G := A.filter (fun k => ∀ m ∈ Icc 1 M, η ≤ dnear (2 * m * ((u k : ℝ) / k)))
  set B := A.filter (fun k => ¬ ∀ m ∈ Icc 1 M, η ≤ dnear (2 * m * ((u k : ℝ) / k)))
  rw [← sum_filter_add_sum_filter_not A (fun k => ∀ m ∈ Icc 1 M, η ≤ dnear (2 * m * ((u k : ℝ) / k)))]
  have hlogK : 0 ≤ Real.log K := Real.log_natCast_nonneg K
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hD : 3 / (M : ℝ) + 1 / (η * N) = 3 / M + T / N := by
    simp only [η]; field_simp
  apply add_le_add
  · -- generic moduli
    have hterm : ∀ k ∈ G, (1 / k : ℝ) * |phiTail k N (u k)| ≤
        Real.pi / 2 * (3 / M + T / N) * Real.log K * (1 / k) := by
      intro k hk
      simp only [G, A, mem_filter, mem_Ioo] at hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have h1 := phiTail_generic k N M (u k) hM1 hη hη2 hN (by omega) hk.2
      rw [hD] at h1
      have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
      have hlogk : Real.log k ≤ Real.log K :=
        Real.log_le_log hk0 (by exact_mod_cast hk.1.1.2.le)
      have hc : 0 ≤ Real.pi / 2 * (3 / M + T / N) := by positivity
      calc (1 / k : ℝ) * |phiTail k N (u k)|
          ≤ (1 / k) * (Real.pi / 2 * (3 / M + T / N) * (Real.log k - Real.log N)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ (1 / k) * (Real.pi / 2 * (3 / M + T / N) * Real.log K) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul_of_nonneg_left _ hc; linarith
        _ = _ := by ring
    calc ∑ k ∈ G, (1 / k : ℝ) * |phiTail k N (u k)|
        ≤ ∑ k ∈ G, Real.pi / 2 * (3 / M + T / N) * Real.log K * (1 / k) := sum_le_sum hterm
      _ = Real.pi / 2 * (3 / M + T / N) * Real.log K * ∑ k ∈ G, (1 / k : ℝ) := by rw [mul_sum]
      _ ≤ Real.pi / 2 * (3 / M + T / N) * Real.log K * (1 + Real.log K) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply sum_inv_le_log K
          intro k hk; simp only [G, A, mem_filter, mem_Ioo] at hk; omega
      _ = _ := by ring
  · -- non-generic moduli
    have hterm : ∀ k ∈ B, (1 / k : ℝ) * |phiTail k N (u k)| ≤ Real.log K / Real.pi * (1 / k) := by
      intro k hk
      simp only [B, A, mem_filter, mem_Ioo] at hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have h1 := phiTail_trivial k N (u k) (by omega) hN
      have hlogk : Real.log k ≤ Real.log K :=
        Real.log_le_log hk0 (by exact_mod_cast hk.1.1.2.le)
      calc (1 / k : ℝ) * |phiTail k N (u k)| ≤ (1 / k) * (Real.log k / Real.pi) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ (1 / k) * (Real.log K / Real.pi) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact div_le_div_of_nonneg_right hlogk Real.pi_pos.le
        _ = _ := by ring
    have hmass : ∑ k ∈ B, (1 / k : ℝ) ≤ 2 * M * I * Real.exp (-(Real.log T / (4 * Real.log (Real.log p)))) := by
      apply nongeneric_mass_Dstar p hp hq T hT0 hTq M K I u hMp hKI hpI B
      · intro k hk; simp only [B, A, mem_filter, mem_Ioo, mem_range] at hk ⊢; omega
      · intro k hk
        have hk' := hk
        simp only [B, A, mem_filter, mem_Ioo] at hk'
        refine ⟨by omega, hu k (by simp only [A, mem_filter, mem_Ioo]; exact hk'.1), ?_⟩
        have := hk'.2
        push_neg at this
        obtain ⟨m, hm, hlt⟩ := this
        exact ⟨m, hm, by simpa [η] using hlt⟩
    calc ∑ k ∈ B, (1 / k : ℝ) * |phiTail k N (u k)|
        ≤ ∑ k ∈ B, Real.log K / Real.pi * (1 / k) := sum_le_sum hterm
      _ = Real.log K / Real.pi * ∑ k ∈ B, (1 / k : ℝ) := by rw [mul_sum]
      _ ≤ Real.log K / Real.pi * (2 * M * I * Real.exp (-(Real.log T / (4 * Real.log (Real.log p))))) :=
          mul_le_mul_of_nonneg_left hmass (by positivity)


/-- **Explicit form** of `tails_sum_star`: with `(log p)² ≤ M`, `T M ≤ N` and `K ≤ p`,
  `∑ (1/k)|Φ_k^{>N}| ≤ 2π(1 + 1/log p) + (log p/π)·2 M I exp(-log T/(4 log log p))`. -/
theorem tails_sum_star_explicit (p : ℕ) (hp : p.Prime) (hq : 1000 ≤ Real.log (Real.log p)) (T : ℝ)
    (hT2 : 2 ≤ T) (hTq : Real.log (Real.log p) ^ 3 ≤ Real.log T)
    (M N K I : ℕ) (u : ℕ → ℤ) (hM1 : 1 ≤ M) (hMN : M ≤ N) (hN : 2 ≤ N) (hMp : M < p)
    (hKI : (K : ℝ) ≤ T * 2 ^ I) (hpI : (p : ℝ) * 2 ^ I + M ≤ (p : ℝ) ^ 2)
    (hLM : Real.log p ^ 2 ≤ M) (hTMN : T * M ≤ N) (hKp : K ≤ p)
    (hu : ∀ k ∈ (Ioo (N + 1) K).filter Odd, (k : ℤ) ∣ 2 * p * u k - 1) :
    ∑ k ∈ (Ioo (N + 1) K).filter Odd, (1 / k : ℝ) * |phiTail k N (u k)| ≤
      2 * Real.pi * (1 + 1 / Real.log p) +
        Real.log p / Real.pi *
          (2 * M * I * Real.exp (-(Real.log T / (4 * Real.log (Real.log p))))) := by
  have h := tails_sum_star p hp hq T hT2 hTq M N K I u hM1 hMN hN hMp hKI hpI hu
  refine h.trans ?_
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hL1 : 1 ≤ Real.log p := by
    by_contra hlt
    push_neg at hlt
    have h0 : Real.log (Real.log p) ≤ 0 :=
      Real.log_nonpos (Real.log_natCast_nonneg p) hlt.le
    linarith
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM1
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hK : Real.log K ≤ Real.log p := by
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]; linarith
    · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hKp)
  have hlogK : 0 ≤ Real.log K := Real.log_natCast_nonneg K
  have hTN : T / N ≤ 1 / M := by
    rw [div_le_div_iff₀ hNR hMR]; linarith
  have hD : 3 / (M : ℝ) + T / N ≤ 4 / Real.log p ^ 2 := by
    have : 4 / (M : ℝ) ≤ 4 / Real.log p ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hLM
    have e : 3 / (M : ℝ) + 1 / M = 4 / M := by ring
    linarith
  have hfirst : Real.pi / 2 * (3 / M + T / N) * (Real.log K * (1 + Real.log K)) ≤
      2 * Real.pi * (1 + 1 / Real.log p) := by
    have hL0 : 0 < Real.log p := by linarith
    have hprod : Real.log K * (1 + Real.log K) ≤ Real.log p * (1 + Real.log p) :=
      mul_le_mul hK (by linarith) (by positivity) (by positivity)
    calc Real.pi / 2 * (3 / M + T / N) * (Real.log K * (1 + Real.log K))
        ≤ Real.pi / 2 * (4 / Real.log p ^ 2) * (Real.log p * (1 + Real.log p)) := by
          apply mul_le_mul _ hprod (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hD (by positivity)
      _ = 2 * Real.pi * (1 + 1 / Real.log p) := by field_simp; ring
  have hsecond : Real.log K / Real.pi *
        (2 * M * I * Real.exp (-(Real.log T / (4 * Real.log (Real.log p))))) ≤
      Real.log p / Real.pi * (2 * M * I * Real.exp (-(Real.log T / (4 * Real.log (Real.log p))))) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact div_le_div_of_nonneg_right hK Real.pi_pos.le
  linarith

end ThetaSum

#print axioms ThetaSum.tails_sum_star_explicit
