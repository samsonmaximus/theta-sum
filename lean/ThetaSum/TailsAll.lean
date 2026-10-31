import ThetaSum.Generic
import ThetaSum.TailBound

/-
Assembly of the tails in §8.

For an odd modulus `k` and `u` with `k ∣ 2 p u - 1` (so `θ_k = u/k`), the tail of the sign form
(Lemma 6.1, `sign_form`) is
  `Φ_k^{>N} = ∑_{N < n < k, n odd} (1/k) cot(π n/(2k)) g(n u / k)`
(up to the overall sign, which is irrelevant for absolute values).

* `phiTail_generic`: if `‖2 m θ_k‖ ≥ η` for `1 ≤ m ≤ M`, then
  `|Φ_k^{>N}| ≤ (π/2)(3/M + 1/(η N))(log k - log N)` (Lemma 6.7(a) + `generic_bound_div`).
* `phiTail_trivial`: always `|Φ_k^{>N}| ≤ (log k)/π` (Lemma 6.7(b)).
* `tails_sum`: summing over odd `k` with `N + 1 < k < K`, the generic moduli contribute at most
  `(π/2)(3/M + 1/(η N)) (log K)(1 + log K)` and the non-generic ones at most
  `(log K / π) · 2 M I T^{-γ₀/4}` (via `nongeneric_mass_D`, i.e. Theorem D).
* `tails_sum_explicit`: with `M ≥ (log p)²`, `N ≥ T M` and `K ≤ p` the first term is at most
  `2π (1 + 1/log p)`.
-/

open Finset

namespace ThetaSum

/-- The tail `Φ_k^{>N}` of the sign form, with `θ_k = u/k`. -/
noncomputable def phiTail (k N : ℕ) (u : ℤ) : ℝ :=
  ∑ n ∈ (Ioo N k).filter Odd, (1 / k : ℝ) * Real.cot (Real.pi * n / (2 * k)) * gsq (n * ((u : ℝ) / k))

/-- The odd numbers in `(N, t]` form the progression `n₀ + 2j`, `j < J`. -/
lemma odd_Ioc_eq_image (N t : ℕ) :
    (Ioc N t).filter Odd =
      (range ((t + 2 - (2 * ((N + 1) / 2) + 1)) / 2)).image (fun j => 2 * ((N + 1) / 2) + 1 + 2 * j) := by
  ext n
  simp only [mem_filter, mem_Ioc, mem_image, mem_range, Nat.odd_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨(n - (2 * ((N + 1) / 2) + 1)) / 2, by omega, by omega⟩
  · rintro ⟨j, hj, rfl⟩
    refine ⟨⟨by omega, by omega⟩, by omega⟩

/-- **Generic tails.** -/
theorem phiTail_generic (k N M : ℕ) (u : ℤ) {η : ℝ} (hM : 1 ≤ M) (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (hN : 2 ≤ N) (hNk : N < k)
    (hθ : ∀ m ∈ Icc 1 M, η ≤ dnear (2 * m * ((u : ℝ) / k))) :
    |phiTail k N u| ≤ Real.pi / 2 * (3 / M + 1 / (η * N)) * (Real.log k - Real.log N) := by
  classical
  set θ := (u : ℝ) / k
  set a : ℕ → ℝ := fun n => if Odd n then gsq (n * θ) else 0
  have hphi : phiTail k N u =
      ∑ n ∈ Ioo N k, (1 / k : ℝ) * Real.cot (Real.pi * n / (2 * k)) * a n := by
    unfold phiTail
    rw [sum_filter]
    apply sum_congr rfl; intro n _
    simp only [a]; split_ifs <;> simp [θ]
  rw [hphi]
  apply tail_partial_summation k N (by omega) hNk a
  intro t hNt htk
  set w := (N + 1) / 2 with hw
  -- partial sums are sums along an arithmetic progression of odd numbers
  have hA : ∑ n ∈ Ioc N t, a n =
      ∑ j ∈ range ((t + 2 - (2 * ((N + 1) / 2) + 1)) / 2),
        gsq ((((2 * ((N + 1) / 2) + 1 : ℕ) : ℤ) + 2 * j) * θ) := by
    rw [← sum_filter_add_sum_filter_not (Ioc N t) Odd]
    have h0 : ∑ n ∈ (Ioc N t).filter (fun n => ¬ Odd n), a n = 0 := by
      apply sum_eq_zero; intro n hn
      simp only [mem_filter] at hn
      simp only [a, if_neg hn.2]
    rw [h0, add_zero, odd_Ioc_eq_image, sum_image (by intro x _ y _ h; simp only at h; omega)]
    apply sum_congr rfl; intro j _
    have hodd : Odd (2 * ((N + 1) / 2) + 1 + 2 * j) := ⟨(N + 1) / 2 + j, by ring⟩
    simp only [a, if_pos hodd]
    congr 1
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Int.cast_add, Int.cast_mul,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_one]
  rw [hA]
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have htR : (N : ℝ) ≤ t := by exact_mod_cast hNt
  have hJ : (((t + 2 - (2 * ((N + 1) / 2) + 1)) / 2 : ℕ) : ℝ) ≤ (t : ℝ) / 2 := by
    have : 2 * ((t + 2 - (2 * ((N + 1) / 2) + 1)) / 2) ≤ t := by omega
    have : ((2 * ((t + 2 - (2 * ((N + 1) / 2) + 1)) / 2) : ℕ) : ℝ) ≤ t := by exact_mod_cast this
    rw [Nat.cast_mul, Nat.cast_ofNat] at this; linarith
  have h := generic_bound_div M hM hη hη2 hθ (((2 * ((N + 1) / 2) + 1 : ℕ) : ℤ))
    ((t + 2 - (2 * ((N + 1) / 2) + 1)) / 2) hNR htR hJ
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hNR htR
  rw [div_le_iff₀ ht0] at h
  linarith

/-- **Trivial tail bound** (Lemma 6.7(b)). -/
theorem phiTail_trivial (k N : ℕ) (u : ℤ) (hk : 3 ≤ k) (hN : 2 ≤ N) :
    |phiTail k N u| ≤ Real.log k / Real.pi := by
  apply tail_trivial k N hk hN (fun n => gsq (n * ((u : ℝ) / k)))
  intro n; unfold gsq; split_ifs <;> norm_num

lemma sum_inv_le_log (K : ℕ) (A : Finset ℕ) (hA : ∀ k ∈ A, 1 ≤ k ∧ k < K) :
    ∑ k ∈ A, (1 / k : ℝ) ≤ 1 + Real.log K := by
  have hsub : A ⊆ Icc 1 K := by
    intro k hk; have := hA k hk; simp only [mem_Icc]; omega
  calc ∑ k ∈ A, (1 / k : ℝ) ≤ ∑ k ∈ Icc 1 K, (1 / k : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = harmonic K := by
        rw [harmonic_eq_sum_Icc]; push_cast; apply sum_congr rfl; intro k _; simp
    _ ≤ 1 + Real.log K := harmonic_le_one_add_log K

/-- **Summed tails of §8.** For `0 < γ₀ < 1` there is `L₀` such that the following holds for
every prime `p` with `log p ≥ L₀`, with `T = exp((log p)^γ₀)` and `η = 1/T`. Let `1 ≤ M ≤ N`,
`2 ≤ N`, `M < p`, `T ≥ 2`, `K ≤ T 2^I` and `p 2^I + M ≤ p²`, and let `u_k` satisfy
`k ∣ 2 p u_k - 1` for the odd `k` with `N + 1 < k < K`. Then
  `∑_{N+1 < k < K, k odd} (1/k) |Φ_k^{>N}| ≤
      (π/2)(3/M + T/N)(log K)(1 + log K) + (log K / π)·2 M I T^{-γ₀/4}`. -/
theorem tails_sum {γ₀ : ℝ} (hγ : 0 < γ₀) (hγ1 : γ₀ < 1) :
    ∃ L₀ : ℝ, ∀ p : ℕ, p.Prime → L₀ ≤ Real.log p →
      ∀ (M N K I : ℕ) (u : ℕ → ℤ), 1 ≤ M → M ≤ N → 2 ≤ N → M < p →
        2 ≤ Real.exp (Real.log p ^ γ₀) →
        (K : ℝ) ≤ Real.exp (Real.log p ^ γ₀) * 2 ^ I →
        (p : ℝ) * 2 ^ I + M ≤ (p : ℝ) ^ 2 →
        (∀ k ∈ (Ioo (N + 1) K).filter Odd, (k : ℤ) ∣ 2 * p * u k - 1) →
        ∑ k ∈ (Ioo (N + 1) K).filter Odd, (1 / k : ℝ) * |phiTail k N (u k)| ≤
          Real.pi / 2 * (3 / M + Real.exp (Real.log p ^ γ₀) / N) * (Real.log K * (1 + Real.log K)) +
            Real.log K / Real.pi *
              (2 * M * I * Real.exp (Real.log p ^ γ₀) ^ (-(γ₀ / 4))) := by
  obtain ⟨L₀, hL₀⟩ := nongeneric_mass_D hγ hγ1
  refine ⟨L₀, fun p hp hpL M N K I u hM1 hMN hN hMp hT2 hKI hpI hu => ?_⟩
  classical
  set T := Real.exp (Real.log p ^ γ₀)
  set η : ℝ := 1 / T
  have hT0 : 0 < T := Real.exp_pos _
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
    have hmass : ∑ k ∈ B, (1 / k : ℝ) ≤ 2 * M * I * T ^ (-(γ₀ / 4)) := by
      apply hL₀ p hp hpL M K I u hMp hKI hpI B
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
      _ ≤ Real.log K / Real.pi * (2 * M * I * T ^ (-(γ₀ / 4))) :=
          mul_le_mul_of_nonneg_left hmass (by positivity)

/-- **Explicit form.** Under the hypotheses of `tails_sum`, if moreover `(log p)² ≤ M`,
`T M ≤ N` and `K ≤ p`, then the generic contribution is at most `2π (1 + 1/log p)`:
  `∑_{N+1 < k < K, k odd} (1/k)|Φ_k^{>N}| ≤ 2π(1 + 1/log p) + (log p/π)·2 M I T^{-γ₀/4}`. -/
theorem tails_sum_explicit {γ₀ : ℝ} (hγ : 0 < γ₀) (hγ1 : γ₀ < 1) :
    ∃ L₀ : ℝ, ∀ p : ℕ, p.Prime → L₀ ≤ Real.log p →
      ∀ (M N K I : ℕ) (u : ℕ → ℤ), 1 ≤ M → M ≤ N → 2 ≤ N → M < p →
        2 ≤ Real.exp (Real.log p ^ γ₀) →
        (K : ℝ) ≤ Real.exp (Real.log p ^ γ₀) * 2 ^ I →
        (p : ℝ) * 2 ^ I + M ≤ (p : ℝ) ^ 2 →
        Real.log p ^ 2 ≤ M → Real.exp (Real.log p ^ γ₀) * M ≤ N → K ≤ p →
        (∀ k ∈ (Ioo (N + 1) K).filter Odd, (k : ℤ) ∣ 2 * p * u k - 1) →
        ∑ k ∈ (Ioo (N + 1) K).filter Odd, (1 / k : ℝ) * |phiTail k N (u k)| ≤
          2 * Real.pi * (1 + 1 / Real.log p) +
            Real.log p / Real.pi * (2 * M * I * Real.exp (Real.log p ^ γ₀) ^ (-(γ₀ / 4))) := by
  obtain ⟨L₀, hL₀⟩ := tails_sum hγ hγ1
  refine ⟨max L₀ 1, fun p hp hpL M N K I u hM1 hMN hN hMp hT2 hKI hpI hLM hTMN hKp hu => ?_⟩
  set T := Real.exp (Real.log p ^ γ₀)
  have hL1 : 1 ≤ Real.log p := le_trans (le_max_right _ _) hpL
  have h := hL₀ p hp (le_trans (le_max_left _ _) hpL) M N K I u hM1 hMN hN hMp hT2 hKI hpI hu
  refine h.trans ?_
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM1
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hT0 : 0 < T := Real.exp_pos _
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hK : Real.log K ≤ Real.log p := by
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]; linarith
    · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hKp)
  have hlogK : 0 ≤ Real.log K := by
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]
    · exact Real.log_nonneg (by exact_mod_cast h0)
  -- `3/M + T/N ≤ 4/M ≤ 4/(log p)²`
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
  have hsecond : Real.log K / Real.pi * (2 * M * I * T ^ (-(γ₀ / 4))) ≤
      Real.log p / Real.pi * (2 * M * I * T ^ (-(γ₀ / 4))) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact div_le_div_of_nonneg_right hK Real.pi_pos.le
  linarith

end ThetaSum

#print axioms ThetaSum.phiTail_generic
#print axioms ThetaSum.tails_sum
#print axioms ThetaSum.tails_sum_explicit
