import ThetaSum.HeadsBG
import ThetaSum.TailsAll

/-
Decomposition of `R_{K_W}(p) = ∑_{3 ≤ k < K_W, k odd} F_k(p)/k²` into heads and tails
(by Lemma 6.1, `sign_form`), the trivial bound (6.2) for the heads, the identification of the
heads with `headTerm` (via `bridge`) for `k > N`, and the dyadic splitting of a range of `k`.
-/

open Finset

namespace ThetaSum

/-- The heads of `Φ_k`: `∑_{n ≤ N, n odd, n < k} (1/k) cot(π n/(2k)) g(n u/k)`. -/
noncomputable def headTh (N k : ℕ) (u : ℤ) : ℝ :=
  ∑ n ∈ ((Ioo 0 k).filter Odd).filter (· ≤ N),
    (1 / k : ℝ) * Real.cot (Real.pi * n / (2 * k)) * gsq (n * ((u : ℝ) / k))

lemma Fsum_split (p k N : ℕ) (hp : p.Prime) (hk : 3 ≤ k) (hodd : Odd k) (hkp : k < p) :
    Fsum k p / (k : ℝ) ^ 2 = -((1 / k : ℝ) * headTh N k (uInv p k) +
      (1 / k : ℝ) * phiTail k N (uInv p k)) := by
  have hcop : Nat.Coprime p k := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]; intro h; have := Nat.le_of_dvd (by omega) h; omega
  have hcop2 : Nat.Coprime (2 * p) k := by
    exact Nat.coprime_mul_iff_left.mpr ⟨Nat.coprime_two_left.mpr hodd, hcop⟩
  have hu := uInv_spec p k (by omega) hcop2
  rw [sign_form k p (uInv p k) hk hodd hcop hu]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  set u := uInv p k
  have hsplit := sum_filter_add_sum_filter_not ((Ioo 0 k).filter Odd) (· ≤ N)
    (fun n => Real.cot (Real.pi * n / (2 * k)) * gsq (n * (u : ℝ) / k))
  have htail : ((Ioo 0 k).filter Odd).filter (fun n => ¬ n ≤ N) = (Ioo N k).filter Odd := by
    ext n; simp only [mem_filter, mem_Ioo, not_le]; constructor
    · rintro ⟨⟨⟨_, h1⟩, h2⟩, h3⟩; exact ⟨⟨h3, h1⟩, h2⟩
    · rintro ⟨⟨h3, h1⟩, h2⟩; exact ⟨⟨⟨by omega, h1⟩, h2⟩, h3⟩
  rw [htail] at hsplit
  have e1 : ∀ S : Finset ℕ, (1 / k : ℝ) * ∑ n ∈ S, (1 / k : ℝ) * Real.cot (Real.pi * n / (2 * k)) *
      gsq (n * ((u : ℝ) / k)) = (∑ n ∈ S, Real.cot (Real.pi * n / (2 * k)) * gsq (n * (u : ℝ) / k)) / (k : ℝ) ^ 2 := by
    intro S
    rw [mul_sum, sum_div]; apply sum_congr rfl; intro n _
    rw [mul_div_assoc]; field_simp
  unfold headTh phiTail
  rw [e1, e1, ← add_div, hsplit, neg_div]

/-- The trivial bound (6.2) for the heads: `|headTh| ≤ (2/π)(2 + log N)` for `N ≥ 1`. -/
lemma headTh_trivial (N k : ℕ) (u : ℤ) (hN : 1 ≤ N) :
    |headTh N k u| ≤ 2 / Real.pi * (2 + Real.log N) := by
  have hpi := Real.pi_pos
  unfold headTh
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ n ∈ ((Ioo 0 k).filter Odd).filter (· ≤ N),
      |(1 / k : ℝ) * Real.cot (Real.pi * n / (2 * k)) * gsq (n * ((u : ℝ) / k))| ≤ 2 / Real.pi * (1 / n) := by
    intro n hn
    simp only [mem_filter, mem_Ioo] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1.1.1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hnk : (n : ℝ) < k := by exact_mod_cast hn.1.1.2
    have hx0 : 0 < Real.pi * n / (2 * k) := by positivity
    have hx2 : Real.pi * n / (2 * k) < Real.pi / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have hc0 := cot_nonneg hx0 hx2
    have hc1 := cot_le_inv hx0 hx2
    have hg : |gsq (n * ((u : ℝ) / k))| ≤ 1 := by unfold gsq; split_ifs <;> norm_num
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / k), abs_of_nonneg hc0]
    calc 1 / (k : ℝ) * Real.cot (Real.pi * n / (2 * k)) * |gsq (n * ((u : ℝ) / k))|
        ≤ 1 / k * (1 / (Real.pi * n / (2 * k))) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hc1 (by positivity)) hg (abs_nonneg _) (by positivity)
      _ = 2 / Real.pi * (1 / n) := by field_simp
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  -- `∑_{n ≤ N odd} 1/n ≤ 1 + (1/2) log N`
  have hsub : ((Ioo 0 k).filter Odd).filter (· ≤ N) ⊆ insert 1 (((Ioo 0 k).filter Odd).filter (fun n => 3 ≤ n ∧ n ≤ N)) := by
    intro n hn
    simp only [mem_filter, mem_Ioo, mem_insert] at hn ⊢
    obtain ⟨⟨⟨h0, hk⟩, ⟨m, hm⟩⟩, hN'⟩ := hn
    by_cases h1 : n = 1
    · left; exact h1
    · right; exact ⟨⟨⟨h0, hk⟩, ⟨m, hm⟩⟩, by omega, hN'⟩
  calc ∑ n ∈ ((Ioo 0 k).filter Odd).filter (· ≤ N), (1 / n : ℝ)
      ≤ ∑ n ∈ insert 1 (((Ioo 0 k).filter Odd).filter (fun n => 3 ≤ n ∧ n ≤ N)), (1 / n : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = 1 / (1 : ℕ) + ∑ n ∈ ((Ioo 0 k).filter Odd).filter (fun n => 3 ≤ n ∧ n ≤ N), (1 / n : ℝ) := by
        rw [sum_insert]; simp only [mem_filter]; omega
    _ ≤ 1 + Real.log (N + 1) / 2 := by
        have := odd_sum_le (N + 1) (by omega) (((Ioo 0 k).filter Odd).filter (fun n => 3 ≤ n ∧ n ≤ N))
          (by intro n hn; simp only [mem_filter, mem_Ioo] at hn; exact ⟨hn.2.1, by omega, hn.1.2⟩)
        push_cast at this
        simp only [Nat.cast_one, div_one]; linarith
    _ ≤ 2 + Real.log N := by
        have : Real.log ((N : ℝ) + 1) ≤ Real.log N + 1 := by
          have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
          have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
          have : Real.log ((N : ℝ) + 1) ≤ Real.log (2 * N) :=
            Real.log_le_log (by positivity) (by linarith)
          rw [Real.log_mul (by norm_num) hN0.ne'] at this
          have := Real.log_two_lt_d9; linarith
        have : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
        linarith

/-- For `N < k < p`, the heads in `θ`-form equal the heads in Kloosterman form. -/
lemma headTh_eq_headTerm (p N k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 3 ≤ k) (hodd : Odd k)
    (hkp : k < p) (hNk : N < k) :
    (1 / k : ℝ) * headTh N k (uInv p k) = headTerm p N k := by
  have hcop : Nat.Coprime p k := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]; intro h; have := Nat.le_of_dvd (by omega) h; omega
  have hcop2 : Nat.Coprime (2 * p) k :=
    Nat.coprime_mul_iff_left.mpr ⟨Nat.coprime_two_left.mpr hodd, hcop⟩
  have hu := uInv_spec p k (by omega) hcop2
  have h2k : ¬ p ∣ 2 * k := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
    · have := Nat.le_of_dvd (by norm_num) h1; have := hp.two_le; omega
    · have := Nat.le_of_dvd (by omega) h1; omega
  have hw := wInv_spec p k hp h2k
  have hset : ((Ioo 0 k).filter Odd).filter (· ≤ N) = (Icc 1 N).filter Odd := by
    ext n; simp only [mem_filter, mem_Ioo, mem_Icc]; constructor
    · rintro ⟨⟨⟨h0, _⟩, ho⟩, hn⟩; exact ⟨⟨h0, hn⟩, ho⟩
    · rintro ⟨⟨h0, hn⟩, ho⟩; exact ⟨⟨⟨h0, by omega⟩, ho⟩, hn⟩
  unfold headTh headTerm
  rw [hset, mul_sum]
  apply sum_congr rfl; intro n hn
  simp only [mem_filter, mem_Icc] at hn
  rw [bridge p k n (uInv p k) (wInv p k) hp hp2 (by omega) hkp hu hw hn.2 (by omega)]
  unfold wt; ring

/-- Dyadic splitting: if `1 ≤ A ≤ B ≤ 2^J A`, then
`∑_{k ∈ [A,B)} f k = ∑_{j < J} ∑_{k ∈ [min(2^j A, B), min(2^{j+1} A, B))} f k`. -/
lemma dyadic_split (f : ℕ → ℝ) (A B J : ℕ) (hAB : A ≤ B) (hJ : B ≤ 2 ^ J * A) :
    ∑ k ∈ Ico A B, f k =
      ∑ j ∈ range J, ∑ k ∈ Ico (min (2 ^ j * A) B) (min (2 ^ (j + 1) * A) B), f k := by
  have key : ∀ J' : ℕ, ∑ k ∈ Ico A (min (2 ^ J' * A) B), f k =
      ∑ j ∈ range J', ∑ k ∈ Ico (min (2 ^ j * A) B) (min (2 ^ (j + 1) * A) B), f k := by
    intro J'
    induction J' with
    | zero => simp
    | succ J' ih =>
      rw [sum_range_succ, ← ih]
      have h1 : A ≤ min (2 ^ J' * A) B := le_min (Nat.le_mul_of_pos_left A (by positivity)) hAB
      have h2 : min (2 ^ J' * A) B ≤ min (2 ^ (J' + 1) * A) B := by
        apply min_le_min_right
        exact Nat.mul_le_mul_right A (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [sum_Ico_consecutive f h1 h2]
  rw [← key J, min_eq_right hJ]

end ThetaSum
