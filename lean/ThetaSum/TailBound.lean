import Mathlib

/-
**Lemma 6.7(b)** of the paper: for odd `k ≥ 3`, `N ≥ 2` and any signs `s_n` with `|s_n| ≤ 1`,
  `|∑_{N < n < k, n odd} (1/k) cot(π n / (2k)) s_n| ≤ (1/π) log k`.
In the paper `s_n = σ(n k̄) = ±1`, and the sum is the tail `Φ_k^{>N}` of (6.1).
-/

open Finset

namespace ThetaSum

/-- `cot x ≤ 1/x` for `0 < x < π/2`. -/
lemma cot_le_inv {x : ℝ} (hx : 0 < x) (hx2 : x < Real.pi / 2) : Real.cot x ≤ 1 / x := by
  have hcos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith, hx2⟩
  have hsin : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx (by linarith [Real.pi_pos])
  have ht : x < Real.tan x := Real.lt_tan hx hx2
  rw [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos] at *
  rw [lt_div_iff₀ hcos] at ht
  rw [div_le_div_iff₀ hsin hx]; linarith

lemma cot_nonneg {x : ℝ} (hx : 0 < x) (hx2 : x < Real.pi / 2) : 0 ≤ Real.cot x := by
  have hcos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith, hx2⟩
  have hsin : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx (by linarith [Real.pi_pos])
  rw [Real.cot_eq_cos_div_sin]; positivity

/-- `∑_{i < j} 1/(2i+3) ≤ (1/2) log (2j+1)`. -/
lemma odd_harmonic (j : ℕ) : ∑ i ∈ range j, (1 / (2 * i + 3 : ℝ)) ≤ Real.log (2 * j + 1) / 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ]
    have h1 : (0 : ℝ) < 2 * j + 1 := by positivity
    have h2 : (0 : ℝ) < 2 * j + 3 := by positivity
    have key : 1 / (2 * (j : ℝ) + 3) ≤ (Real.log (2 * j + 3) - Real.log (2 * j + 1)) / 2 := by
      rw [← Real.log_div h2.ne' h1.ne']
      have hx : (2 * (j : ℝ) + 1) / (2 * j + 3) = 1 - 2 / (2 * j + 3) := by field_simp; ring
      have hl := Real.log_le_sub_one_of_pos (show 0 < (2 * (j : ℝ) + 1) / (2 * j + 3) by positivity)
      have hneg : Real.log ((2 * j + 3) / (2 * j + 1)) = -Real.log ((2 * (j : ℝ) + 1) / (2 * j + 3)) := by
        rw [← Real.log_inv, inv_div]
      rw [hneg, hx] at *
      rw [hx] at hl
      have : 1 / (2 * (j : ℝ) + 3) = (2 / (2 * j + 3)) / 2 := by ring
      rw [this]; linarith
    push_cast
    have e : (2 * ((j : ℝ) + 1) + 1) = 2 * j + 3 := by ring
    rw [e]; linarith

/-- `i ↦ 2i + 3`. -/
def oddMap (i : ℕ) : ℕ := 2 * i + 3

/-- Odd harmonic bound: `∑_{3 ≤ n < k, n odd} 1/n ≤ (1/2) log k` for `k ≥ 2`. -/
lemma odd_sum_le (k : ℕ) (hk : 2 ≤ k) (A : Finset ℕ) (hA : ∀ n ∈ A, 3 ≤ n ∧ n < k ∧ Odd n) :
    ∑ n ∈ A, (1 / n : ℝ) ≤ Real.log k / 2 := by
  set j := (k - 2) / 2
  have hsub : A ⊆ (range j).image oddMap := by
    intro n hn
    obtain ⟨h3, hk', ⟨m, hm⟩⟩ := hA n hn
    rw [mem_image]
    refine ⟨m - 1, mem_range.mpr (by omega), by simp only [oddMap]; omega⟩
  calc ∑ n ∈ A, (1 / n : ℝ) ≤ ∑ n ∈ (range j).image oddMap, (1 / n : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ i ∈ range j, (1 / (2 * i + 3 : ℝ)) := by
        rw [sum_image (by intro a _ b _ h; simp only [oddMap] at h; omega)]
        simp only [oddMap]; push_cast; rfl
    _ ≤ Real.log (2 * j + 1) / 2 := odd_harmonic j
    _ ≤ Real.log k / 2 := by
        have h1 : (2 * (j : ℝ) + 1) ≤ k := by
          have : 2 * j + 1 ≤ k := by omega
          exact_mod_cast this
        have : Real.log (2 * j + 1) ≤ Real.log k := Real.log_le_log (by positivity) h1
        linarith

/-- **Lemma 6.7(b).** For `k ≥ 3`, `N ≥ 2` and `|s_n| ≤ 1`,
`|∑_{N < n < k, n odd} (1/k) cot(π n/(2k)) s_n| ≤ (1/π) log k`. -/
theorem tail_trivial (k N : ℕ) (hk : 3 ≤ k) (hN : 2 ≤ N) (s : ℕ → ℝ) (hs : ∀ n, |s n| ≤ 1) :
    |∑ n ∈ (Ioo N k).filter Odd, (1 / k : ℝ) * Real.cot (Real.pi * n / (2 * k)) * s n| ≤
      Real.log k / Real.pi := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hpi := Real.pi_pos
  have hterm : ∀ n ∈ (Ioo N k).filter Odd,
      |(1 / k : ℝ) * Real.cot (Real.pi * n / (2 * k)) * s n| ≤ (2 / Real.pi) * (1 / n) := by
    intro n hn
    simp only [mem_filter, mem_Ioo] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hnk : (n : ℝ) < k := by exact_mod_cast hn.1.2
    have hx0 : 0 < Real.pi * n / (2 * k) := by positivity
    have hx2 : Real.pi * n / (2 * k) < Real.pi / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have hc0 := cot_nonneg hx0 hx2
    have hc1 := cot_le_inv hx0 hx2
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1 / k : ℝ) * Real.cot (Real.pi * n / (2 * k)))]
    have hsn := hs n
    calc (1 / k : ℝ) * Real.cot (Real.pi * n / (2 * k)) * |s n|
        ≤ (1 / k) * (1 / (Real.pi * n / (2 * k))) * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hc1 (by positivity)) hsn (abs_nonneg _)
          positivity
      _ = (2 / Real.pi) * (1 / n) := by field_simp
  calc _ ≤ ∑ n ∈ (Ioo N k).filter Odd, |(1 / k : ℝ) * Real.cot (Real.pi * n / (2 * k)) * s n| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ (Ioo N k).filter Odd, (2 / Real.pi) * (1 / n : ℝ) := sum_le_sum hterm
    _ = (2 / Real.pi) * ∑ n ∈ (Ioo N k).filter Odd, (1 / n : ℝ) := by rw [mul_sum]
    _ ≤ (2 / Real.pi) * (Real.log k / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply odd_sum_le k (by omega)
        intro n hn
        simp only [mem_filter, mem_Ioo] at hn
        refine ⟨?_, hn.1.2, hn.2⟩
        obtain ⟨m, hm⟩ := hn.2
        omega
    _ = Real.log k / Real.pi := by field_simp

end ThetaSum

#print axioms ThetaSum.tail_trivial

/-! ### Lemma 6.7(a): partial summation -/

namespace ThetaSum

/-- Discrete Abel summation: with `A n = ∑_{N < m ≤ n} a m`,
`∑_{N < n < k} c n a n = ∑_{N < n < k} (c n - c (n+1)) A n + c k · A (k-1)` for `k > N`. -/
lemma abel_sum (c a : ℕ → ℝ) (N : ℕ) : ∀ k, N < k →
    ∑ n ∈ Ioo N k, c n * a n =
      ∑ n ∈ Ioo N k, (c n - c (n + 1)) * ∑ m ∈ Ioc N n, a m +
        c k * ∑ m ∈ Ioc N (k - 1), a m := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hk) with h | h
    · subst h
      have he : Ioo N (N + 1) = ∅ := by ext x; simp only [mem_Ioo, Finset.notMem_empty, iff_false]; omega
      simp [he]
    · have hI : Ioo N (k + 1) = insert k (Ioo N k) := by
        ext x; simp only [mem_Ioo, mem_insert]; omega
      have hk' : k ∉ Ioo N k := by simp
      rw [hI, sum_insert hk', sum_insert hk', ih h]
      have hA : ∑ m ∈ Ioc N k, a m = ∑ m ∈ Ioc N (k - 1), a m + a k := by
        have : Ioc N k = insert k (Ioc N (k - 1)) := by
          ext x; simp only [mem_Ioc, mem_insert]; omega
        rw [this, sum_insert (by simp only [mem_Ioc]; omega), add_comm]
      simp only [Nat.add_sub_cancel]
      rw [hA]; ring

/-- `cot x - cot y ≤ (y - x) / (sin x sin y)` for `0 < x ≤ y ≤ π/2`. -/
lemma cot_sub_cot {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ Real.pi / 2) :
    Real.cot x - Real.cot y ≤ (y - x) / (Real.sin x * Real.sin y) := by
  have hpi := Real.pi_pos
  have hsx : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx (by linarith)
  have hsy : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have e : Real.cot x - Real.cot y = Real.sin (y - x) / (Real.sin x * Real.sin y) := by
    rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.sin_sub]
    field_simp
  rw [e]
  apply div_le_div_of_nonneg_right (Real.sin_le (by linarith)) (by positivity)

/-- The weights `c(n) = (1/k) cot(π n/(2k))` satisfy `0 ≤ c(n) - c(n+1) ≤ π/(2 n (n+1))`
for `1 ≤ n < k`. -/
lemma cweight_diff (k n : ℕ) (hn : 1 ≤ n) (hnk : n < k) :
    0 ≤ (1 / k : ℝ) * Real.cot (Real.pi * n / (2 * k)) -
        (1 / k : ℝ) * Real.cot (Real.pi * (n + 1 : ℕ) / (2 * k)) ∧
    (1 / k : ℝ) * Real.cot (Real.pi * n / (2 * k)) -
        (1 / k : ℝ) * Real.cot (Real.pi * (n + 1 : ℕ) / (2 * k)) ≤
      Real.pi / (2 * (n * (n + 1))) := by
  have hpi := Real.pi_pos
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1k : ((n + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hnk
  set x := Real.pi * n / (2 * k)
  set y := Real.pi * (n + 1 : ℕ) / (2 * k)
  have hx : 0 < x := by positivity
  have hxy : x ≤ y := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ hpi.le; push_cast; linarith
  have hy : y ≤ Real.pi / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hsx : 2 / Real.pi * x ≤ Real.sin x := Real.mul_le_sin hx.le (by linarith)
  have hsy : 2 / Real.pi * y ≤ Real.sin y := Real.mul_le_sin (by linarith) hy
  have hsx0 : 0 < 2 / Real.pi * x := by positivity
  have hsy0 : 0 < 2 / Real.pi * y := by positivity
  constructor
  · rw [← mul_sub]
    apply mul_nonneg (by positivity)
    have := cot_sub_cot hx hxy hy
    have hsx' : 0 < Real.sin x := by linarith
    have hsy' : 0 < Real.sin y := by linarith
    -- monotonicity of cot: cot x - cot y = sin(y-x)/(sin x sin y) ≥ 0
    have e : Real.cot x - Real.cot y = Real.sin (y - x) / (Real.sin x * Real.sin y) := by
      rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.sin_sub]
      field_simp
    rw [e]
    apply div_nonneg _ (by positivity)
    apply Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  · rw [← mul_sub]
    have h1 := cot_sub_cot hx hxy hy
    have hprod : (2 / Real.pi * x) * (2 / Real.pi * y) ≤ Real.sin x * Real.sin y :=
      mul_le_mul hsx hsy hsy0.le (by linarith)
    have h2 : (y - x) / (Real.sin x * Real.sin y) ≤ (y - x) / ((2 / Real.pi * x) * (2 / Real.pi * y)) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) hprod
    have h3 : (1 / k : ℝ) * ((y - x) / ((2 / Real.pi * x) * (2 / Real.pi * y))) =
        Real.pi / (2 * (n * (n + 1))) := by
      simp only [x, y]; push_cast; field_simp; ring
    calc (1 / k : ℝ) * (Real.cot x - Real.cot y)
        ≤ (1 / k) * ((y - x) / ((2 / Real.pi * x) * (2 / Real.pi * y))) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
      _ = _ := h3

/-- `∑_{N < n < k} 1/(n+1) ≤ log (k/N)` for `1 ≤ N < k`. -/
lemma sum_inv_succ_le_log (N : ℕ) (hN : 1 ≤ N) : ∀ k, N < k →
    ∑ n ∈ Ioo N k, (1 / ((n : ℝ) + 1)) ≤ Real.log k - Real.log N := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hk) with h | h
    · subst h
      have he : Ioo N (N + 1) = ∅ := by ext x; simp only [mem_Ioo, Finset.notMem_empty, iff_false]; omega
      rw [he, sum_empty]
      push_cast
      have : Real.log N ≤ Real.log (N + 1) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < N)) (by linarith)
      linarith
    · have hI : Ioo N (k + 1) = insert k (Ioo N k) := by
        ext x; simp only [mem_Ioo, mem_insert]; omega
      rw [hI, sum_insert (by simp)]
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have key : 1 / ((k : ℝ) + 1) ≤ Real.log (k + 1) - Real.log k := by
        rw [← Real.log_div (by positivity) hk0.ne']
        have hl := Real.log_le_sub_one_of_pos (show 0 < (k : ℝ) / (k + 1) by positivity)
        have : Real.log ((k + 1) / k) = -Real.log ((k : ℝ) / (k + 1)) := by
          rw [← Real.log_inv, inv_div]
        rw [this]
        have e : (k : ℝ) / (k + 1) - 1 = -(1 / (k + 1)) := by field_simp; ring
        linarith
      push_cast
      linarith [ih h]

/-- **Lemma 6.7(a)** (tails by partial summation). Let `1 ≤ N < k` and let `a : ℕ → ℝ` have
partial sums `A t = ∑_{N < n ≤ t} a n` with `|A t| ≤ D t` for `N ≤ t < k`. Then
  `|∑_{N < n < k} (1/k) cot(π n/(2k)) a n| ≤ (π/2) D log(k/N)`.
(In the paper `a n = -g(n θ_k)` for odd `n` and `0` for even `n`, so the sum is `Φ_k^{>N}` and
`D` is `D_k`.) -/
theorem tail_partial_summation (k N : ℕ) (hN : 1 ≤ N) (hNk : N < k) (a : ℕ → ℝ) (D : ℝ)
    (hD : ∀ t, N ≤ t → t < k → |∑ n ∈ Ioc N t, a n| ≤ D * t) :
    |∑ n ∈ Ioo N k, (1 / k : ℝ) * Real.cot (Real.pi * n / (2 * k)) * a n| ≤
      Real.pi / 2 * D * (Real.log k - Real.log N) := by
  set c : ℕ → ℝ := fun n => (1 / k : ℝ) * Real.cot (Real.pi * n / (2 * k))
  have hck : c k = 0 := by
    simp only [c]
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have : Real.pi * k / (2 * k) = Real.pi / 2 := by field_simp
    rw [this, Real.cot_eq_cos_div_sin, Real.cos_pi_div_two]; simp
  have hab := abel_sum c a N k hNk
  simp only [c] at hab hck
  rw [hab, hck, zero_mul, add_zero]
  have hD0 : 0 ≤ D := by
    have := hD N le_rfl hNk
    simp only [Ioc_self, sum_empty, abs_zero] at this
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    nlinarith
  have hpi := Real.pi_pos
  calc |∑ n ∈ Ioo N k, ((1 / k : ℝ) * Real.cot (Real.pi * n / (2 * k)) -
          (1 / k : ℝ) * Real.cot (Real.pi * (n + 1 : ℕ) / (2 * k))) * ∑ m ∈ Ioc N n, a m|
      ≤ ∑ n ∈ Ioo N k, |((1 / k : ℝ) * Real.cot (Real.pi * n / (2 * k)) -
          (1 / k : ℝ) * Real.cot (Real.pi * (n + 1 : ℕ) / (2 * k))) * ∑ m ∈ Ioc N n, a m| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Ioo N k, Real.pi / 2 * D * (1 / ((n : ℝ) + 1)) := by
        apply sum_le_sum; intro n hn
        simp only [mem_Ioo] at hn
        obtain ⟨h0, h1⟩ := cweight_diff k n (by omega) hn.2
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        rw [abs_mul, abs_of_nonneg h0]
        have hA := hD n hn.1.le hn.2
        calc _ ≤ Real.pi / (2 * (n * (n + 1))) * (D * n) :=
              mul_le_mul h1 hA (abs_nonneg _) (by positivity)
          _ = Real.pi / 2 * D * (1 / ((n : ℝ) + 1)) := by field_simp
    _ = Real.pi / 2 * D * ∑ n ∈ Ioo N k, (1 / ((n : ℝ) + 1)) := by rw [mul_sum]
    _ ≤ Real.pi / 2 * D * (Real.log k - Real.log N) :=
        mul_le_mul_of_nonneg_left (sum_inv_succ_le_log N hN k hNk) (by positivity)

end ThetaSum

#print axioms ThetaSum.tail_partial_summation
