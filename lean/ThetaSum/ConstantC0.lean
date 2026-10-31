import ThetaSum.TheoremCStar

/-!
# The constant `c₀` of Theorem B / Theorem C

`K₀ = γ + log(4/π)`, `c₀ = K₀/2 - (4/π²) ∑_{k odd} log k / k²`.

* `Cp_one_asymp`: `C_m(1) = (m/π)(log m + K₀) + O(1)` for odd `m` (comparison of `cot` with `1/y`,
  the odd harmonic sum via the Euler–Mascheroni bounds, and the Riemann sum of
  `1/y - cot y = (log(y / sin y))'` by the mean value theorem).
* `I_asymp_K0`: `|πλ I(λ) - log(1/λ) - K₀| ≤ λ (4 log(1/λ) + 91)` for `0 < λ ≤ 1` (Lemma 4.2,
  weak form), from `I(1/m) = C_m(1)` and monotonicity of `I`.
* `Psi_asymp`: `Ψ(p) = (p/2) log p + c₀ p + o(p)`.
* `theorem_B_c0`: `S(p) = (p/2) log p + c₀ p + (4p/π) R_K(p) + o(p)`, `K = KW34 p`.
* `theorem_C_c0`, `theorem_C_star_c0`: Theorems C and C* with `c = c₀`.
-/

open Finset Filter

namespace ThetaSum

/-- `K₀ = γ + log(4/π)`. -/
noncomputable def Kzero : ℝ := Real.eulerMascheroniConstant + Real.log (4 / Real.pi)

/-- `∑_{k odd} log k / k² = ∑_{j ≥ 0} log(2j+1)/(2j+1)²`. -/
noncomputable def SLodd : ℝ := ∑' j : ℕ, Real.log (2 * j + 1) / (2 * (j : ℝ) + 1) ^ 2

/-- **The constant** `c₀ = K₀/2 - (4/π²) ∑_{k odd} log k / k²`. -/
noncomputable def c0 : ℝ := Kzero / 2 - 4 / Real.pi ^ 2 * SLodd

end ThetaSum

namespace TheoremB

open Real
open Arxiv.«2501.03234» Recip

/-! ### The odd harmonic sum -/

lemma odd_harm_eq (h : ℕ) :
    ∑ j ∈ range h, 1 / (2 * (j : ℝ) + 1) = (harmonic (2 * h) : ℝ) - (harmonic h : ℝ) / 2 := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [sum_range_succ, ih, show 2 * (h + 1) = 2 * h + 1 + 1 by ring, harmonic_succ, harmonic_succ,
      harmonic_succ]
    push_cast
    field_simp
    ring

lemma harm_log {n : ℕ} (hn : 1 ≤ n) :
    |(harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant| ≤ 1 / n := by
  have h1 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  have h2 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  rw [Real.eulerMascheroniSeq] at h1
  rw [Real.eulerMascheroniSeq', ite_eq_right_iff.mpr (fun h => absurd h (by omega))] at h2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h3 : Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
    rw [← Real.log_div (by positivity) hnR.ne']
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
    have e : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
    linarith
  rw [abs_le]; constructor <;> linarith

lemma odd_harm_asymp {h : ℕ} (hh : 1 ≤ h) :
    |∑ j ∈ range h, 1 / (2 * (j : ℝ) + 1) -
      (Real.log h / 2 + Real.log 2 + Real.eulerMascheroniConstant / 2)| ≤ 1 / h := by
  rw [odd_harm_eq]
  have hA := harm_log (n := 2 * h) (by omega)
  have hB := harm_log hh
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  push_cast at hA
  rw [Real.log_mul (by norm_num) hhR.ne'] at hA
  have e : 1 / (2 * (h : ℝ)) = 1 / h / 2 := by field_simp
  rw [e] at hA
  rw [abs_le] at hA hB ⊢
  constructor <;> linarith [hA.1, hA.2, hB.1, hB.2]

/-! ### The Riemann sum of `1/y - cot y` -/

/-- `F(y) = log y - log sin y`, an antiderivative of `1/y - cot y` on `(0, π)`. -/
noncomputable def Fl (y : ℝ) : ℝ := Real.log y - Real.log (Real.sin y)

/-- `g(y) = 1/y - cot y`. -/
noncomputable def gc (y : ℝ) : ℝ := y⁻¹ - Real.cos y / Real.sin y

lemma gc_eq (y : ℝ) : gc y = 1 / y - Real.cot y := by
  rw [gc, Real.cot_eq_cos_div_sin, one_div]

lemma hasDerivAt_Fl {y : ℝ} (h0 : 0 < y) (h1 : y < π) : HasDerivAt Fl (gc y) y := by
  have hs : Real.sin y ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi h0 h1).ne'
  exact (Real.hasDerivAt_log h0.ne').sub ((Real.hasDerivAt_sin y).log hs)

lemma hasDerivAt_gc {y : ℝ} (h0 : 0 < y) (h1 : y < π) :
    HasDerivAt gc (-(y ^ 2)⁻¹ - ((-Real.sin y) * Real.sin y - Real.cos y * Real.cos y) /
      Real.sin y ^ 2) y := by
  have hs : Real.sin y ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi h0 h1).ne'
  exact (hasDerivAt_inv h0.ne').sub ((Real.hasDerivAt_cos y).div (Real.hasDerivAt_sin y) hs)

lemma gc_mono : MonotoneOn gc (Set.Ioo 0 (π / 2)) := by
  have hpi := Real.pi_pos
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo 0 (π / 2))
    (f' := fun y => -(y ^ 2)⁻¹ - ((-Real.sin y) * Real.sin y - Real.cos y * Real.cos y) /
      Real.sin y ^ 2) ?_ ?_ ?_
  · intro x hx
    exact (hasDerivAt_gc hx.1 (by linarith [hx.2])).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    exact (hasDerivAt_gc hx.1 (by linarith [hx.2])).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2])
    have hsx : Real.sin x ≤ x := Real.sin_le hx.1.le
    have e : (-Real.sin x) * Real.sin x - Real.cos x * Real.cos x = -1 := by
      have := Real.sin_sq_add_cos_sq x; nlinarith
    rw [e]
    have : (x ^ 2)⁻¹ ≤ (Real.sin x ^ 2)⁻¹ := by
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_left₀ hs.le hsx 2
    have : -(x ^ 2)⁻¹ - -1 / Real.sin x ^ 2 = (Real.sin x ^ 2)⁻¹ - (x ^ 2)⁻¹ := by ring
    linarith

lemma gc_nonneg {y : ℝ} (h0 : 0 < y) (h1 : y < π / 2) : 0 ≤ gc y := by
  rw [gc_eq]; have := cot_le_inv h0 h1; linarith

lemma gc_le_two {y : ℝ} (h0 : 0 < y) (h1 : y ≤ π / 2) : gc y ≤ 2 := by
  rw [gc_eq]; have := cot_ge h0 h1; linarith

/-- One step: `|(b-a) g(c) - (F b - F a)| ≤ (b-a)(g b - g a)` for `0 < a ≤ c ≤ b < π/2`. -/
lemma step_bound {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < π / 2) (hac : a ≤ c)
    (hcb : c ≤ b) : |(b - a) * gc c - (Fl b - Fl a)| ≤ (b - a) * (gc b - gc a) := by
  have hpi := Real.pi_pos
  have hcont : ContinuousOn Fl (Set.Icc a b) := fun x hx =>
    (hasDerivAt_Fl (by linarith [hx.1]) (by linarith [hx.2])).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope Fl gc hab hcont
    (fun x hx => hasDerivAt_Fl (by linarith [hx.1]) (by linarith [hx.2]))
  have hba : 0 < b - a := by linarith
  have hF : Fl b - Fl a = (b - a) * gc ξ := by rw [hξe]; field_simp
  rw [hF, ← mul_sub, abs_mul, abs_of_pos hba]
  apply mul_le_mul_of_nonneg_left _ hba.le
  have mem : ∀ t, a ≤ t → t ≤ b → t ∈ Set.Ioo 0 (π / 2) := fun t h1 h2 => ⟨by linarith, by linarith⟩
  have m1 := gc_mono (mem a le_rfl hab.le) (mem c hac hcb) hac
  have m2 := gc_mono (mem c hac hcb) (mem b hab.le le_rfl) hcb
  have m3 := gc_mono (mem a le_rfl hab.le) (mem ξ hξ.1.le hξ.2.le) hξ.1.le
  have m4 := gc_mono (mem ξ hξ.1.le hξ.2.le) (mem b hab.le le_rfl) hξ.2.le
  rw [abs_le]; constructor <;> linarith

lemma Fl_small {d : ℝ} (h0 : 0 < d) (h1 : d ≤ 1) : 0 ≤ Fl d ∧ Fl d ≤ d := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hs : 0 < Real.sin d := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
  have hsd : Real.sin d ≤ d := Real.sin_le h0.le
  have hj : 2 / π * d ≤ Real.sin d := Real.mul_le_sin h0.le (by linarith)
  have hc : d - d ^ 3 / 6 < Real.sin d := Real.sin_gt_sub_cube h0
  constructor
  · unfold Fl; have := Real.log_le_log hs hsd; linarith
  · unfold Fl
    rw [← Real.log_div h0.ne' hs.ne']
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [div_sub_one hs.ne', div_le_iff₀ hs]
    have h2 : d * (2 / π * d) ≤ d * Real.sin d := mul_le_mul_of_nonneg_left hj h0.le
    have h3 : d ^ 3 / 6 ≤ d * (2 / π * d) := by
      rw [show d * (2 / π * d) = d ^ 2 * (2 / π) by ring, show d ^ 3 / 6 = d ^ 2 * (d / 6) by ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [le_div_iff₀ hpi]
      calc d / 6 * π ≤ 1 / 6 * 4 := by
            apply mul_le_mul (by linarith) (by linarith [Real.pi_lt_four]) hpi.le (by norm_num)
        _ ≤ 2 := by norm_num
    linarith

lemma Fl_top {d : ℝ} (h0 : 0 < d) (h1 : d ≤ π / 5) :
    |Fl (π / 2 - d / 2) - Real.log (π / 2)| ≤ d := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  unfold Fl
  rw [Real.sin_pi_div_two_sub]
  have hc : 0 < Real.cos (d / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hc1 : Real.cos (d / 2) ≤ 1 := Real.cos_le_one _
  have hc2 : 1 - (d / 2) ^ 2 / 2 ≤ Real.cos (d / 2) := Real.one_sub_sq_div_two_le_cos
  have hlc : Real.log (Real.cos (d / 2)) ≤ 0 := Real.log_nonpos hc.le hc1
  have hlc2 : -(d / 4) ≤ Real.log (Real.cos (d / 2)) := by
    have := Real.one_sub_inv_le_log_of_pos hc
    have hd : d ≤ 1 := by linarith
    have hc12 : 1 / 2 ≤ Real.cos (d / 2) := by nlinarith
    have : 1 - (Real.cos (d / 2))⁻¹ ≥ -(d / 4) := by
      rw [ge_iff_le, ← sub_nonneg]
      have e : 1 - (Real.cos (d / 2))⁻¹ - -(d / 4) =
          (Real.cos (d / 2) - 1 + d / 4 * Real.cos (d / 2)) / Real.cos (d / 2) := by
        field_simp; ring
      rw [e]; apply div_nonneg _ hc.le
      nlinarith
    linarith
  have hq : 0 < π / 2 - d / 2 := by linarith
  have hl1 : Real.log (π / 2 - d / 2) ≤ Real.log (π / 2) := Real.log_le_log hq (by linarith)
  have hl2 : Real.log (π / 2) - d / 2 ≤ Real.log (π / 2 - d / 2) := by
    have e : π / 2 - d / 2 = π / 2 * (1 - d / π) := by field_simp
    rw [e, Real.log_mul (by positivity) (by
      have : d / π < 1 := by rw [div_lt_one hpi]; linarith
      linarith)]
    have ht : d / π ≤ 1 / 5 := by rw [div_le_iff₀ hpi]; linarith
    have h1t : 0 < 1 - d / π := by linarith
    have := Real.one_sub_inv_le_log_of_pos h1t
    have hπd : π - d ≠ 0 := by linarith
    have e2 : 1 - (1 - d / π)⁻¹ = -(d / π) / (1 - d / π) := by field_simp; ring
    rw [e2] at this
    have h3 : -(d / 2) ≤ -(d / π) / (1 - d / π) := by
      rw [le_div_iff₀ h1t]
      have h4 : d / π ≤ d / 3 := div_le_div_of_nonneg_left h0.le (by norm_num) hpi3.le
      nlinarith
    linarith
  rw [abs_le]; constructor <;> linarith

lemma tele_real (f : ℝ → ℝ) (d : ℝ) (n : ℕ) :
    ∑ i ∈ range n, (f (((i : ℝ) + 2) * d) - f (((i : ℝ) + 1) * d)) = f (((n : ℝ) + 1) * d) - f d := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]; push_cast
    rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]; ring

/-- **Riemann sum.** For `m = 2h+1 ≥ 5`, `|∑_{j<h} (1/y_j - cot y_j) - (m/π) log(π/2)| ≤ 6`,
`y_j = π(2j+1)/(2m)`. -/
lemma gsum_asymp {h : ℕ} (hh : 2 ≤ h) :
    |∑ j ∈ range h, gc (π * (2 * j + 1) / (2 * (2 * h + 1))) -
      (2 * h + 1) / π * Real.log (π / 2)| ≤ 6 := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 1 := ⟨h - 1, by omega⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  set m : ℝ := 2 * ((n + 1 : ℕ) : ℝ) + 1 with hm
  have hmR : m = 2 * (n : ℝ) + 3 := by rw [hm]; push_cast; ring
  have hm5 : 5 ≤ m := by linarith
  set d := π / m with hd
  have hd0 : 0 < d := by positivity
  have hd1 : d ≤ π / 5 := div_le_div_of_nonneg_left hpi.le (by norm_num) hm5
  have hd1' : d ≤ 1 := by linarith
  have hc : ∀ i : ℕ, π * (2 * ((i + 1 : ℕ) : ℝ) + 1) / (2 * m) = ((i : ℝ) + 3 / 2) * d := by
    intro i; rw [hd]; push_cast; field_simp; ring
  have hc0 : π * (2 * ((0 : ℕ) : ℝ) + 1) / (2 * m) = d / 2 := by
    rw [hd]; push_cast; ring
  have hhd : ((n : ℝ) + 1) * d = π / 2 - d / 2 := by rw [hd, hmR]; field_simp; ring
  rw [sum_range_succ', hc0]
  simp only [hc]
  have hstep : ∀ i ∈ range n,
      |d * gc (((i : ℝ) + 3 / 2) * d) - (Fl (((i : ℝ) + 2) * d) - Fl (((i : ℝ) + 1) * d))| ≤
        d * (gc (((i : ℝ) + 2) * d) - gc (((i : ℝ) + 1) * d)) := by
    intro i hi
    simp only [mem_range] at hi
    have hiR : (i : ℝ) + 2 ≤ n + 1 := by exact_mod_cast (by omega : i + 2 ≤ n + 1)
    have hb : ((i : ℝ) + 2) * d < π / 2 := by
      calc ((i : ℝ) + 2) * d ≤ ((n : ℝ) + 1) * d := mul_le_mul_of_nonneg_right hiR hd0.le
        _ < π / 2 := by linarith
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have := step_bound (a := ((i : ℝ) + 1) * d) (b := ((i : ℝ) + 2) * d)
      (c := ((i : ℝ) + 3 / 2) * d) (by positivity) (by nlinarith) hb (by nlinarith) (by nlinarith)
    have e : ((i : ℝ) + 2) * d - ((i : ℝ) + 1) * d = d := by ring
    rwa [e] at this
  have hS1 := (abs_sum_le_sum_abs _ _).trans (sum_le_sum hstep)
  have eL : ∑ i ∈ range n, (d * gc (((i : ℝ) + 3 / 2) * d) -
      (Fl (((i : ℝ) + 2) * d) - Fl (((i : ℝ) + 1) * d))) =
      d * ∑ i ∈ range n, gc (((i : ℝ) + 3 / 2) * d) - (Fl (((n : ℝ) + 1) * d) - Fl d) := by
    rw [sum_sub_distrib, tele_real Fl d n, mul_sum]
  have eR : ∑ i ∈ range n, d * (gc (((i : ℝ) + 2) * d) - gc (((i : ℝ) + 1) * d)) =
      d * (gc (((n : ℝ) + 1) * d) - gc d) := by
    rw [← mul_sum, tele_real gc d n]
  rw [eL, eR, hhd] at hS1
  have hgn := gc_le_two (show 0 < π / 2 - d / 2 by linarith) (by linarith)
  have hg1 := gc_nonneg hd0 (by linarith)
  have hg0 := gc_nonneg (show 0 < d / 2 by positivity) (by linarith)
  have hg0' := gc_le_two (show 0 < d / 2 by positivity) (by linarith)
  have hFt := Fl_top hd0 hd1
  have hFb := Fl_small hd0 hd1'
  have hmd : m / π * d = 1 := by rw [hd]; field_simp
  set sg := ∑ i ∈ range n, gc (((i : ℝ) + 3 / 2) * d)
  have key : |d * (sg + gc (d / 2)) - Real.log (π / 2)| ≤ 6 * d := by
    have hdg0 : 0 ≤ d * gc (d / 2) := mul_nonneg hd0.le hg0
    have hdg2 : d * gc (d / 2) ≤ 2 * d := by nlinarith
    have hR : d * (gc (π / 2 - d / 2) - gc d) ≤ 2 * d := by nlinarith
    rw [abs_le] at hS1 hFt ⊢
    constructor <;> nlinarith [hFb.1, hFb.2]
  have e2 : sg + gc (d / 2) - m / π * Real.log (π / 2) =
      m / π * (d * (sg + gc (d / 2)) - Real.log (π / 2)) := by
    rw [mul_sub, ← mul_assoc, hmd, one_mul]
  rw [e2, abs_mul, abs_of_pos (show 0 < m / π by positivity)]
  calc m / π * |d * (sg + gc (d / 2)) - Real.log (π / 2)| ≤ m / π * (6 * d) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = 6 := by rw [show m / π * (6 * d) = 6 * (m / π * d) by ring, hmd, mul_one]

/-! ### `C_m(1)` and `I(λ)` -/

lemma Kzero_bounds : 0 ≤ ThetaSum.Kzero ∧ ThetaSum.Kzero ≤ 1 := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  have hγ1 := Real.one_half_lt_eulerMascheroniConstant
  have hγ2 := Real.eulerMascheroniConstant_lt_two_thirds
  have h1 : 0 ≤ Real.log (4 / π) := Real.log_nonneg (by rw [le_div_iff₀ hpi]; linarith)
  have h2 : Real.log (4 / π) ≤ 1 / 3 := by
    have := Real.log_le_sub_one_of_pos (show 0 < 4 / π by positivity)
    have : 4 / π ≤ 4 / 3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpi3.le
    linarith
  unfold ThetaSum.Kzero
  constructor <;> linarith

/-- **`C_m(1) = (m/π)(log m + K₀) + O(1)`** for `m = 2h+1 ≥ 5`. -/
lemma Cp_one_asymp {h : ℕ} (hh : 2 ≤ h) :
    |Cp (2 * h + 1) 1 - (2 * (h : ℝ) + 1) / π * (Real.log (2 * (h : ℝ) + 1) + ThetaSum.Kzero)| ≤ 9 := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hhR : (2 : ℝ) ≤ h := by exact_mod_cast hh
  rw [Cp_one_eq, sum_odd_range]
  have hterm : ∀ x ∈ range h, Real.cot (π * ((2 * x + 1 : ℕ) : ℝ) / (2 * ((2 * h + 1 : ℕ) : ℝ))) =
      2 * (2 * (h : ℝ) + 1) / π * (1 / (2 * (x : ℝ) + 1)) -
        gc (π * (2 * x + 1) / (2 * (2 * h + 1))) := by
    intro x _
    rw [gc_eq]; push_cast; field_simp; ring
  rw [sum_congr rfl hterm, sum_sub_distrib, ← mul_sum]
  set M : ℝ := 2 * (h : ℝ) + 1 with hM
  set O := ∑ x ∈ range h, 1 / (2 * (x : ℝ) + 1)
  set G := ∑ x ∈ range h, gc (π * (2 * x + 1) / (2 * (2 * h + 1)))
  have hO := odd_harm_asymp (h := h) (by omega)
  have hG := gsum_asymp hh
  rw [← hM] at hG
  set A := Real.log h / 2 + Real.log 2 + Real.eulerMascheroniConstant / 2
  set D := Real.log 2 + Real.log h - Real.log M
  have hK : Real.log (4 / π) = 2 * Real.log 2 - Real.log π := by
    rw [Real.log_div (by norm_num) hpi.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hP : Real.log (π / 2) = Real.log π - Real.log 2 := Real.log_div hpi.ne' (by norm_num)
  have e : 2 * M / π * O - G - M / π * (Real.log M + ThetaSum.Kzero) =
      2 * M / π * (O - A) - (G - M / π * Real.log (π / 2)) + M / π * D := by
    simp only [A, D, ThetaSum.Kzero]; rw [hK, hP]; ring
  rw [e]
  have hhpos : (0 : ℝ) < h := by linarith
  have hD1 : D ≤ 0 := by
    simp only [D]
    rw [← Real.log_mul (by norm_num) hhpos.ne']
    have := Real.log_le_log (by positivity) (show 2 * (h : ℝ) ≤ M by rw [hM]; linarith)
    linarith
  have hD2 : -(1 / (2 * h)) ≤ D := by
    simp only [D]
    rw [← Real.log_mul (by norm_num) hhpos.ne', ← Real.log_div (by positivity) (by positivity)]
    have := Real.one_sub_inv_le_log_of_pos (show 0 < 2 * (h : ℝ) / M by positivity)
    have e2 : 1 - (2 * (h : ℝ) / M)⁻¹ = -(1 / (2 * h)) := by rw [hM]; field_simp; ring
    linarith
  have hMD : |M / π * D| ≤ 1 := by
    rw [abs_mul, abs_of_pos (by positivity), abs_of_nonpos hD1]
    calc M / π * -D ≤ M / π * (1 / (2 * h)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ 1 := by
          rw [div_mul_div_comm, div_le_one (by positivity), hM]; nlinarith
  have hOA : |2 * M / π * (O - A)| ≤ 2 := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc 2 * M / π * |O - A| ≤ 2 * M / π * (1 / h) := mul_le_mul_of_nonneg_left hO (by positivity)
      _ ≤ 2 := by
          rw [div_mul_div_comm, div_le_iff₀ (by positivity), hM]; nlinarith
  calc |2 * M / π * (O - A) - (G - M / π * Real.log (π / 2)) + M / π * D|
      ≤ |2 * M / π * (O - A)| + |G - M / π * Real.log (π / 2)| + |M / π * D| := by
        have h1 := abs_add_le (2 * M / π * (O - A) - (G - M / π * Real.log (π / 2))) (M / π * D)
        have h2 := abs_sub (2 * M / π * (O - A)) (G - M / π * Real.log (π / 2))
        linarith
    _ ≤ 2 + 6 + 1 := by linarith
    _ = 9 := by norm_num

/-- **Lemma 4.2 (weak form)**: `|πλ I(λ) - log(1/λ) - K₀| ≤ λ (4 log(1/λ) + 91)` for `0 < λ ≤ 1`. -/
theorem I_asymp_K0 {l : ℝ} (h0 : 0 < l) (h1 : l ≤ 1) :
    |π * l * Ifun l - Real.log (1 / l) - ThetaSum.Kzero| ≤ l * (4 * Real.log (1 / l) + 91) := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_d2
  obtain ⟨hK0, hK1⟩ := Kzero_bounds
  set K := ThetaSum.Kzero
  set x := 1 / l with hx
  have hx1 : 1 ≤ x := by rw [hx, le_div_iff₀ h0]; linarith
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  by_cases hl7 : 1 / 7 < l
  · have := I_asymp h0 h1
    rw [abs_le] at this ⊢
    constructor
    · nlinarith
    · nlinarith
  push_neg at hl7
  have hx7 : 7 ≤ x := by rw [hx, le_div_iff₀ h0]; linarith
  set h := ⌊(x - 1) / 2⌋₊ with hh
  have hfl := Nat.floor_le (show 0 ≤ (x - 1) / 2 by linarith)
  have hfl2 := Nat.lt_floor_add_one ((x - 1) / 2)
  rw [← hh] at hfl hfl2
  have hh3 : 3 ≤ h := by
    have : (3 : ℝ) ≤ (x - 1) / 2 := by linarith
    exact Nat.le_floor (by exact_mod_cast this)
  have hhR : (3 : ℝ) ≤ h := by exact_mod_cast hh3
  set m := 2 * h + 1 with hm
  have hmo : Odd m := ⟨h, rfl⟩
  have hmR : (m : ℝ) = 2 * h + 1 := by rw [hm]; push_cast; ring
  have hmx : (m : ℝ) ≤ x := by rw [hmR]; linarith
  have hxm : x < m + 2 := by rw [hmR]; linarith
  have hm1 : (7 : ℝ) ≤ m := by rw [hmR]; linarith
  have hlx : l = 1 / x := by rw [hx]; field_simp
  have hl_le : l ≤ 1 / m := by rw [hlx]; exact one_div_le_one_div_of_le (by linarith) hmx
  have hl_ge : 1 / ((m : ℝ) + 2) ≤ l := by rw [hlx]; exact one_div_le_one_div_of_le (by linarith) hxm.le
  have hI1 : Ifun (1 / m) ≤ Ifun l := Ifun_anti h0 hl_le (by rw [div_le_one (by linarith)]; linarith)
  have hI2 : Ifun l ≤ Ifun (1 / ((m : ℝ) + 2)) := Ifun_anti (by positivity) hl_ge h1
  rw [Ifun_inv_nat hmo] at hI1
  have hm2o : Odd (m + 2) := by rw [hm]; exact ⟨h + 1, by ring⟩
  have hI2' : Ifun (1 / ((m : ℝ) + 2)) = Cp (m + 2) 1 := by
    rw [← Ifun_inv_nat hm2o]; push_cast; rfl
  rw [hI2'] at hI2
  have hA1 := Cp_one_asymp (h := h) (by omega)
  have hA2 := Cp_one_asymp (h := h + 1) (by omega)
  rw [show 2 * (h + 1) + 1 = m + 2 by rw [hm]; ring] at hA2
  rw [← hm] at hA1
  push_cast at hA2
  rw [← hmR] at hA1
  rw [show 2 * ((h : ℝ) + 1) + 1 = (m : ℝ) + 2 by rw [hmR]; ring] at hA2
  rw [abs_le] at hA1 hA2
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by linarith)
  have hlm1 : l * m ≤ 1 := by
    calc l * m ≤ 1 / m * m := mul_le_mul_of_nonneg_right hl_le (by linarith)
      _ = 1 := by field_simp
  have hlm2 : 1 - 2 * l ≤ l * m := by
    have : 1 ≤ l * ((m : ℝ) + 2) := by
      have := mul_le_mul_of_nonneg_right hl_ge (show (0 : ℝ) ≤ m + 2 by linarith)
      rwa [one_div_mul_cancel (by linarith)] at this
    linarith
  have hlogxm : Real.log x ≤ Real.log m + 4 * l := by
    have h1 : Real.log x ≤ Real.log ((m : ℝ) + 2) := Real.log_le_log (by linarith) hxm.le
    have h2 : Real.log ((m : ℝ) + 2) - Real.log m ≤ 2 / m := by
      rw [← Real.log_div (by linarith) (by linarith)]
      have := Real.log_le_sub_one_of_pos (show 0 < ((m : ℝ) + 2) / m by positivity)
      have e : ((m : ℝ) + 2) / m - 1 = 2 / m := by field_simp; ring
      linarith
    have h3 : 2 / (m : ℝ) ≤ 4 * l := by
      rw [div_le_iff₀ (by linarith), hlx]
      have : x ≤ 2 * m := by linarith
      rw [show 4 * (1 / x) * (m : ℝ) = 4 * m / x by ring, le_div_iff₀ (by linarith)]
      linarith
    linarith
  have hlogm2 : Real.log ((m : ℝ) + 2) ≤ Real.log x + 2 * l := by
    have h1 : Real.log ((m : ℝ) + 2) ≤ Real.log (x + 2) := Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log (x + 2) - Real.log x ≤ 2 / x := by
      rw [← Real.log_div (by linarith) (by linarith)]
      have := Real.log_le_sub_one_of_pos (show 0 < (x + 2) / x by positivity)
      have e : (x + 2) / x - 1 = 2 / x := by field_simp; ring
      linarith
    have : 2 / x = 2 * l := by rw [hlx]; field_simp
    linarith
  rw [abs_le]
  constructor
  · -- lower bound
    have s1 : π * l * Cp m 1 ≤ π * l * Ifun l := mul_le_mul_of_nonneg_left hI1 (by positivity)
    have s2 : π * l * ((m : ℝ) / π * (Real.log m + K) - 9) ≤ π * l * Cp m 1 :=
      mul_le_mul_of_nonneg_left (by linarith [hA1.1]) (by positivity)
    have e : π * l * ((m : ℝ) / π * (Real.log m + K) - 9) = l * m * (Real.log m + K) - 9 * π * l := by
      field_simp
    have s3 : (1 - 2 * l) * (Real.log x - 4 * l + K) ≤ l * m * (Real.log m + K) := by
      apply mul_le_mul hlm2 (by linarith) _ (by positivity)
      have : Real.log 7 ≤ Real.log x := Real.log_le_log (by norm_num) hx7
      have : 1 ≤ Real.log 7 := by
        rw [Real.le_log_iff_exp_le (by norm_num)]; have := Real.exp_one_lt_d9; linarith
      linarith
    have : Real.log (1 / l) = Real.log x := rfl
    rw [this]
    nlinarith
  · -- upper bound
    have s1 : π * l * Ifun l ≤ π * l * Cp (m + 2) 1 := mul_le_mul_of_nonneg_left hI2 (by positivity)
    have s2 : π * l * Cp (m + 2) 1 ≤ π * l * (((m : ℝ) + 2) / π * (Real.log ((m : ℝ) + 2) + K) + 9) :=
      mul_le_mul_of_nonneg_left (by push_cast at hA2 ⊢; linarith [hA2.2]) (by positivity)
    have e : π * l * (((m : ℝ) + 2) / π * (Real.log ((m : ℝ) + 2) + K) + 9) =
        l * ((m : ℝ) + 2) * (Real.log ((m : ℝ) + 2) + K) + 9 * π * l := by field_simp
    have hlm3 : l * ((m : ℝ) + 2) ≤ 1 + 2 * l := by linarith
    have hlogm2' : 0 ≤ Real.log ((m : ℝ) + 2) := Real.log_nonneg (by linarith)
    have s3 : l * ((m : ℝ) + 2) * (Real.log ((m : ℝ) + 2) + K) ≤ (1 + 2 * l) * (Real.log x + 2 * l + K) :=
      mul_le_mul hlm3 (by linarith) (by linarith) (by linarith)
    have : Real.log (1 / l) = Real.log x := rfl
    rw [this]
    have s4 : (1 + 2 * l) * (Real.log x + 2 * l + K) =
        Real.log x + K + 2 * l + 2 * (l * Real.log x) + 4 * (l * l) + 2 * (l * K) := by ring
    have hll : l * l ≤ l := mul_le_of_le_one_left h0.le h1
    have hlK : l * K ≤ l := mul_le_of_le_one_right h0.le hK1
    have h9 : 9 * π * l ≤ 29 * l := mul_le_mul_of_nonneg_right (by linarith) h0.le
    have hlx0' : 0 ≤ l * Real.log x := mul_nonneg h0.le hlx0
    have t : l * (4 * Real.log x + 91) = 4 * (l * Real.log x) + 91 * l := by ring
    rw [t]
    linarith

/-! ### `Ψ(p) = (p/2) log p + c₀ p + o(p)` -/

lemma gc_le_self {y : ℝ} (h0 : 0 < y) (h1 : y ≤ π / 2) : gc y ≤ y := by
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_lt_four
  have hs : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
  have hsy := Real.sin_le h0.le
  have hj := Real.mul_le_sin h0.le h1
  have hc := Real.one_sub_sq_div_two_le_cos (x := y)
  have e : gc y = (Real.sin y - y * Real.cos y) / (y * Real.sin y) := by
    unfold gc; field_simp
  rw [e, div_le_iff₀ (by positivity)]
  have h1' : Real.sin y - y * Real.cos y ≤ y ^ 3 / 2 := by nlinarith
  have h2 : 2 / π * y * y ^ 2 ≤ Real.sin y * y ^ 2 := mul_le_mul_of_nonneg_right hj (by positivity)
  have h3 : y ^ 3 / 2 ≤ 2 / π * y * y ^ 2 := by
    rw [show 2 / π * y * y ^ 2 = y ^ 3 * (2 / π) by ring, show y ^ 3 / 2 = y ^ 3 * (1 / 2) by ring]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_le_div_iff₀ (by norm_num) hpi]; linarith
  nlinarith

lemma Psi_term_K {p k : ℕ} (hk0 : 0 < k) (hkp : k < p) :
    |2 / p * (Real.cot (π * k / (2 * p)) * Ifun ((k : ℝ) / p)) -
      4 * p / (π ^ 2 * k ^ 2) * (Real.log p - Real.log k + ThetaSum.Kzero)| ≤
        1 / k * (2 * Real.log p + 41) + 1 / p * (Real.log p + 12) := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hpR : (0 : ℝ) < p := by exact_mod_cast (hk0.trans hkp)
  have hkp' : (k : ℝ) < p := by exact_mod_cast hkp
  have hl0 : 0 < (k : ℝ) / p := by positivity
  have hl1 : (k : ℝ) / p ≤ 1 := by rw [div_le_one hpR]; linarith
  have hasy := I_asymp_K0 hl0 hl1
  have hasy0 := I_asymp hl0 hl1
  set K := ThetaSum.Kzero
  set I := Ifun ((k : ℝ) / p) with hI
  have hI0 : 0 ≤ I := Ifun_nonneg hl0 hl1
  set L := Real.log p - Real.log k with hL
  have hlog : Real.log (1 / ((k : ℝ) / p)) = L := by
    rw [one_div_div, Real.log_div hpR.ne' hkR.ne']
  rw [hlog] at hasy hasy0
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk0)
  have hLp : L ≤ Real.log p := by rw [hL]; linarith
  have hL0 : 0 ≤ L := by
    rw [hL, sub_nonneg]; exact Real.log_le_log hkR hkp'.le
  set ε := π * ((k : ℝ) / p) * I - L - K with hε
  set y := π * k / (2 * p) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ π / 2 := by
    rw [hy, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  set δ := gc y with hδ
  have hd0 : 0 ≤ δ := gc_nonneg hy0 (lt_of_le_of_ne hy1 (by
    intro h; rw [hy, div_eq_div_iff (by positivity) (by norm_num)] at h; nlinarith))
  have hd1 : δ ≤ y := gc_le_self hy0 hy1
  have hcot : Real.cot y = 2 * p / (π * k) - δ := by
    rw [hδ, gc_eq, hy]; field_simp; ring
  have hIeq : I = p / (π * k) * (L + K + ε) := by
    rw [hε]; field_simp; ring
  have hE : 2 / p * (Real.cot y * I) - 4 * p / (π ^ 2 * k ^ 2) * (L + K) =
      4 * p / (π ^ 2 * k ^ 2) * ε - 2 / p * δ * I := by
    rw [hcot]
    have h4 : 2 / (p : ℝ) * (2 * p / (π * k)) * I = 4 * p / (π ^ 2 * k ^ 2) * (L + K + ε) := by
      rw [hIeq]; field_simp; ring
    have e1 : 2 / (p : ℝ) * ((2 * p / (π * k) - δ) * I) = 2 / (p : ℝ) * (2 * p / (π * k)) * I -
        2 / p * δ * I := by ring
    rw [e1, h4]; ring
  rw [hE]
  have hIle : I ≤ p / (π * k) * (Real.log p + 12) := by
    have hIeq0 : I = p / (π * k) * (π * ((k : ℝ) / p) * I) := by field_simp
    rw [hIeq0]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := (abs_le.1 hasy0).2
    linarith
  have hε' : |ε| ≤ (k : ℝ) / p * (4 * Real.log p + 91) := by
    refine hasy.trans ?_
    apply mul_le_mul_of_nonneg_left _ hl0.le
    linarith
  have t1 : |4 * p / (π ^ 2 * k ^ 2) * ε| ≤ 1 / k * (2 * Real.log p + 41) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc 4 * p / (π ^ 2 * k ^ 2) * |ε| ≤ 4 * p / (π ^ 2 * k ^ 2) * ((k : ℝ) / p * (4 * Real.log p + 91)) :=
          mul_le_mul_of_nonneg_left hε' (by positivity)
      _ = 1 / k * (4 / π ^ 2 * (4 * Real.log p + 91)) := by field_simp
      _ ≤ 1 / k * (2 * Real.log p + 41) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hp9 : 4 / π ^ 2 ≤ 4 / 9 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
          have hlp : 0 ≤ Real.log p := by linarith
          have : 4 / π ^ 2 * (4 * Real.log p + 91) ≤ 4 / 9 * (4 * Real.log p + 91) :=
            mul_le_mul_of_nonneg_right hp9 (by linarith)
          linarith
  have t2 : |2 / p * δ * I| ≤ 1 / p * (Real.log p + 12) := by
    rw [abs_of_nonneg (by positivity)]
    calc 2 / (p : ℝ) * δ * I ≤ 2 / p * y * (p / (π * k) * (Real.log p + 12)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hd1 (by positivity)) hIle hI0 (by positivity)
      _ = 1 / p * (Real.log p + 12) := by rw [hy]; field_simp
  calc |4 * p / (π ^ 2 * k ^ 2) * ε - 2 / p * δ * I|
      ≤ |4 * p / (π ^ 2 * k ^ 2) * ε| + |2 / p * δ * I| := abs_sub _ _
    _ ≤ _ := add_le_add t1 t2

/-- `log(2j+1)/(2j+1)²`. -/
noncomputable def fodd (j : ℕ) : ℝ := Real.log (2 * j + 1) / (2 * (j : ℝ) + 1) ^ 2

lemma summable_fodd : Summable fodd := by
  have hg : Summable fun k : ℕ => Real.log k / (k : ℝ) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => log_div_sq_le k)
      ((Real.summable_nat_rpow_inv.2 (by norm_num : (1 : ℝ) < 3 / 2)).mul_left 2)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
      positivity
  have := hg.comp_injective (i := fun j : ℕ => 2 * j + 1) (fun a b h => by simpa using h)
  refine this.congr (fun j => ?_)
  simp only [Function.comp, fodd]; push_cast; ring

set_option maxHeartbeats 1000000 in
/-- **`Ψ(p) = (p/2) log p + c₀ p + o(p)`.** -/
theorem Psi_asymp : ∀ ε > 0, ∀ᶠ p : ℕ in atTop, Odd p →
    |Psi p - p / 2 * Real.log p - ThetaSum.c0 * p| ≤ ε * p := by
  intro ε hε
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have htail := _root_.tendsto_sum_nat_add fodd
  have ev1 := htail.eventually (gt_mem_nhds (show (0 : ℝ) < ε * π ^ 2 / 8 by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.mp ev1
  have hlogt : Tendsto (fun p : ℕ => (p : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have ev2 := hlogt.eventually (ThetaSum.ev_log_pow_le 2 (202 / ε) (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [ev2, eventually_ge_atTop (2 * N + 5)] with p h2 hpN hpo
  obtain ⟨h, rfl⟩ := hpo
  have hhN : N ≤ h := by omega
  have hh1 : 1 ≤ h := by omega
  have hhR : (2 : ℝ) ≤ h := by exact_mod_cast (by omega : 2 ≤ h)
  set p := 2 * h + 1 with hp
  have hpR' : (p : ℝ) = 2 * h + 1 := by rw [hp]; push_cast; ring
  have hpR : (5 : ℝ) ≤ p := by rw [hpR']; linarith
  have hp0 : (0 : ℝ) < p := by linarith
  simp only [Real.rpow_one] at h2
  have hlogp1 : 1 ≤ Real.log p := by
    rw [Real.le_log_iff_exp_le hp0]; have := Real.exp_one_lt_d9; linarith
  obtain ⟨hK0, hK1⟩ := Kzero_bounds
  set K := ThetaSum.Kzero
  set s := (range p).filter Odd with hs
  have hmem : ∀ k ∈ s, 0 < k ∧ k < p := by
    intro k hk; simp only [hs, mem_filter, mem_range] at hk; exact ⟨hk.2.pos, hk.1⟩
  set S2 := ∑ k ∈ s, 1 / (k : ℝ) ^ 2 with hS2
  set SL := ∑ k ∈ s, Real.log k / (k : ℝ) ^ 2 with hSL
  have hS2' : S2 = ∑ j ∈ range h, 1 / ((2 * j + 1 : ℕ) : ℝ) ^ 2 := by
    rw [hS2, hs, hp, sum_odd_range]
  obtain ⟨hS2a, hS2b⟩ := odd_sq_partial h hh1
  rw [← hS2'] at hS2a hS2b
  have hSL' : SL = ∑ j ∈ range h, fodd j := by
    rw [hSL, hs, hp, sum_odd_range]
    refine sum_congr rfl fun j _ => ?_
    simp only [fodd]; push_cast; ring_nf
  set t := ∑' i, fodd (i + h) with ht
  have htN : t < ε * π ^ 2 / 8 := hN h hhN
  have hsplit := summable_fodd.sum_add_tsum_nat_add h
  rw [← hSL'] at hsplit
  have hSLodd : ThetaSum.SLodd = SL + t := by
    show ∑' i, fodd i = SL + t
    rw [← hsplit]
  have ht0 : 0 ≤ t := tsum_nonneg fun i => by
    simp only [fodd]
    have : (0 : ℝ) ≤ Real.log (2 * ((i + h : ℕ) : ℝ) + 1) := Real.log_nonneg (by
      have : (0 : ℝ) ≤ ((i + h : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith)
    positivity
  have hH := sum_inv_odd_le p
  rw [← hs] at hH
  have hcard : (s.card : ℝ) ≤ p := by
    have : s.card ≤ p := (card_filter_le _ _).trans (card_range p).le
    exact_mod_cast this
  set M := ∑ k ∈ s, 4 * p / (π ^ 2 * k ^ 2) * (Real.log p - Real.log k + K) with hM
  have hMeq : M = 4 * p / π ^ 2 * ((Real.log p + K) * S2 - SL) := by
    rw [hM, hS2, hSL, mul_sum, ← sum_sub_distrib, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have := (hmem k hk).1
    have hk : (k : ℝ) ≠ 0 := by exact_mod_cast this.ne'
    field_simp
    ring
  -- `|Ψ - M|`
  have h1 : |Psi p - M| ≤ (2 * Real.log p + 41) * (1 + Real.log p) + (Real.log p + 12) := by
    have : Psi p - M = ∑ k ∈ s, (2 / p * (Real.cot (π * k / (2 * p)) * Ifun ((k : ℝ) / p)) -
        4 * p / (π ^ 2 * k ^ 2) * (Real.log p - Real.log k + K)) := by
      rw [Psi, mul_sum, hM, ← sum_sub_distrib]
    rw [this]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ s, |2 / p * (Real.cot (π * k / (2 * p)) * Ifun ((k : ℝ) / p)) -
          4 * p / (π ^ 2 * k ^ 2) * (Real.log p - Real.log k + K)|
        ≤ ∑ k ∈ s, (1 / k * (2 * Real.log p + 41) + 1 / p * (Real.log p + 12)) :=
          sum_le_sum fun k hk => Psi_term_K (hmem k hk).1 (hmem k hk).2
      _ = (2 * Real.log p + 41) * ∑ k ∈ s, 1 / (k : ℝ) + s.card * (1 / p * (Real.log p + 12)) := by
          rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_sum]
          congr 1; refine sum_congr rfl fun k _ => ?_; ring
      _ ≤ (2 * Real.log p + 41) * (1 + Real.log p) + p * (1 / p * (Real.log p + 12)) := by
          gcongr
      _ = (2 * Real.log p + 41) * (1 + Real.log p) + (Real.log p + 12) := by field_simp
  -- `M - (p/2) log p - c₀ p`
  have e2 : M - p / 2 * Real.log p - ThetaSum.c0 * p =
      4 * p / π ^ 2 * (Real.log p + K) * (S2 - π ^ 2 / 8) + 4 * p / π ^ 2 * t := by
    rw [hMeq, ThetaSum.c0, hSLodd]; field_simp; ring
  have h3 : |4 * p / π ^ 2 * (Real.log p + K) * (S2 - π ^ 2 / 8)| ≤ Real.log p + 1 := by
    rw [abs_mul, abs_of_pos (by positivity), abs_sub_comm, abs_of_nonneg hS2a]
    calc 4 * (p : ℝ) / π ^ 2 * (Real.log p + K) * (π ^ 2 / 8 - S2)
        ≤ 4 * (p : ℝ) / π ^ 2 * (Real.log p + 1) * (1 / (4 * h)) := by gcongr
      _ = (p : ℝ) / (π ^ 2 * h) * (Real.log p + 1) := by field_simp
      _ ≤ 1 * (Real.log p + 1) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          have h9 : 9 < π ^ 2 := by nlinarith
          have h9h : 9 * (h : ℝ) ≤ π ^ 2 * h := mul_le_mul_of_nonneg_right h9.le (by linarith)
          rw [div_le_one (by positivity), hpR']; linarith
      _ = Real.log p + 1 := one_mul _
  have h4 : 4 * p / π ^ 2 * t ≤ ε / 2 * p := by
    calc 4 * (p : ℝ) / π ^ 2 * t ≤ 4 * p / π ^ 2 * (ε * π ^ 2 / 8) :=
          mul_le_mul_of_nonneg_left htN.le (by positivity)
      _ = ε / 2 * p := by field_simp; ring
  have h5 : (2 * Real.log p + 41) * (1 + Real.log p) + (Real.log p + 12) + (Real.log p + 1) ≤
      ε / 2 * p := by
    have hl2 : Real.log p ≤ Real.log p ^ 2 := by
      rw [sq]; exact le_mul_of_one_le_right (by linarith) hlogp1
    have hl1 : 1 ≤ Real.log p ^ 2 := by linarith
    have ex : (2 * Real.log p + 41) * (1 + Real.log p) + (Real.log p + 12) + (Real.log p + 1) =
        2 * Real.log p ^ 2 + 45 * Real.log p + 54 := by ring
    have h202 : 202 / ε * Real.log p ^ 2 ≤ p := h2
    have e101 : 101 * Real.log p ^ 2 = ε / 2 * (202 / ε * Real.log p ^ 2) := by field_simp; ring
    have := mul_le_mul_of_nonneg_left h202 (show 0 ≤ ε / 2 by positivity)
    rw [ex]
    linarith
  have h4' : 0 ≤ 4 * p / π ^ 2 * t := by positivity
  calc |Psi p - p / 2 * Real.log p - ThetaSum.c0 * p|
      = |(Psi p - M) + (4 * p / π ^ 2 * (Real.log p + K) * (S2 - π ^ 2 / 8) + 4 * p / π ^ 2 * t)| := by
        rw [← e2]; ring_nf
    _ ≤ |Psi p - M| + (|4 * p / π ^ 2 * (Real.log p + K) * (S2 - π ^ 2 / 8)| + |4 * p / π ^ 2 * t|) :=
        (abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _))
    _ ≤ ((2 * Real.log p + 41) * (1 + Real.log p) + (Real.log p + 12)) + ((Real.log p + 1) + ε / 2 * p) := by
        rw [abs_of_nonneg h4']; gcongr
    _ ≤ ε * p := by linarith


/-! ### Theorem B with the constant `c₀` -/

lemma arithC' {p x L K M : ℝ} (hp : 0 < p) (hx1 : 1 ≤ x) (hL1 : 1 ≤ L) (hK : x * L ^ 4 / 2 ≤ K)
    (hM : M ≤ 9 * p * x * (L + 2) ^ 3) :
    2 / p * (2 * p / (π * K)) * M ≤ 648 * p / L := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hL4 : 1 ≤ L ^ 4 := one_le_pow₀ hL1
  have hKpos : 0 < K := by nlinarith
  have hL3 : (L + 2) ^ 3 ≤ 27 * L ^ 3 := by
    have : L + 2 ≤ 3 * L := by linarith
    have h3 : (L + 2) ^ 3 ≤ (3 * L) ^ 3 := by gcongr
    nlinarith
  have hM' : 2 / p * (2 * p / (π * K)) * M ≤ 2 / p * (2 * p / (π * K)) * (9 * p * x * (L + 2) ^ 3) :=
    mul_le_mul_of_nonneg_left hM (by positivity)
  refine hM'.trans ?_
  rw [show 2 / p * (2 * p / (π * K)) * (9 * p * x * (L + 2) ^ 3) = 36 * p * x * (L + 2) ^ 3 / (π * K) by
    field_simp; norm_num]
  rw [div_le_div_iff₀ (by positivity) (by linarith)]
  have hπK : x * L ^ 4 / 2 * 3 ≤ π * K := by nlinarith
  have h1 : 36 * p * x * (L + 2) ^ 3 * L ≤ 36 * p * x * (27 * L ^ 3) * L :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL3 (by positivity)) (by linarith)
  have h2 : 648 * p * (x * L ^ 4 / 2 * 3) ≤ 648 * p * (π * K) :=
    mul_le_mul_of_nonneg_left hπK (by positivity)
  nlinarith

lemma arithI' {p x L K : ℝ} (hp : 0 < p) (hx0 : 0 ≤ x) (hx2 : p ≤ x ^ 2) (hL1 : 1 ≤ L)
    (hK : x * L ^ 4 / 2 ≤ K) (hK0 : 0 < K) : 2 * p ^ 2 * (1 + L) / K ^ 2 ≤ 16 * p / L := by
  rw [div_le_div_iff₀ (by positivity) (by linarith)]
  have hK2' : x ^ 2 * L ^ 8 / 4 ≤ K ^ 2 := by
    have h0 : 0 ≤ x * L ^ 4 / 2 := by positivity
    have : (x * L ^ 4 / 2) ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ h0 hK 2
    nlinarith
  have h1 : p * L ^ 8 / 4 ≤ K ^ 2 := by
    have := mul_le_mul_of_nonneg_right hx2 (by positivity : (0 : ℝ) ≤ L ^ 8 / 4)
    nlinarith
  have hL8 : (1 + L) * L ≤ 2 * L ^ 8 := by
    have h2 : L ^ 2 ≤ L ^ 8 := pow_le_pow_right₀ hL1 (by norm_num)
    nlinarith
  have h3 : 2 * p ^ 2 * ((1 + L) * L) ≤ 2 * p ^ 2 * (2 * L ^ 8) :=
    mul_le_mul_of_nonneg_left hL8 (by positivity)
  have h4 : 16 * p * (p * L ^ 8 / 4) ≤ 16 * p * K ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
  nlinarith

lemma eventually_small (ε : ℝ) (hε : 0 < ε) : ∀ᶠ p : ℕ in Filter.atTop,
    Real.log p ^ 5 ≤ ε * π / 48 * (p : ℝ) ^ ((1 : ℝ) / 4) ∧ 2656 / ε ≤ Real.log p := by
  have h3 := (isLittleO_log_rpow_rpow_atTop (5 : ℝ) (by norm_num : (0 : ℝ) < 1 / 4)).bound
    (show (0 : ℝ) < ε * π / 48 by have := Real.pi_pos; positivity)
  have h4 : ∀ᶠ y : ℝ in Filter.atTop, 2656 / ε ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  have h : ∀ᶠ y : ℝ in Filter.atTop, Real.log y ^ 5 ≤ ε * π / 48 * y ^ ((1 : ℝ) / 4) ∧
      2656 / ε ≤ Real.log y := by
    filter_upwards [h3, h4, Filter.eventually_ge_atTop (3 : ℝ)] with y hy3 hy4 hy1
    refine ⟨?_, hy4⟩
    have hl : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hl _), Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _),
      show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hy3
    exact hy3
  exact tendsto_natCast_atTop_atTop.eventually h

set_option maxHeartbeats 1000000 in
/-- **Theorem B(ii) with the constant `c₀`** (Kloosterman cut-off `K = p^{3/4}(log p)^4`):
`S(p) = (p/2) log p + c₀ p + (4p/π) R_K(p) + o(p)`. -/
theorem HB34_c0 (hK : HK34) : ∀ ε > 0, ∀ᶠ p : ℕ in Filter.atTop, p.Prime →
    |(S p : ℝ) - p / 2 * Real.log p - ThetaSum.c0 * p -
      4 * p / π * ∑ k ∈ (Ico 3 (KW34 p)).filter Odd, Fsum k p / (k : ℝ) ^ 2| ≤ ε * p := by
  intro ε hε
  have hψ := Psi_asymp (ε / 4) (by positivity)
  have hsm := eventually_small ε hε
  filter_upwards [eventually_facts, hψ, hsm] with p hfacts hψp hsmp hp
  obtain ⟨hsm5, hLε⟩ := hsmp
  obtain ⟨hp3, hx6, hlog⟩ := hfacts
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  have hpR : (0 : ℝ) < p := by linarith
  have hp3n : 3 ≤ p := by exact_mod_cast hp3
  have hp2 : p ≠ 2 := by omega
  set L := Real.log p with hLdef
  set x := (p : ℝ) ^ ((3 : ℝ) / 4) with hxdef
  have hL1 : 1 ≤ L := by
    have : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9; linarith
    have := Real.log_le_log (by norm_num) hp3
    linarith
  have hxq : x * (p : ℝ) ^ ((1 : ℝ) / 4) = p := by
    rw [hxdef, ← Real.rpow_add hpR]; norm_num
  have hx1 : 1 ≤ x := by linarith
  have hx2 : (p : ℝ) ≤ x ^ 2 := by
    have e : x ^ 2 = (p : ℝ) ^ ((3 : ℝ) / 2) := by
      rw [hxdef, sq, ← Real.rpow_add hpR]; norm_num
    rw [e]
    calc (p : ℝ) = (p : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (p : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  set y := x * L ^ 4 with hydef
  have hL4 : 1 ≤ L ^ 4 := one_le_pow₀ hL1
  have hy6 : 6 ≤ y := by nlinarith
  have hmain : 12 / π * x * L ^ 5 ≤ p := by
    have h1 : x * L ^ 5 ≤ x * (π / 12 * (p : ℝ) ^ ((1 : ℝ) / 4)) := by gcongr
    have h2 : x * (π / 12 * (p : ℝ) ^ ((1 : ℝ) / 4)) = π / 12 * p := by
      calc x * (π / 12 * (p : ℝ) ^ ((1 : ℝ) / 4)) = π / 12 * (x * (p : ℝ) ^ ((1 : ℝ) / 4)) := by ring
        _ = π / 12 * p := by rw [hxq]
    have h3 : 12 / π * x * L ^ 5 = 12 / π * (x * L ^ 5) := by ring
    rw [h3]
    calc 12 / π * (x * L ^ 5) ≤ 12 / π * (π / 12 * p) :=
          mul_le_mul_of_nonneg_left (h1.trans h2.le) (by positivity)
      _ = p := by field_simp
  have hsmall : 4 / π * (L + 2) * y ≤ p := by
    have : 4 / π * (L + 2) * y ≤ 12 / π * x * L ^ 5 := by
      rw [hydef]
      have h4 : 4 / π * (L + 2) ≤ 12 / π * L := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hpi]; linarith
      calc 4 / π * (L + 2) * (x * L ^ 4) ≤ 12 / π * L * (x * L ^ 4) := by gcongr
        _ = 12 / π * x * L ^ 5 := by ring
    linarith
  have hylt : y < p := by
    have h4 : 1 < 4 / π * (L + 2) := by
      rw [div_mul_eq_mul_div, one_lt_div hpi]; linarith
    have hy0 : 0 < y := by linarith
    nlinarith
  set K := KW34 p with hKdef
  have hKy : (K : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hyK : y < K + 1 := Nat.lt_floor_add_one y
  have hK3 : 3 ≤ K := by
    have : (5 : ℝ) < K := by linarith
    have : 5 < K := by exact_mod_cast this
    omega
  have hKp : K < p := by
    have : (K : ℝ) < p := by linarith
    exact_mod_cast this
  have hK2 : y / 2 ≤ K := by linarith
  have hKR : (3 : ℝ) ≤ K := by exact_mod_cast hK3
  -- the pieces
  have hS := S_eq_Psi_Phi hp hp2
  have hΦ := Phi_split hp hp2 hKp.le
  set Φs := 2 * ∑ k ∈ (range K).filter Odd, Real.cot (π * k / (2 * p)) * Fsum k p / k with hΦs
  set T := 4 * p / π * ∑ k ∈ (Ico 3 K).filter Odd, Fsum k p / (k : ℝ) ^ 2 with hT
  set Cpart := 2 / p * ∑ k ∈ (Ico K p).filter Odd, Real.cot (π * k / (2 * p)) * Cp p k with hCpart
  set Ipart := 2 / p * ∑ k ∈ (Ico K p).filter Odd, Real.cot (π * k / (2 * p)) * Ifun ((k : ℝ) / p)
    with hIpart
  have e : (S p : ℝ) - p / 2 * L - ThetaSum.c0 * p - T =
      (Psi p - p / 2 * L - ThetaSum.c0 * p) + (Φs - T) + Cpart - Ipart := by rw [hS, hΦ]; ring
  rw [e]
  have b1 : |Psi p - p / 2 * L - ThetaSum.c0 * p| ≤ ε / 4 * p := hψp (hp.odd_of_ne_two hp2)
  have hsmall' : 4 / π * (L + 2) * y ≤ ε / 4 * p := by
    have h1 : x * L ^ 5 ≤ x * (ε * π / 48 * (p : ℝ) ^ ((1 : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_left hsm5 (by linarith)
    have h2 : x * (ε * π / 48 * (p : ℝ) ^ ((1 : ℝ) / 4)) = ε * π / 48 * p := by
      calc x * (ε * π / 48 * (p : ℝ) ^ ((1 : ℝ) / 4)) = ε * π / 48 * (x * (p : ℝ) ^ ((1 : ℝ) / 4)) := by ring
        _ = ε * π / 48 * p := by rw [hxq]
    have h4 : 4 / π * (L + 2) ≤ 12 / π * L := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hpi]; linarith
    calc 4 / π * (L + 2) * y = 4 / π * (L + 2) * (x * L ^ 4) := by rw [hydef]
      _ ≤ 12 / π * L * (x * L ^ 4) := by gcongr
      _ = 12 / π * (x * L ^ 5) := by ring
      _ ≤ 12 / π * (ε * π / 48 * p) := mul_le_mul_of_nonneg_left (h1.trans h2.le) (by positivity)
      _ = ε / 4 * p := by field_simp; ring
  have b2 : |Φs - T| ≤ ε / 4 * p := by
    have := small_part hp hKp.le
    have h' : 4 / π * (L + 2) * K ≤ 4 / π * (L + 2) * y := by gcongr
    linarith
  have hLpos : 0 < L := by linarith
  have b3 : |Cpart| ≤ 648 * p / L := by
    have hC := large_C hK hp hp2 (by omega) hKp
    have hMb := arithM hpR hx1 (by linarith) (Cp_one_nonneg p) (Cp_one_le (hp.odd_of_ne_two hp2))
    exact hC.trans (arithC' hpR hx1 hL1 (by rw [← hydef]; exact hK2) hMb)
  have b4 : |Ipart| ≤ 16 * p / L :=
    (large_I hp (K := K) (by omega)).trans
      (arithI' hpR (by linarith) hx2 hL1 (by rw [← hydef]; exact hK2) (by linarith))
  have b34 : 648 * p / L + 16 * p / L ≤ ε / 4 * p := by
    rw [← add_div, div_le_iff₀ hLpos]
    have := mul_le_mul_of_nonneg_left hLε (show (0 : ℝ) ≤ ε / 4 * p by positivity)
    have e3 : ε / 4 * p * (2656 / ε) = 664 * p := by field_simp; ring
    linarith
  calc |Psi p - p / 2 * L - ThetaSum.c0 * p + (Φs - T) + Cpart - Ipart|
      ≤ |Psi p - p / 2 * L - ThetaSum.c0 * p| + |Φs - T| + |Cpart| + |Ipart| := by
        have h1 := abs_sub (Psi p - p / 2 * L - ThetaSum.c0 * p + (Φs - T) + Cpart) Ipart
        have h2 := abs_add_le (Psi p - p / 2 * L - ThetaSum.c0 * p + (Φs - T)) Cpart
        have h3 := abs_add_le (Psi p - p / 2 * L - ThetaSum.c0 * p) (Φs - T)
        linarith
    _ ≤ ε / 4 * p + ε / 4 * p + (648 * p / L + 16 * p / L) := by linarith
    _ ≤ ε * p := by nlinarith


end TheoremB

namespace ThetaSum

/-- **Theorem B(ii) with the explicit constant** `c₀ = K₀/2 - (4/π²) ∑_{k odd} log k/k²`,
`K₀ = γ + log(4/π)`, cut-off `K = KW34 p` (unconditional; Kloosterman's bound is proved):
`S(p) = (p/2) log p + c₀ p + (4p/π) R_K(p) + o(p)`. -/
theorem theorem_B_c0 : ∀ ε > 0, ∀ᶠ p : ℕ in Filter.atTop, p.Prime →
    |(S p : ℝ) - p / 2 * Real.log p - c0 * p - 4 * p / Real.pi * RsumK (KW34 p) p| ≤ ε * p := by
  intro ε hε
  filter_upwards [TheoremB.HB34_c0 (HK34_bridge.mp hK34) ε hε] with p hp hpr
  have := hp hpr
  simp only [S_bridge, KW34_bridge, Fsum_bridge] at this
  exact this

/-- Theorem C with `c = c₀`, conditional on (HBGfull). (Cosmetic: the error term dominates `p`,
so any `c` works here; the content is in `theorem_B_c0` and `TheoremB.Psi_asymp`.) -/
theorem theorem_C_c0 (hBGfull : HBGfull) : ∀ γ₀ : ℝ, 0 < γ₀ → γ₀ < 2 / 3 → ∃ C : ℝ,
    ∀ᶠ p : ℕ in Filter.atTop, p.Prime →
      |(S p : ℝ) - p / 2 * Real.log p - c0 * p| ≤
        C * p * Real.log p ^ (2 / 3 + γ₀) * Real.log (Real.log p) ^ (8 / 3 : ℝ) := by
  intro γ₀ hγ hγ1
  obtain ⟨C₂, hC₂, hR⟩ := R_thmC hBGfull hγ hγ1
  refine ⟨1 + 4 / Real.pi * C₂, ?_⟩
  filter_upwards [hR, theorem_B_c0 1 one_pos] with p hRp hBp hp
  obtain ⟨h1, h2⟩ := hRp hp
  have hB' := hBp hp
  set W := Real.log p ^ (2 / 3 + γ₀) * Real.log (Real.log p) ^ (8 / 3 : ℝ)
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hpi := Real.pi_pos
  set X := (S p : ℝ) - p / 2 * Real.log p - c0 * p
  set Y := 4 * (p : ℝ) / Real.pi * RsumK (KW34 p) p
  have hY : |Y| ≤ 4 * p / Real.pi * (C₂ * W) := by
    simp only [Y]
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have htri : |X| ≤ |X - Y| + |Y| := by
    have := abs_sub_le X Y 0
    simpa only [sub_zero] using this
  have hC0 : 1 * p ≤ 1 * p * W := le_mul_of_one_le_right (by positivity) h1
  calc |X| ≤ |X - Y| + |Y| := htri
    _ ≤ 1 * p * W + 4 * p / Real.pi * (C₂ * W) := by linarith
    _ = (1 + 4 / Real.pi * C₂) * p * W := by ring
    _ = _ := by simp only [W]; ring

/-- Theorem C\* with `c = c₀`, conditional on (HBGfull). (Cosmetic, as for `theorem_C_c0`.) -/
theorem theorem_C_star_c0 (hBGfull : HBGfull) : ∃ C : ℝ,
    ∀ᶠ p : ℕ in Filter.atTop, p.Prime →
      |(S p : ℝ) - p / 2 * Real.log p - c0 * p| ≤
        C * p * Real.log p ^ (2 / 3 : ℝ) * Real.log (Real.log p) ^ (17 / 3 : ℝ) := by
  obtain ⟨C₂, hC₂, hR⟩ := R_thmCstar hBGfull
  refine ⟨1 + 4 / Real.pi * C₂, ?_⟩
  filter_upwards [hR, theorem_B_c0 1 one_pos] with p hRp hBp hp
  obtain ⟨h1, h2⟩ := hRp hp
  have hB' := hBp hp
  set W := Real.log p ^ (2 / 3 : ℝ) * Real.log (Real.log p) ^ (17 / 3 : ℝ)
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hpi := Real.pi_pos
  set X := (S p : ℝ) - p / 2 * Real.log p - c0 * p
  set Y := 4 * (p : ℝ) / Real.pi * RsumK (KW34 p) p
  have hY : |Y| ≤ 4 * p / Real.pi * (C₂ * W) := by
    simp only [Y]
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have htri : |X| ≤ |X - Y| + |Y| := by
    have := abs_sub_le X Y 0
    simpa only [sub_zero] using this
  have hC0 : 1 * p ≤ 1 * p * W := le_mul_of_one_le_right (by positivity) h1
  calc |X| ≤ |X - Y| + |Y| := htri
    _ ≤ 1 * p * W + 4 * p / Real.pi * (C₂ * W) := by linarith
    _ = (1 + 4 / Real.pi * C₂) * p * W := by ring
    _ = _ := by simp only [W]; ring

end ThetaSum

#print axioms TheoremB.I_asymp_K0
#print axioms TheoremB.Psi_asymp
#print axioms ThetaSum.theorem_B_c0
#print axioms ThetaSum.theorem_C_c0
#print axioms ThetaSum.theorem_C_star_c0
