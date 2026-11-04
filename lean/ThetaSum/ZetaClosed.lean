import ThetaSum.ConstantC0

/-!
# Closed form of `c₀`

`∑_{k odd} log k / k² = -(log 2/4) ζ(2) - (3/4) ζ'(2)`, hence
`c₀ = K₀/2 + log 2 / 6 + (3/π²) ζ'(2)`.
Route: `ζ'(2) = -∑ log n / n²` (`LSeries_deriv` for `L 1 = ζ` on `re s > 1`), and the
even/odd split `∑ log(2j)/(2j)² = (log 2/4) ζ(2) + (1/4) ∑ log n / n²`.
-/

open Filter

namespace ThetaSum

/-- `∑_{n ≥ 1} log n / n²` (the `n = 0` term is `0`). -/
noncomputable def Lall : ℝ := ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2

lemma summable_logsq : Summable fun n : ℕ => Real.log n / (n : ℝ) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => TheoremB.log_div_sq_le k)
    ((Real.summable_nat_rpow_inv.2 (by norm_num : (1 : ℝ) < 3 / 2)).mul_left 2)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
    positivity

/-- `ζ'(2) = -∑ log n / n²`. -/
theorem deriv_zeta_two : deriv riemannZeta 2 = -((Lall : ℝ) : ℂ) := by
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : riemannZeta =ᶠ[nhds (2 : ℂ)] LSeries 1 := by
    filter_upwards [hopen.mem_nhds (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by simp)] with s hs
    exact (LSeries_one_eq_riemannZeta hs).symm
  rw [hev.deriv_eq, LSeries_deriv (by
    norm_num [LSeries.abscissaOfAbsConv_one]; exact_mod_cast (show (1 : ℝ) < 2 by norm_num))]
  congr 1
  rw [Lall, Complex.ofReal_tsum]
  show ∑' n, LSeries.term (LSeries.logMul 1) 2 n = _
  congr 1; ext n
  rw [LSeries.term_def]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, Complex.cpow_ofNat]
    simp only [LSeries.logMul, Pi.one_apply, mul_one]
    rw [Complex.ofReal_div, Complex.ofReal_log (Nat.cast_nonneg n)]
    push_cast; rfl

/-- `∑_{k odd} log k/k² = (3/4) ∑ log n/n² - (log 2/4) ζ(2)`. -/
lemma SLodd_eq : SLodd = 3 / 4 * Lall - Real.log 2 / 4 * (Real.pi ^ 2 / 6) := by
  set g : ℕ → ℝ := fun n => Real.log n / (n : ℝ) ^ 2 with hg
  have hz : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2) (Real.pi ^ 2 / 6) := hasSum_zeta_two
  have he : HasSum (fun j => g (2 * j)) (Real.log 2 / 4 * (Real.pi ^ 2 / 6) + 1 / 4 * Lall) := by
    have := (hz.mul_left (Real.log 2 / 4)).add (summable_logsq.hasSum.mul_left (1 / 4))
    convert this using 1
    ext j
    simp only [hg]
    rcases eq_or_ne j 0 with rfl | hj
    · simp
    · have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast hj
      push_cast
      rw [Real.log_mul (by norm_num) hjR]
      field_simp
      ring
    rfl
  have ho : Summable fun j => g (2 * j + 1) :=
    summable_logsq.comp_injective (fun a b h => by simpa using h)
  have htot := tsum_even_add_odd he.summable ho
  rw [he.tsum_eq] at htot
  have hodd : SLodd = ∑' j, g (2 * j + 1) := by
    rw [SLodd]; congr 1; ext j; simp only [hg]; push_cast; ring_nf
  have hall : ∑' n, g n = Lall := rfl
  rw [hall] at htot
  rw [hodd]
  linarith

/-- **`∑_{k odd} log k / k² = -(log 2/4) ζ(2) - (3/4) ζ'(2)`.** -/
theorem SLodd_closed_form :
    SLodd = -(Real.log 2 / 4) * (riemannZeta 2).re - 3 / 4 * (deriv riemannZeta 2).re := by
  have h1 : (riemannZeta 2).re = Real.pi ^ 2 / 6 := by
    rw [riemannZeta_two, show (Real.pi : ℂ) ^ 2 / 6 = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) by push_cast; rfl,
      Complex.ofReal_re]
  have h2 : (deriv riemannZeta 2).re = -Lall := by
    rw [deriv_zeta_two, Complex.neg_re, Complex.ofReal_re]
  rw [h1, h2, SLodd_eq]
  ring

/-- **The closed form of `c₀`**: `c₀ = K₀/2 + log 2/6 + (3/π²) ζ'(2)`, `K₀ = γ + log(4/π)`. -/
theorem c0_closed_form :
    c0 = Kzero / 2 + Real.log 2 / 6 + 3 / Real.pi ^ 2 * (deriv riemannZeta 2).re := by
  have h2 : (deriv riemannZeta 2).re = -Lall := by
    rw [deriv_zeta_two, Complex.neg_re, Complex.ofReal_re]
  have hpi := Real.pi_pos
  rw [c0, SLodd_eq, h2]
  field_simp
  ring

end ThetaSum

#print axioms ThetaSum.SLodd_closed_form
#print axioms ThetaSum.c0_closed_form
