import Upper.Tangent

/-!
# Lemma 4.1 of `theta_sum_v3.pdf`: the reciprocity law for half-range cotangent sums

For coprime odd positive `m, k`:  `C_m(k) = (m/k) F_k(m) + I(k/m)`, where
`I(λ) = (1/π) ∫_0^∞ (cosh v - cosh λv)/(sinh v sinh λv) dv`.

The proof avoids contour integration. Ingredients:
1. `integral_Jint`: `∫_0^∞ (e^{-xt} - e^{-(1-x)t})/(1-e^{-t}) dt = π cot(πx)` (`0<x<1`), from the
   geometric series, termwise integration and Mathlib's Mittag-Leffler expansion of `cot`.
2. `Dpoly_eq_zero`: the polynomial identity
   `(1-X^{2k}) A_{m,k} - (1-X^{2m}) A_{k,m} = X^k - X^m - X^{m+2k} + X^{k+2m}`,
   `A_{m,k} = Σ_{0<a<m odd} (X^{⟨ka⟩_{2m}} - X^{2m-⟨ka⟩_{2m}})`, proved by evaluating at all
   `2m`-th and `2k`-th roots of unity (geometric sums), a degree count and a palindromy argument.
3. With `q = e^{-v/m}` the integrand of `I(k/m)` equals
   `2(A_{m,k}(q)/(1-q^{2m}) - A_{k,m}(q)/(1-q^{2k}))`; integrating termwise with 1. gives
   `π (C_m(k) - (m/k) C_k(m))`, and `C_k(m) = F_k(m)` (Lemma 4.4, `Cp_eq_Fsum`).
-/
namespace Recip
section Analytic
open Real Set MeasureTheory Filter Topology

/-- Mittag-Leffler in the form `Σ_{n≥0} (1/(x+n) - 1/(1-x+n)) = π cot(π x)` for `0 < x < 1`. -/
lemma hasSum_cot (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    HasSum (fun n : ℕ => 1 / (x + n) - 1 / (1 - x + n)) (π * Real.cot (π * x)) := by
  have hxZ : (x : ℂ) ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨n, hn⟩
    have : (n : ℝ) = x := by exact_mod_cast hn
    have h1 : (0 : ℝ) < n := this ▸ hx0
    have h2 : (n : ℝ) < 1 := this ▸ hx1
    have h1' : 0 < n := by exact_mod_cast h1
    have h2' : n < 1 := by exact_mod_cast h2
    omega
  have hd := (summable_cotTerm hxZ).hasSum
  rw [← cot_series_rep' hxZ] at hd
  -- real version of `hd`
  have hdR : HasSum (fun n : ℕ => 1 / (x - (n + 1)) + 1 / (x + (n + 1)))
      (π * Real.cot (π * x) - 1 / x) := by
    rw [← Complex.hasSum_ofReal]
    convert hd using 1
    · ext n; simp [cotTerm]
    · push_cast; rfl
  have he : HasSum (fun n : ℕ => 1 / (x + n) - 1 / (x + (n + 1))) (1 / x) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg]
    · have : ∀ N : ℕ, ∑ i ∈ Finset.range N, (1 / (x + i) - 1 / (x + (i + 1))) = 1 / x - 1 / (x + N) := by
        intro N
        induction N with
        | zero => simp
        | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
      simp_rw [this]
      have : Tendsto (fun N : ℕ => 1 / (x + N)) atTop (𝓝 0) := by
        apply Tendsto.div_atTop tendsto_const_nhds
        exact tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
      simpa using (tendsto_const_nhds (x := 1 / x)).sub this
    · intro n
      have h1 : 0 < x + n := by positivity
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le h1 (by linarith)
  convert hdR.add he using 1
  · ext n
    have h1 : x + n ≠ 0 := by positivity
    have h2 : 1 - x + n ≠ 0 := by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
    have h3 : x - (n + 1) ≠ 0 := by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
    have h4 : x + (n + 1) ≠ 0 := by positivity
    field_simp
    ring
  · ring

/-- The integrand `(e^{-xt} - e^{-(1-x)t})/(1 - e^{-t})`. -/
noncomputable def Jint (x t : ℝ) : ℝ := (exp (-(x * t)) - exp (-((1 - x) * t))) / (1 - exp (-t))

noncomputable def gt (x : ℝ) (n : ℕ) (t : ℝ) : ℝ := exp (-((x + n) * t)) - exp (-((1 - x + n) * t))

lemma hasSum_gt (x : ℝ) {t : ℝ} (ht : 0 < t) : HasSum (fun n => gt x n t) (Jint x t) := by
  have h0 : 0 ≤ exp (-t) := (exp_pos _).le
  have h1 : exp (-t) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have := (hasSum_geometric_of_lt_one h0 h1).mul_left (exp (-(x * t)) - exp (-((1 - x) * t)))
  convert this using 1
  · ext n
    unfold gt
    rw [← Real.exp_nat_mul]
    rw [sub_mul, ← Real.exp_add, ← Real.exp_add]
    congr 2 <;> ring
  · unfold Jint; rw [div_eq_mul_inv]

lemma integral_exp_neg_mul {c : ℝ} (hc : 0 < c) : ∫ t in Ioi (0 : ℝ), exp (-(c * t)) = 1 / c := by
  have := integral_exp_mul_Ioi (a := -c) (by linarith) 0
  simp only [neg_mul, mul_zero, exp_zero] at this
  rw [this]; field_simp

lemma integrableOn_exp_neg_mul {c : ℝ} (hc : 0 < c) : IntegrableOn (fun t => exp (-(c * t))) (Ioi 0) := by
  have := integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0
  simpa only [neg_mul] using this

lemma integrable_gt {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (n : ℕ) :
    IntegrableOn (gt x n) (Ioi 0) := by
  have h1 : 0 < x + n := by positivity
  have h2 : 0 < 1 - x + n := by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
  exact (integrableOn_exp_neg_mul h1).sub (integrableOn_exp_neg_mul h2)

lemma integral_gt {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), gt x n t = 1 / (x + n) - 1 / (1 - x + n) := by
  have h1 : 0 < x + n := by positivity
  have h2 : 0 < 1 - x + n := by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
  unfold gt
  rw [integral_sub (integrableOn_exp_neg_mul h1) (integrableOn_exp_neg_mul h2),
    integral_exp_neg_mul h1, integral_exp_neg_mul h2]

lemma integral_norm_gt {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), ‖gt x n t‖ = |1 / (x + n) - 1 / (1 - x + n)| := by
  rcases le_or_gt x (1 / 2) with hx | hx
  · have hnn : ∀ t ∈ Ioi (0 : ℝ), ‖gt x n t‖ = gt x n t := by
      intro t ht
      apply Real.norm_of_nonneg
      unfold gt; rw [sub_nonneg, exp_le_exp]
      have : (0 : ℝ) < t := ht
      nlinarith
    rw [setIntegral_congr_fun measurableSet_Ioi hnn, integral_gt hx0 hx1, abs_of_nonneg]
    have h1 : 0 < x + n := by positivity
    rw [sub_nonneg]; apply one_div_le_one_div_of_le h1; linarith
  · have hnn : ∀ t ∈ Ioi (0 : ℝ), ‖gt x n t‖ = -gt x n t := by
      intro t ht
      rw [Real.norm_of_nonpos]
      unfold gt; rw [sub_nonpos, exp_le_exp]
      have : (0 : ℝ) < t := ht
      nlinarith
    rw [setIntegral_congr_fun measurableSet_Ioi hnn, integral_neg, integral_gt hx0 hx1,
      abs_of_nonpos]
    have h2 : 0 < 1 - x + n := by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
    rw [sub_nonpos]; apply one_div_le_one_div_of_le h2; linarith

lemma summable_integral_norm_gt {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Summable (fun n : ℕ => ∫ t in Ioi (0 : ℝ), ‖gt x n t‖) := by
  simp_rw [integral_norm_gt hx0 hx1]
  exact (hasSum_cot x hx0 hx1).summable.abs

lemma measurable_Jint (x : ℝ) : Measurable (Jint x) := by
  unfold Jint; fun_prop

lemma integrableOn_Jint {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : IntegrableOn (Jint x) (Ioi 0) := by
  refine ⟨(measurable_Jint x).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hg := fun n => integrable_gt hx0 hx1 n
  calc ∫⁻ t in Ioi (0 : ℝ), ‖Jint x t‖ₑ = ∫⁻ t in Ioi (0 : ℝ), ‖∑' n, gt x n t‖ₑ := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro t ht; simp only; rw [(hasSum_gt x ht).tsum_eq]
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), ∑' n, ‖gt x n t‖ₑ := lintegral_mono fun t => enorm_tsum_le_tsum_enorm
    _ = ∑' n, ∫⁻ t in Ioi (0 : ℝ), ‖gt x n t‖ₑ :=
        lintegral_tsum fun n => (hg n).aestronglyMeasurable.aemeasurable.enorm
    _ = ∑' n, ENNReal.ofReal (∫ t in Ioi (0 : ℝ), ‖gt x n t‖) := by
        congr 1; ext n; rw [ofReal_integral_norm_eq_lintegral_enorm (hg n)]
    _ < ⊤ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg fun t => norm_nonneg _)
          (summable_integral_norm_gt hx0 hx1)]
        exact ENNReal.ofReal_lt_top

/-- `∫_0^∞ (e^{-xt} - e^{-(1-x)t})/(1 - e^{-t}) dt = π cot(π x)` for `0 < x < 1`. -/
theorem integral_Jint {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ∫ t in Ioi (0 : ℝ), Jint x t = π * Real.cot (π * x) := by
  have h := integral_tsum_of_summable_integral_norm (μ := volume.restrict (Ioi (0 : ℝ)))
    (fun n => integrable_gt hx0 hx1 n) (summable_integral_norm_gt hx0 hx1)
  have h2 : ∫ t in Ioi (0 : ℝ), ∑' n, gt x n t = ∫ t in Ioi (0 : ℝ), Jint x t :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht => (hasSum_gt x ht).tsum_eq
  rw [← h2, ← h]
  simp_rw [integral_gt hx0 hx1]
  exact (hasSum_cot x hx0 hx1).tsum_eq

end Analytic

section Poly
open Polynomial Finset

/-- `A_{m,k}(q) = Σ_{0<a<m, a odd} (q^{⟨ka⟩} - q^{2m-⟨ka⟩})`, `⟨·⟩` = residue mod `2m`. -/
noncomputable def Apoly (m k : ℕ) : ℂ[X] :=
  ∑ a ∈ (range m).filter Odd, (X ^ ((k * a) % (2 * m)) - X ^ (2 * m - (k * a) % (2 * m)))

noncomputable def Ppoly (m k : ℕ) : ℂ[X] := X ^ k - X ^ m - X ^ (m + 2 * k) + X ^ (k + 2 * m)

noncomputable def Dpoly (m k : ℕ) : ℂ[X] :=
  (1 - X ^ (2 * k)) * Apoly m k - (1 - X ^ (2 * m)) * Apoly k m - Ppoly m k

lemma eval_Apoly (m k : ℕ) (z : ℂ) : (Apoly m k).eval z =
    ∑ a ∈ (range m).filter Odd, (z ^ ((k * a) % (2 * m)) - z ^ (2 * m - (k * a) % (2 * m))) := by
  simp [Apoly, eval_finsetSum]

lemma sum_odd_range' {M : Type*} [AddCommMonoid M] (h : ℕ) (f : ℕ → M) :
    ∑ k ∈ (range (2 * h + 1)).filter Odd, f k = ∑ x ∈ range h, f (2 * x + 1) := by
  symm
  rw [← sum_image (s := range h) (g := fun x => 2 * x + 1) (by intro x _ y _ hxy; simp at hxy; omega)]
  congr 1
  ext k; simp only [mem_image, mem_range, mem_filter]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨by omega, ⟨x, rfl⟩⟩
  · rintro ⟨hk, ⟨x, rfl⟩⟩; exact ⟨x, by omega, rfl⟩

lemma telescope (z : ℂ) (h : ℕ) : (1 - z ^ 2) * ∑ j ∈ range h, z ^ (2 * j + 1) = z - z ^ (2 * h + 1) := by
  induction h with
  | zero => simp
  | succ h ih => rw [sum_range_succ, mul_add, ih]; ring

/-- Evaluation at a `2m`-th root of unity. -/
lemma root_identity {m k : ℕ} (hm : Odd m) (hk : Odd k) {ζ : ℂ} (hζ : ζ ^ (2 * m) = 1) :
    (1 - ζ ^ (2 * k)) * (Apoly m k).eval ζ = ζ ^ k - ζ ^ m - ζ ^ (m + 2 * k) + ζ ^ (k + 2 * m) := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl; rw [zero_pow (by have := hm.pos; omega)] at hζ; exact zero_ne_one hζ
  have hm0 : 0 < 2 * m := by have := hm.pos; omega
  set x := ζ ^ k with hx
  have hx0 : x ≠ 0 := pow_ne_zero _ hζ0
  have e1 : ∀ a, ζ ^ ((k * a) % (2 * m)) = x ^ a := by
    intro a
    rw [hx, ← pow_mul]
    conv_rhs => rw [← Nat.mod_add_div (k * a) (2 * m), pow_add, pow_mul, hζ, one_pow, mul_one]
  have e2 : ∀ a, ζ ^ (2 * m - (k * a) % (2 * m)) = (x⁻¹) ^ a := by
    intro a
    rw [inv_pow, ← e1]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_add, Nat.sub_add_cancel (Nat.mod_lt _ hm0).le, hζ]
  rw [eval_Apoly, show ζ ^ (2 * k) = x ^ 2 by rw [hx, ← pow_mul, mul_comm]]
  simp_rw [e1, e2]
  obtain ⟨h, rfl⟩ := hm
  rw [sum_odd_range', sum_sub_distrib, mul_sub, telescope]
  have hy : (1 - x ^ 2) * ∑ j ∈ range h, x⁻¹ ^ (2 * j + 1) =
      -x ^ 2 * (x⁻¹ - x⁻¹ ^ (2 * h + 1)) := by
    rw [← telescope, ← mul_assoc]; congr 1; field_simp; ring
  rw [hy]
  set e := ζ ^ (2 * h + 1) with he
  have he2 : e ^ 2 = 1 := by rw [he, ← pow_mul, mul_comm]; exact hζ
  have hek : e ^ k = e := by
    obtain ⟨c, rfl⟩ := hk
    rw [pow_succ, pow_mul, he2, one_pow, one_mul]
  have hxm : x ^ (2 * h + 1) = e := by rw [hx, ← pow_mul, mul_comm, pow_mul, ← he, hek]
  have hxmi : x⁻¹ ^ (2 * h + 1) = e := by
    rw [inv_pow, hxm]
    have : e * e = 1 := by rw [← sq, he2]
    exact inv_eq_of_mul_eq_one_right this
  have p1 : ζ ^ (2 * h + 1 + 2 * k) = e * x ^ 2 := by
    rw [pow_add, ← he, hx, ← pow_mul, mul_comm k 2]
  have p2 : ζ ^ (k + 2 * (2 * h + 1)) = x := by rw [pow_add, hζ, mul_one]
  rw [hxm, hxmi, p1, p2]
  field_simp
  ring

lemma eval_Dpoly (m k : ℕ) (z : ℂ) : (Dpoly m k).eval z =
    (1 - z ^ (2 * k)) * (Apoly m k).eval z - (1 - z ^ (2 * m)) * (Apoly k m).eval z -
      (z ^ k - z ^ m - z ^ (m + 2 * k) + z ^ (k + 2 * m)) := by
  simp [Dpoly, Ppoly]

lemma Dpoly_root_m {m k : ℕ} (hm : Odd m) (hk : Odd k) {ζ : ℂ} (hζ : ζ ^ (2 * m) = 1) :
    (Dpoly m k).eval ζ = 0 := by
  rw [eval_Dpoly, root_identity hm hk hζ, hζ]; ring

lemma Dpoly_root_k {m k : ℕ} (hm : Odd m) (hk : Odd k) {ζ : ℂ} (hζ : ζ ^ (2 * k) = 1) :
    (Dpoly m k).eval ζ = 0 := by
  rw [eval_Dpoly, root_identity hk hm hζ, hζ]; ring

lemma Apoly_eval_zero {m k : ℕ} (hk : Odd k) : (Apoly m k).eval 0 = 0 := by
  rw [eval_Apoly]
  apply sum_eq_zero
  intro a ha
  simp only [mem_filter, mem_range] at ha
  have hka : Odd (k * a) := hk.mul ha.2
  have hr : (k * a) % (2 * m) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd _ (dvd_mul_right 2 m)]; exact Nat.odd_iff.1 hka
  have hlt : (k * a) % (2 * m) < 2 * m := Nat.mod_lt _ (by omega)
  rw [zero_pow (by omega), zero_pow (by omega), sub_zero]

lemma Dpoly_eval_zero {m k : ℕ} (hm : Odd m) (hk : Odd k) : (Dpoly m k).eval 0 = 0 := by
  have := hm.pos; have := hk.pos
  rw [eval_Dpoly, Apoly_eval_zero hk, Apoly_eval_zero hm]
  simp [zero_pow (show k ≠ 0 by omega), zero_pow (show m ≠ 0 by omega),
    zero_pow (show k + 2 * m ≠ 0 by omega), zero_pow (show m + 2 * k ≠ 0 by omega)]

lemma mono_inv {q : ℂ} (hq : q ≠ 0) (a b : ℕ) : q⁻¹ ^ a * q ^ (a + b) = q ^ b := by
  rw [pow_add, ← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hq), one_mul]

lemma Apoly_inv {m k : ℕ} {q : ℂ} (hq : q ≠ 0) :
    (Apoly m k).eval q⁻¹ * q ^ (2 * m) = -(Apoly m k).eval q := by
  rw [eval_Apoly, eval_Apoly, sum_mul, ← sum_neg_distrib]
  refine sum_congr rfl fun a ha => ?_
  simp only [mem_filter, mem_range] at ha
  have hlt : (k * a) % (2 * m) < 2 * m := Nat.mod_lt _ (by omega)
  set r := (k * a) % (2 * m)
  rw [sub_mul]
  have e1 : q⁻¹ ^ r * q ^ (2 * m) = q ^ (2 * m - r) := by
    have := mono_inv hq r (2 * m - r); rwa [Nat.add_sub_cancel' hlt.le] at this
  have e2 : q⁻¹ ^ (2 * m - r) * q ^ (2 * m) = q ^ r := by
    have := mono_inv hq (2 * m - r) r; rwa [Nat.sub_add_cancel hlt.le] at this
  rw [e1, e2]; ring

lemma Dpoly_palin {m k : ℕ} {q : ℂ} (hq : q ≠ 0) :
    (Dpoly m k).eval q⁻¹ * q ^ (2 * m + 2 * k) = (Dpoly m k).eval q := by
  have hAm := Apoly_inv (m := m) (k := k) hq
  have hAk := Apoly_inv (m := k) (k := m) hq
  rw [eval_Dpoly, eval_Dpoly]
  have i1 : (1 - q⁻¹ ^ (2 * k)) * q ^ (2 * k) = -(1 - q ^ (2 * k)) := by
    rw [sub_mul, one_mul, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hq)]; ring
  have i2 : (1 - q⁻¹ ^ (2 * m)) * q ^ (2 * m) = -(1 - q ^ (2 * m)) := by
    rw [sub_mul, one_mul, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hq)]; ring
  have j1 : q⁻¹ ^ k * q ^ (2 * m + 2 * k) = q ^ (k + 2 * m) := by
    rw [show 2 * m + 2 * k = k + (k + 2 * m) by ring, mono_inv hq]
  have j2 : q⁻¹ ^ m * q ^ (2 * m + 2 * k) = q ^ (m + 2 * k) := by
    rw [show 2 * m + 2 * k = m + (m + 2 * k) by ring, mono_inv hq]
  have j3 : q⁻¹ ^ (m + 2 * k) * q ^ (2 * m + 2 * k) = q ^ m := by
    rw [show 2 * m + 2 * k = (m + 2 * k) + m by ring, mono_inv hq]
  have j4 : q⁻¹ ^ (k + 2 * m) * q ^ (2 * m + 2 * k) = q ^ k := by
    rw [show 2 * m + 2 * k = (k + 2 * m) + k by ring, mono_inv hq]
  have hsplit : q ^ (2 * m + 2 * k) = q ^ (2 * k) * q ^ (2 * m) := by rw [pow_add, mul_comm]
  calc ((1 - q⁻¹ ^ (2 * k)) * (Apoly m k).eval q⁻¹ - (1 - q⁻¹ ^ (2 * m)) * (Apoly k m).eval q⁻¹ -
        (q⁻¹ ^ k - q⁻¹ ^ m - q⁻¹ ^ (m + 2 * k) + q⁻¹ ^ (k + 2 * m))) * q ^ (2 * m + 2 * k)
      = ((1 - q⁻¹ ^ (2 * k)) * q ^ (2 * k)) * ((Apoly m k).eval q⁻¹ * q ^ (2 * m)) -
        ((1 - q⁻¹ ^ (2 * m)) * q ^ (2 * m)) * ((Apoly k m).eval q⁻¹ * q ^ (2 * k)) -
        (q⁻¹ ^ k * q ^ (2 * m + 2 * k) - q⁻¹ ^ m * q ^ (2 * m + 2 * k) -
          q⁻¹ ^ (m + 2 * k) * q ^ (2 * m + 2 * k) + q⁻¹ ^ (k + 2 * m) * q ^ (2 * m + 2 * k)) := by
        rw [hsplit]; ring
    _ = _ := by rw [i1, i2, hAm, hAk, j1, j2, j3, j4]; ring

lemma Apoly_natDegree {m k : ℕ} (hm : 0 < m) (hk : Odd k) : (Apoly m k).natDegree ≤ 2 * m - 1 := by
  unfold Apoly
  apply natDegree_sum_le_of_forall_le
  intro a ha
  simp only [mem_filter, mem_range] at ha
  have hka : Odd (k * a) := hk.mul ha.2
  have hr : (k * a) % (2 * m) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd _ (dvd_mul_right 2 m)]; exact Nat.odd_iff.1 hka
  have hlt : (k * a) % (2 * m) < 2 * m := Nat.mod_lt _ (by omega)
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · rw [natDegree_X_pow]; omega
  · rw [natDegree_X_pow]; omega

lemma Dpoly_natDegree {m k : ℕ} (hm : Odd m) (hk : Odd k) :
    (Dpoly m k).natDegree ≤ 2 * m + 2 * k - 1 := by
  have hm0 := hm.pos; have hk0 := hk.pos
  have h1 : (1 - X ^ (2 * k) : ℂ[X]).natDegree ≤ 2 * k :=
    (natDegree_sub_le _ _).trans (max_le (by simp) (by rw [natDegree_X_pow]))
  have h2 : (1 - X ^ (2 * m) : ℂ[X]).natDegree ≤ 2 * m :=
    (natDegree_sub_le _ _).trans (max_le (by simp) (by rw [natDegree_X_pow]))
  unfold Dpoly Ppoly
  refine (natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le ?_ ?_)) ?_)
  · exact natDegree_mul_le.trans (by have := Apoly_natDegree hm0 hk; omega)
  · exact natDegree_mul_le.trans (by have := Apoly_natDegree hk0 hm; omega)
  · refine (natDegree_add_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le
      ((natDegree_sub_le _ _).trans (max_le ?_ ?_)) ?_)) ?_) <;> rw [natDegree_X_pow] <;> omega

/-- The auxiliary polynomial `L = (Σ_{j<m} X^{2j}) (X^{2k} - 1)`. -/
noncomputable def Lpoly (m k : ℕ) : ℂ[X] := (∑ j ∈ range m, X ^ (2 * j)) * (X ^ (2 * k) - 1)

lemma Lpoly_mul (m k : ℕ) : Lpoly m k * (X ^ 2 - 1) = (X ^ (2 * m) - 1) * (X ^ (2 * k) - 1) := by
  unfold Lpoly
  have : (∑ j ∈ range m, (X : ℂ[X]) ^ (2 * j)) * (X ^ 2 - 1) = X ^ (2 * m) - 1 := by
    have := geom_sum_mul ((X : ℂ[X]) ^ 2) m
    simp_rw [← pow_mul] at this
    rw [show 2 * m = m * 2 by ring]; convert this using 2
    ext1 j; rw [mul_comm]
  rw [mul_right_comm, this]

lemma Lpoly_monic_natDegree {m k : ℕ} (hm : 0 < m) (hk : 0 < k) :
    (Lpoly m k).Monic ∧ (Lpoly m k).natDegree = 2 * m + 2 * k - 2 := by
  have mon : ∀ n : ℕ, 0 < n → ((X : ℂ[X]) ^ n - 1).Monic := fun n hn => by
    simpa using monic_X_pow_sub_C (1 : ℂ) (n := n) (by omega)
  have hX2 := mon 2 (by norm_num)
  have hprod : ((X ^ (2 * m) - 1) * (X ^ (2 * k) - 1) : ℂ[X]).Monic :=
    (mon _ (by omega)).mul (mon _ (by omega))
  rw [← Lpoly_mul] at hprod
  have hmon : (Lpoly m k).Monic := hX2.of_mul_monic_right hprod
  refine ⟨hmon, ?_⟩
  have nd : ∀ n : ℕ, ((X : ℂ[X]) ^ n - 1).natDegree = n := fun n => by
    simpa using natDegree_X_pow_sub_C (R := ℂ) (n := n) (r := 1)
  have h1 := congrArg natDegree (Lpoly_mul m k)
  rw [hmon.natDegree_mul hX2, (mon _ (by omega : 0 < 2 * m)).natDegree_mul
    (mon _ (by omega : 0 < 2 * k)), nd, nd, nd] at h1
  omega

lemma Lpoly_eval_root {m k : ℕ} {z : ℂ} (hz : z ^ (2 * m) = 1 ∨ z ^ (2 * k) = 1) :
    (Lpoly m k).eval z = 0 := by
  rcases hz with hz | hz
  · by_cases h2 : z ^ 2 = 1
    · unfold Lpoly; simp [pow_mul, h2]
    · have := congrArg (eval z) (Lpoly_mul m k)
      simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_one, hz, sub_self, zero_mul] at this
      exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 h2)
  · unfold Lpoly; simp [hz]

lemma card_Z {m k : ℕ} (hm : 0 < m) (hk : 0 < k) (hcop : Nat.Coprime m k) :
    (nthRootsFinset (2 * m) (1 : ℂ) ∪ nthRootsFinset (2 * k) (1 : ℂ)).card = 2 * m + 2 * k - 2 := by
  have hA := (Complex.isPrimitiveRoot_exp (2 * m) (by omega)).card_nthRootsFinset
  have hB := (Complex.isPrimitiveRoot_exp (2 * k) (by omega)).card_nthRootsFinset
  have hC := (Complex.isPrimitiveRoot_exp 2 (by omega)).card_nthRootsFinset
  have hinter : nthRootsFinset (2 * m) (1 : ℂ) ∩ nthRootsFinset (2 * k) (1 : ℂ) =
      nthRootsFinset 2 (1 : ℂ) := by
    ext z
    rw [mem_inter, mem_nthRootsFinset (by omega), mem_nthRootsFinset (by omega),
      mem_nthRootsFinset (by omega), ← pow_gcd_eq_one, Nat.gcd_mul_left, hcop, mul_one]
  have := card_union_add_card_inter (nthRootsFinset (2 * m) (1 : ℂ)) (nthRootsFinset (2 * k) (1 : ℂ))
  rw [hinter, hA, hB, hC] at this
  omega

/-- **The polynomial reciprocity identity**: for coprime odd `m, k`,
`(1 - X^{2k}) A_{m,k} - (1 - X^{2m}) A_{k,m} = X^k - X^m - X^{m+2k} + X^{k+2m}`. -/
theorem Dpoly_eq_zero {m k : ℕ} (hm : Odd m) (hk : Odd k) (hcop : Nat.Coprime m k) :
    Dpoly m k = 0 := by
  have hm0 := hm.pos; have hk0 := hk.pos
  set N := 2 * m + 2 * k - 2 with hN
  obtain ⟨D1, hD1⟩ : X ∣ Dpoly m k := X_dvd_iff.2 (by
    rw [coeff_zero_eq_eval_zero]; exact Dpoly_eval_zero hm hk)
  have hdeg1 : D1.natDegree ≤ N := by
    by_cases h0 : D1 = 0
    · rw [h0]; simp
    · have := Dpoly_natDegree hm hk
      rw [hD1, natDegree_X_mul h0] at this
      omega
  set Z := nthRootsFinset (2 * m) (1 : ℂ) ∪ nthRootsFinset (2 * k) (1 : ℂ) with hZ
  have hZroot : ∀ z ∈ Z, z ^ (2 * m) = 1 ∨ z ^ (2 * k) = 1 := by
    intro z hz
    rw [hZ, mem_union, mem_nthRootsFinset (by omega), mem_nthRootsFinset (by omega)] at hz
    exact hz
  have hD1Z : ∀ z ∈ Z, D1.eval z = 0 := by
    intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      rcases hZroot 0 hz with h | h <;> rw [zero_pow (by omega)] at h <;> exact zero_ne_one h
    have hDz : (Dpoly m k).eval z = 0 := by
      rcases hZroot z hz with h | h
      · exact Dpoly_root_m hm hk h
      · exact Dpoly_root_k hm hk h
    rw [hD1, eval_mul, eval_X] at hDz
    exact (mul_eq_zero.1 hDz).resolve_left hz0
  obtain ⟨hLmon, hLdeg⟩ := Lpoly_monic_natDegree (m := m) (k := k) hm0 hk0
  set c := D1.coeff N with hc
  set p := D1 - C c * Lpoly m k with hp
  have hpZ : ∀ z ∈ Z, p.eval z = 0 := by
    intro z hz
    rw [hp, eval_sub, eval_mul, eval_C, hD1Z z hz, Lpoly_eval_root (hZroot z hz)]; ring
  have hpcoeff : ∀ i, N ≤ i → p.coeff i = 0 := by
    intro i hi
    rw [hp, coeff_sub, coeff_C_mul]
    rcases hi.lt_or_eq with h | h
    · rw [coeff_eq_zero_of_natDegree_lt (hdeg1.trans_lt h),
        coeff_eq_zero_of_natDegree_lt (hLdeg ▸ h)]; ring
    · have h1 : (Lpoly m k).coeff N = 1 := by rw [hN, ← hLdeg]; exact hLmon.coeff_natDegree
      rw [← h, hc, h1]; ring
  have hp0 : p = 0 := by
    by_contra hne
    have hdeg : p.natDegree < N := by
      rw [natDegree_lt_iff_degree_lt hne, degree_lt_iff_coeff_zero]
      intro i hi; exact hpcoeff i hi
    apply hne
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero p (f := fun z : Z => (z : ℂ))
      Subtype.val_injective (fun z => hpZ z z.2)
    rw [Fintype.card_coe, hZ, card_Z hm0 hk0 hcop]; exact hdeg
  have hD1eq : D1 = C c * Lpoly m k := by rw [← sub_eq_zero]; exact hp0
  -- palindrome at `q = 2` forces `c = 0`
  have hpal := Dpoly_palin (m := m) (k := k) (q := (2 : ℂ)) two_ne_zero
  rw [hD1, hD1eq] at hpal
  simp only [eval_mul, eval_X, eval_C] at hpal
  have hL2 := congrArg (eval (2 : ℂ)) (Lpoly_mul m k)
  have hLh := congrArg (eval (2⁻¹ : ℂ)) (Lpoly_mul m k)
  simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_one] at hL2 hLh
  set a := (Lpoly m k).eval 2
  set b := (Lpoly m k).eval 2⁻¹
  have hu : (2 : ℂ) ^ (2 * m + 2 * k) = 2 ^ (2 * m) * 2 ^ (2 * k) := pow_add _ _ _
  have hu1 : (2⁻¹ : ℂ) ^ (2 * m) * 2 ^ (2 * m) = 1 := by rw [inv_pow, inv_mul_cancel₀ (by simp)]
  have hu2 : (2⁻¹ : ℂ) ^ (2 * k) * 2 ^ (2 * k) = 1 := by rw [inv_pow, inv_mul_cancel₀ (by simp)]
  set U := (2 : ℂ) ^ (2 * m); set W := (2 : ℂ) ^ (2 * k)
  set U' := (2⁻¹ : ℂ) ^ (2 * m); set W' := (2⁻¹ : ℂ) ^ (2 * k)
  have hU : U ≠ 1 := by
    rw [show U = ((2 ^ (2 * m) : ℕ) : ℂ) by push_cast; rfl]
    norm_cast
    exact (Nat.one_lt_pow (by omega) (by norm_num)).ne'
  have hW : W ≠ 1 := by
    rw [show W = ((2 ^ (2 * k) : ℕ) : ℂ) by push_cast; rfl]
    norm_cast
    exact (Nat.one_lt_pow (by omega) (by norm_num)).ne'
  have ha : a ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hL2
    rcases mul_eq_zero.1 hL2.symm with h | h
    · exact hU (sub_eq_zero.1 h)
    · exact hW (sub_eq_zero.1 h)
  have hcz : c = 0 := by
    have hU0 : U ≠ 0 := by simp [U]
    have hW0 : W ≠ 0 := by simp [W]
    have hU' : U' = U⁻¹ := by simp [U, U', inv_pow]
    have hW' : W' = W⁻¹ := by simp [W, W', inv_pow]
    rw [hU', hW'] at hLh
    rw [hu] at hpal
    have h4 : (2⁻¹ : ℂ) ^ 2 = 4⁻¹ := by norm_num
    rw [h4] at hLh
    -- from hLh: b = -4 a / (U W)
    have hb : b = -4 * a / (U * W) := by
      have e : b * (4⁻¹ - 1) * (U * W) = (1 - U) * (1 - W) := by
        rw [hLh]; field_simp
      have e2 : a * (2 ^ 2 - 1) = (U - 1) * (W - 1) := hL2
      rw [eq_div_iff (mul_ne_zero hU0 hW0)]
      linear_combination (-4/3 : ℂ) * e + (4/3 : ℂ) * e2
    rw [hb] at hpal
    field_simp at hpal
    linear_combination (-1/8 : ℂ) * hpal
  rw [hD1, hD1eq, hcz]; simp

end Poly


section Main
open Real MeasureTheory
open Arxiv.«2501.03234»

/-- The integrand of `I(λ)`. -/
noncomputable def Iint (l v : ℝ) : ℝ :=
  (Real.cosh v - Real.cosh (l * v)) / (Real.sinh v * Real.sinh (l * v))

/-- `I(λ) = (1/π) ∫_0^∞ (cosh v - cosh λv)/(sinh v sinh λv) dv`. -/
noncomputable def Ifun (l : ℝ) : ℝ := 1 / π * ∫ v in Set.Ioi (0 : ℝ), Iint l v

/-- Real form of `A_{m,k}`. -/
noncomputable def Areal (m k : ℕ) (q : ℝ) : ℝ :=
  ∑ a ∈ (Finset.range m).filter Odd, (q ^ ((k * a) % (2 * m)) - q ^ (2 * m - (k * a) % (2 * m)))

lemma Areal_identity {m k : ℕ} (hm : Odd m) (hk : Odd k) (hcop : Nat.Coprime m k) (q : ℝ) :
    (1 - q ^ (2 * k)) * Areal m k q - (1 - q ^ (2 * m)) * Areal k m q =
      q ^ k - q ^ m - q ^ (m + 2 * k) + q ^ (k + 2 * m) := by
  apply Complex.ofReal_injective
  have := congrArg (Polynomial.eval (q : ℂ)) (Dpoly_eq_zero hm hk hcop)
  rw [eval_Dpoly, eval_Apoly, eval_Apoly, Polynomial.eval_zero] at this
  unfold Areal
  push_cast
  linear_combination this

/-- One summand: `(e^{-r s v} - e^{-(2m-r) s v})/(1 - e^{-2m s v})`. -/
noncomputable def term (m r : ℕ) (s v : ℝ) : ℝ :=
  (exp (-((r : ℝ) * s * v)) - exp (-(((2 * m - r : ℕ) : ℝ) * s * v))) / (1 - exp (-(2 * m * s * v)))

lemma term_eq_Jint {m r : ℕ} (hm : 0 < m) (hr : r < 2 * m) (s v : ℝ) :
    term m r s v = Jint ((r : ℝ) / (2 * m)) ((2 * m * s) * v) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold term Jint
  rw [Nat.cast_sub hr.le]
  push_cast
  congr 3 <;> field_simp

lemma term_integral {m r : ℕ} (hm : 0 < m) (hr0 : 0 < r) (hr : r < 2 * m) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (term m r s) (Set.Ioi 0) ∧
      ∫ v in Set.Ioi (0 : ℝ), term m r s v = π * Real.cot (π * ((r : ℝ) / (2 * m))) / (2 * m * s) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hx0 : 0 < (r : ℝ) / (2 * m) := by
    have : (0 : ℝ) < r := by exact_mod_cast hr0
    positivity
  have hx1 : (r : ℝ) / (2 * m) < 1 := by
    rw [div_lt_one (by positivity)]; exact_mod_cast hr
  have hb : 0 < 2 * m * s := by positivity
  have heq : term m r s = fun v => Jint ((r : ℝ) / (2 * m)) ((2 * m * s) * v) :=
    funext fun v => term_eq_Jint hm hr s v
  rw [heq]
  constructor
  · rw [integrableOn_Ioi_comp_mul_left_iff _ 0 hb, mul_zero]
    exact integrableOn_Jint hx0 hx1
  · rw [integral_comp_mul_left_Ioi _ 0 hb, mul_zero, integral_Jint hx0 hx1, smul_eq_mul]
    field_simp

/-- `Σ_a term`. -/
noncomputable def Ahat (m k : ℕ) (s v : ℝ) : ℝ :=
  ∑ a ∈ (Finset.range m).filter Odd, term m ((k * a) % (2 * m)) s v

lemma residue_facts {m k a : ℕ} (hm : 0 < m) (hk : Odd k) (ha : Odd a) :
    0 < (k * a) % (2 * m) ∧ (k * a) % (2 * m) < 2 * m := by
  have hka : Odd (k * a) := hk.mul ha
  have hr : (k * a) % (2 * m) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd _ (dvd_mul_right 2 m)]; exact Nat.odd_iff.1 hka
  exact ⟨by omega, Nat.mod_lt _ (by omega)⟩

lemma Ahat_integral {m k : ℕ} (hm : 0 < m) (hk : Odd k) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (Ahat m k s) (Set.Ioi 0) ∧
      ∫ v in Set.Ioi (0 : ℝ), Ahat m k s v = π / (2 * m * s) * Cp m k := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hint : ∀ a ∈ (Finset.range m).filter Odd, IntegrableOn (term m ((k * a) % (2 * m)) s) (Set.Ioi 0) := by
    intro a ha
    simp only [Finset.mem_filter] at ha
    obtain ⟨h1, h2⟩ := residue_facts hm hk ha.2
    exact (term_integral hm h1 h2 hs).1
  have hfun : Ahat m k s = fun v => ∑ a ∈ (Finset.range m).filter Odd, term m ((k * a) % (2 * m)) s v :=
    rfl
  constructor
  · rw [hfun]; exact integrable_finsetSum _ hint
  · rw [hfun, integral_finsetSum _ hint, Cp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    simp only [Finset.mem_filter] at ha
    obtain ⟨h1, h2⟩ := residue_facts hm hk ha.2
    rw [(term_integral hm h1 h2 hs).2]
    -- cot periodicity: `k a = r + 2m q`
    have hdiv : ((k : ℝ) * a) = ((k * a) % (2 * m) : ℕ) + 2 * m * ((k * a / (2 * m) : ℕ) : ℝ) := by
      have h := congrArg (Nat.cast (R := ℝ)) (Nat.mod_add_div (k * a) (2 * m)).symm
      push_cast at h
      exact h
    rw [show π * (k : ℝ) * a / (2 * m) = π * (((k * a) % (2 * m) : ℕ) / (2 * m)) +
      ((k * a / (2 * m) : ℕ) : ℝ) * π by rw [mul_assoc, hdiv]; field_simp, cot_add_nat_mul_pi]
    field_simp

lemma Iint_eq {m k : ℕ} (hm : Odd m) (hk : Odd k) (hcop : Nat.Coprime m k) {v : ℝ} (hv : 0 < v) :
    Iint ((k : ℝ) / m) v = 2 * (Ahat m k (1 / m) v - Ahat k m (1 / m) v) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.pos
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk.pos
  set q := exp (-(v / m)) with hq
  have hpow : ∀ n : ℕ, exp (-((n : ℝ) * (1 / m) * v)) = q ^ n := by
    intro n; rw [hq, ← Real.exp_nat_mul]; congr 1; ring
  have hden : ∀ n : ℕ, exp (-(2 * (n : ℝ) * (1 / m) * v)) = q ^ (2 * n) := by
    intro n; have := hpow (2 * n); push_cast at this; exact this
  have hA : ∀ (M K : ℕ), Ahat M K (1 / m) v = Areal M K q / (1 - q ^ (2 * M)) := by
    intro M K
    unfold Ahat Areal term
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hpow, hpow, hden, sub_div]
  rw [hA, hA]
  have hid := Areal_identity hm hk hcop q
  set A1 := Areal m k q
  set A2 := Areal k m q
  set a := q ^ m with ha
  set b := q ^ k with hb
  have hav : exp (-v) = a := by
    rw [ha, ← hpow m]; congr 1; field_simp
  have hbv : exp (-((k : ℝ) / m * v)) = b := by
    rw [hb, ← hpow k]; congr 1; field_simp
  have ha0 : 0 < a := hav ▸ exp_pos _
  have hb0 : 0 < b := hbv ▸ exp_pos _
  have ha1 : a < 1 := by rw [← hav, Real.exp_lt_one_iff]; linarith
  have hb1 : b < 1 := by rw [← hbv, Real.exp_lt_one_iff]; have : 0 < (k : ℝ) / m * v := by positivity
                         linarith
  have e2m : q ^ (2 * m) = a ^ 2 := by rw [ha, ← pow_mul, mul_comm]
  have e2k : q ^ (2 * k) = b ^ 2 := by rw [hb, ← pow_mul, mul_comm]
  have e3 : q ^ (m + 2 * k) = a * b ^ 2 := by rw [pow_add, e2k]
  have e4 : q ^ (k + 2 * m) = b * a ^ 2 := by rw [pow_add, e2m]
  rw [e2m, e2k, e3, e4] at hid
  rw [e2m, e2k]
  unfold Iint
  rw [Real.cosh_eq, Real.cosh_eq, Real.sinh_eq, Real.sinh_eq, hav, hbv,
    show exp v = a⁻¹ by rw [← hav, Real.exp_neg, inv_inv],
    show exp ((k : ℝ) / m * v) = b⁻¹ by rw [← hbv, Real.exp_neg, inv_inv]]
  have h1 : 1 - a ^ 2 ≠ 0 := by nlinarith
  have h2 : 1 - b ^ 2 ≠ 0 := by nlinarith
  have h3 : a⁻¹ - a ≠ 0 := by
    rw [sub_ne_zero]; intro h
    have : a * a⁻¹ = a * a := by rw [h]
    rw [mul_inv_cancel₀ ha0.ne'] at this; nlinarith
  have h4 : b⁻¹ - b ≠ 0 := by
    rw [sub_ne_zero]; intro h
    have : b * b⁻¹ = b * b := by rw [h]
    rw [mul_inv_cancel₀ hb0.ne'] at this; nlinarith
  clear_value a b A1 A2
  field_simp
  linear_combination (-1 : ℝ) * hid

/-- **Lemma 4.1 (reciprocity)** of `theta_sum_v3.pdf`: for coprime odd positive `m, k`,
`C_m(k) = (m/k) F_k(m) + I(k/m)`. -/
theorem reciprocity {m k : ℕ} (hm : Odd m) (hk : Odd k) (hcop : Nat.Coprime m k) :
    Cp m k = (m : ℝ) / k * Fsum k m + Ifun ((k : ℝ) / m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.pos
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk.pos
  have hs : (0 : ℝ) < 1 / m := by positivity
  obtain ⟨i1, e1⟩ := Ahat_integral (m := m) (k := k) hm.pos hk hs
  obtain ⟨i2, e2⟩ := Ahat_integral (m := k) (k := m) hk.pos hm hs
  have hI : ∫ v in Set.Ioi (0 : ℝ), Iint ((k : ℝ) / m) v =
      ∫ v in Set.Ioi (0 : ℝ), 2 * (Ahat m k (1 / m) v - Ahat k m (1 / m) v) :=
    setIntegral_congr_fun measurableSet_Ioi fun v hv => Iint_eq hm hk hcop hv
  unfold Ifun
  rw [hI, integral_const_mul, integral_sub i1 i2, e1, e2, ← Cp_eq_Fsum hk hm]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- `I(1/λ) = -λ I(λ)` for `λ > 0`. -/
theorem Ifun_inv {l : ℝ} (hl : 0 < l) : Ifun (1 / l) = -l * Ifun l := by
  unfold Ifun
  have h := integral_comp_mul_left_Ioi (Iint (1 / l)) 0 hl
  rw [mul_zero, smul_eq_mul] at h
  have hg : ∀ x, Iint (1 / l) (l * x) = -Iint l x := by
    intro x
    unfold Iint
    rw [show 1 / l * (l * x) = x by field_simp]
    rw [neg_div', mul_comm (Real.sinh (l * x))]
    congr 1; ring
  simp_rw [hg, integral_neg] at h
  have hl' : l ≠ 0 := hl.ne'
  have : ∫ v in Set.Ioi (0 : ℝ), Iint (1 / l) v = -l * ∫ v in Set.Ioi (0 : ℝ), Iint l v := by
    have h2 : l * (l⁻¹ * ∫ x in Set.Ioi (0 : ℝ), Iint (1 / l) x) =
        ∫ x in Set.Ioi (0 : ℝ), Iint (1 / l) x := by field_simp
    rw [← h2, ← h]; ring
  rw [this]; ring

lemma Iint_formula {l v : ℝ} (hl : 0 < l) (hv : 0 < v) :
    Iint l v = 2 * (exp (-(l * v)) - exp (-v)) * (1 - exp (-v) * exp (-(l * v))) /
      ((1 - exp (-v) ^ 2) * (1 - exp (-(l * v)) ^ 2)) := by
  set a := exp (-v) with ha
  set b := exp (-(l * v)) with hb
  have ha0 : 0 < a := exp_pos _
  have hb0 : 0 < b := exp_pos _
  have ha1 : a < 1 := by rw [ha, Real.exp_lt_one_iff]; linarith
  have hb1 : b < 1 := by rw [hb, Real.exp_lt_one_iff]; have := mul_pos hl hv; linarith
  unfold Iint
  rw [Real.cosh_eq, Real.cosh_eq, Real.sinh_eq, Real.sinh_eq, ← ha, ← hb,
    show exp v = a⁻¹ by rw [ha, Real.exp_neg, inv_inv],
    show exp (l * v) = b⁻¹ by rw [hb, Real.exp_neg, inv_inv]]
  have h1 : 1 - a ^ 2 ≠ 0 := by nlinarith
  have h2 : 1 - b ^ 2 ≠ 0 := by nlinarith
  have h3 : a⁻¹ - a ≠ 0 := by
    rw [sub_ne_zero]; intro h
    have : a * a⁻¹ = a * a := by rw [h]
    rw [mul_inv_cancel₀ ha0.ne'] at this; nlinarith
  have h4 : b⁻¹ - b ≠ 0 := by
    rw [sub_ne_zero]; intro h
    have : b * b⁻¹ = b * b := by rw [h]
    rw [mul_inv_cancel₀ hb0.ne'] at this; nlinarith
  clear_value a b
  field_simp
  ring

lemma Iint_pos_bound {l v : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (hv : 0 < v) :
    0 < Iint l v ∧ Iint l v ≤ 2 * (1 + (1 - l) / l) * exp (-(l * v)) := by
  rw [Iint_formula hl0 hv]
  set a := exp (-v) with ha
  set b := exp (-(l * v)) with hb
  have ha0 : 0 < a := exp_pos _
  have hb0 : 0 < b := exp_pos _
  have ha1 : a < 1 := by rw [ha, Real.exp_lt_one_iff]; linarith
  have hb1 : b < 1 := by rw [hb, Real.exp_lt_one_iff]; have := mul_pos hl0 hv; linarith
  have hab : a < b := by rw [ha, hb, Real.exp_lt_exp]; nlinarith
  have hden : 0 < (1 - a ^ 2) * (1 - b ^ 2) := by
    apply mul_pos <;> nlinarith
  constructor
  · apply div_pos _ hden
    apply mul_pos (by linarith)
    nlinarith
  · -- key estimate: `b - a ≤ (1 + p)(1 - b) b` with `p = (1-l)/l`
    set p := (1 - l) / l with hp
    have hp0 : 0 ≤ p := by rw [hp]; apply div_nonneg <;> linarith
    have hkey : 1 - exp (-((1 - l) * v)) ≤ (1 + p) * (1 - b) := by
      rcases le_or_gt (1 - l) l with h | h
      · have : exp (-(l * v)) ≤ exp (-((1 - l) * v)) := by rw [Real.exp_le_exp]; nlinarith
        nlinarith
      · have hp1 : 1 ≤ p := by rw [hp, le_div_iff₀ hl0]; linarith
        have hs : -1 ≤ b - 1 := by linarith
        have hbern := one_add_mul_self_le_rpow_one_add hs hp1
        rw [show 1 + (b - 1) = b by ring, hb, ← Real.exp_mul] at hbern
        have : -(l * v) * p = -((1 - l) * v) := by rw [hp]; field_simp
        rw [this] at hbern
        nlinarith
    have hba : b - a = b * (1 - exp (-((1 - l) * v))) := by
      rw [mul_sub, mul_one, hb, ← Real.exp_add, ha]; congr 2; ring
    have h1 : 2 * (b - a) * (1 - a * b) / ((1 - a ^ 2) * (1 - b ^ 2)) ≤ 2 * (b - a) / (1 - b) := by
      rw [div_le_div_iff₀ hden (by linarith)]
      have hba0 : 0 ≤ b - a := by linarith
      have hq : 0 ≤ b * (1 + a - a ^ 2) - a ^ 2 := by nlinarith
      have : (1 - a * b) * (1 - b) ≤ (1 - a ^ 2) * (1 - b ^ 2) := by
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - b) hq]
      nlinarith
    refine h1.trans ?_
    rw [div_le_iff₀ (by linarith), hba]
    nlinarith

lemma integrableOn_Iint {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) : IntegrableOn (Iint l) (Set.Ioi 0) := by
  have hbound : IntegrableOn (fun v => 2 * (1 + (1 - l) / l) * exp (-(l * v))) (Set.Ioi 0) :=
    (integrableOn_exp_neg_mul hl0).const_mul _
  refine hbound.mono' ?_ ?_
  · exact (by unfold Iint; fun_prop : Measurable (Iint l)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    obtain ⟨h1, h2⟩ := Iint_pos_bound hl0 hl1 hv
    rw [Real.norm_of_nonneg h1.le]; exact h2

/-- `I(λ) > 0` for `0 < λ < 1`. -/
theorem Ifun_pos {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) : 0 < Ifun l := by
  unfold Ifun
  apply mul_pos (by positivity)
  rw [setIntegral_pos_iff_support_of_nonneg_ae _ (integrableOn_Iint hl0 hl1)]
  · have : Function.support (Iint l) ∩ Set.Ioi 0 = Set.Ioi 0 := by
      ext v
      simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_Ioi, and_iff_right_iff_imp]
      intro hv; exact (Iint_pos_bound hl0 hl1 hv).1.ne'
    rw [this]; simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact (Iint_pos_bound hl0 hl1 hv).1.le

end Main

end Recip

#print axioms Recip.integral_Jint
#print axioms Recip.Dpoly_eq_zero
#print axioms Recip.reciprocity
#print axioms Recip.Ifun_inv
#print axioms Recip.Ifun_pos
