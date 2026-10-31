import Upper.Reciprocity

/-!
# Theorem B of `theta_sum_v3.pdf` (weak form)

* `S_eq_Psi_Phi` — Theorem B(i): `S(p) = Ψ(p) + Φ(p)`.
* `I_asymp` — `|πλ I(λ) - log(1/λ)| ≤ 12` for `0 < λ ≤ 1` (weak Lemma 4.2/Cor. 4.3(c)), via
  monotonicity of `I`, `I(1/m) = C_m(1)` and two-sided bounds for `C_m(1)`.
* `Psi_bound` — `Ψ(p) = (p/2) log p + O(p)`.
* `weil_kbar`, `sum_Cp_interval` — Lemmas 5.2, 5.3, for any uniform Kloosterman bound
  (`KlBound`); `KlBound_of_HK34`, `KlBound_of_HW` supply it from `HK34` resp. `HW`.
* `HBweak34_of_HK34` — Theorem B(ii) with cut-off `K = p^{3/4}(log p)^4` and error `O(p)`.
-/

namespace TheoremB
section Analytic
open Real Finset
open Arxiv.«2501.03234» Recip

/-- `Ψ(p) = (2/p) Σ_{0<k<p odd} cot(πk/2p) I(k/p)`. -/
noncomputable def Psi (p : ℕ) : ℝ :=
  2 / p * ∑ k ∈ (range p).filter Odd, Real.cot (π * k / (2 * p)) * Ifun ((k : ℝ) / p)

/-- `Φ(p) = 2 Σ_{0<k<p odd} cot(πk/2p) F_k(p)/k`. -/
noncomputable def Phi (p : ℕ) : ℝ :=
  2 * ∑ k ∈ (range p).filter Odd, Real.cot (π * k / (2 * p)) * Fsum k p / k

lemma coprime_of_lt {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) : Nat.Coprime p k :=
  (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => absurd (Nat.le_of_dvd hk0 h) (by omega)

/-- **Theorem B(i)**: `S(p) = Ψ(p) + Φ(p)` for odd primes `p`. -/
theorem S_eq_Psi_Phi {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (S p : ℝ) = Psi p + Phi p := by
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  rw [S_dual hp hp2, Psi, Phi, mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun k hk => ?_
  simp only [mem_filter, mem_range] at hk
  have hk0 : 0 < k := hk.2.pos
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
  rw [reciprocity hpo hk.2 (coprime_of_lt hp hk0 hk.1)]
  field_simp
  ring

/-! ### Bounds for `I(λ)` -/

lemma Iint_anti {l1 l2 v : ℝ} (h1 : 0 < l1) (h12 : l1 ≤ l2) (h2 : l2 ≤ 1) (hv : 0 < v) :
    Iint l2 v ≤ Iint l1 v := by
  rw [Iint_formula (h1.trans_le h12) hv, Iint_formula h1 hv]
  set a := exp (-v) with ha
  set b1 := exp (-(l1 * v)) with hb1
  set b2 := exp (-(l2 * v)) with hb2
  have ha0 : 0 < a := exp_pos _
  have ha1 : a < 1 := by rw [ha, Real.exp_lt_one_iff]; linarith
  have hb1' : b1 < 1 := by rw [hb1, Real.exp_lt_one_iff]; have := mul_pos h1 hv; linarith
  have hab2 : a ≤ b2 := by rw [ha, hb2, Real.exp_le_exp]; nlinarith
  have hb21 : b2 ≤ b1 := by rw [hb1, hb2, Real.exp_le_exp]; nlinarith
  have hd1 : 0 < (1 - a ^ 2) * (1 - b1 ^ 2) := by apply mul_pos <;> nlinarith
  have hd2 : 0 < (1 - a ^ 2) * (1 - b2 ^ 2) := by apply mul_pos <;> nlinarith
  rw [div_le_div_iff₀ hd2 hd1]
  have key : (b1 - a) * (1 - a * b1) * (1 - b2 ^ 2) - (b2 - a) * (1 - a * b2) * (1 - b1 ^ 2) =
      (b1 - b2) * ((1 - a * b1) * (1 - a * b2) + (b1 - a) * (b2 - a)) := by ring
  have hpos : 0 ≤ (b1 - b2) * ((1 - a * b1) * (1 - a * b2) + (b1 - a) * (b2 - a)) := by
    apply mul_nonneg (by linarith)
    apply add_nonneg
    · apply mul_nonneg <;> nlinarith
    · apply mul_nonneg <;> linarith
  have h1a : 0 ≤ 1 - a ^ 2 := by nlinarith
  nlinarith [mul_nonneg (mul_nonneg h1a (by norm_num : (0:ℝ) ≤ 2)) hpos]

lemma Ifun_one : Ifun 1 = 0 := by
  unfold Ifun Iint; simp

lemma Ifun_nonneg {l : ℝ} (h0 : 0 < l) (h1 : l ≤ 1) : 0 ≤ Ifun l := by
  rcases h1.lt_or_eq with h | h
  · exact (Ifun_pos h0 h).le
  · rw [h, Ifun_one]

lemma Ifun_anti {l1 l2 : ℝ} (h1 : 0 < l1) (h12 : l1 ≤ l2) (h2 : l2 ≤ 1) : Ifun l2 ≤ Ifun l1 := by
  rcases h2.lt_or_eq with h2' | h2'
  · unfold Ifun
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply MeasureTheory.setIntegral_mono_on (integrableOn_Iint (h1.trans_le h12) h2')
      (integrableOn_Iint h1 (h12.trans_lt h2')) measurableSet_Ioi
    intro v hv; exact Iint_anti h1 h12 h2'.le hv
  · rw [h2', Ifun_one]; exact Ifun_nonneg h1 (h12.trans h2)

lemma Ifun_le {l : ℝ} (h0 : 0 < l) (h1 : l ≤ 1) : Ifun l ≤ 2 / (π * l ^ 2) := by
  rcases h1.lt_or_eq with h | h
  · unfold Ifun
    have hb : MeasureTheory.IntegrableOn (fun v => 2 * (1 + (1 - l) / l) * exp (-(l * v))) (Set.Ioi 0) :=
      (integrableOn_exp_neg_mul h0).const_mul _
    have := MeasureTheory.setIntegral_mono_on (integrableOn_Iint h0 h) hb measurableSet_Ioi
      (fun v hv => (Iint_pos_bound h0 h hv).2)
    rw [MeasureTheory.integral_const_mul, integral_exp_neg_mul h0] at this
    have e : 2 * (1 + (1 - l) / l) * (1 / l) = 2 / l ^ 2 := by field_simp; ring
    rw [e] at this
    calc 1 / π * ∫ v in Set.Ioi (0 : ℝ), Iint l v ≤ 1 / π * (2 / l ^ 2) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by field_simp
  · rw [h, Ifun_one]; positivity

lemma Ifun_inv_nat {m : ℕ} (hm : Odd m) : Ifun (1 / m) = Cp m 1 := by
  have := reciprocity hm odd_one (Nat.coprime_one_right m)
  have hF : Fsum 1 m = 0 := by unfold Fsum; simp
  rw [hF, mul_zero, zero_add] at this
  rw [this]; norm_num

lemma cot_ge {y : ℝ} (h0 : 0 < y) (h1 : y ≤ π / 2) : 1 / y - 2 ≤ Real.cot y := by
  have hs : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos y := Real.cos_nonneg_of_mem_Icc ⟨by linarith, h1⟩
  rw [Real.cot_eq_cos_div_sin, le_div_iff₀ hs]
  have key : Real.sin y * (1 - 2 * y) ≤ y * Real.cos y := by
    rcases le_or_gt (1 / 2) y with h | h
    · have : Real.sin y * (1 - 2 * y) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs.le (by linarith)
      exact this.trans (mul_nonneg h0.le hc)
    · have hsin := Real.sin_le h0.le
      have hcos := Real.one_sub_sq_div_two_le_cos (x := y)
      nlinarith
  have : (1 / y - 2) * Real.sin y = Real.sin y * (1 - 2 * y) / y := by field_simp
  rw [this, div_le_iff₀ h0]; linarith

lemma odd_harmonic_ge (h : ℕ) : Real.log (2 * h + 1) / 2 ≤ ∑ j ∈ range h, 1 / (2 * (j : ℝ) + 1) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [sum_range_succ]
    have hpos : (0 : ℝ) < 2 * h + 1 := by positivity
    have hl := Real.log_le_sub_one_of_pos (x := (2 * h + 3) / (2 * h + 1)) (by positivity)
    rw [Real.log_div (by positivity) hpos.ne'] at hl
    have e : (2 * (h : ℝ) + 3) / (2 * h + 1) - 1 = 2 * (1 / (2 * h + 1)) := by field_simp; ring
    push_cast
    rw [show 2 * ((h : ℝ) + 1) + 1 = 2 * h + 3 by ring]
    linarith

lemma Cp_one_ge {m : ℕ} (hm : Odd m) : (m : ℝ) / π * Real.log m - 2 * m ≤ Cp m 1 := by
  obtain ⟨h, rfl⟩ := hm
  have hpi := Real.pi_pos
  rw [Cp_one_eq, sum_odd_range]
  have hmR : (0 : ℝ) < ((2 * h + 1 : ℕ) : ℝ) := by positivity
  have hterm : ∀ x ∈ range h, 2 * ((2 * h + 1 : ℕ) : ℝ) / π * (1 / (2 * (x : ℝ) + 1)) - 2 ≤
      Real.cot (π * ((2 * x + 1 : ℕ) : ℝ) / (2 * ((2 * h + 1 : ℕ) : ℝ))) := by
    intro x hx
    simp only [mem_range] at hx
    have hxR : (x : ℝ) < h := by exact_mod_cast hx
    have hy0 : 0 < π * ((2 * x + 1 : ℕ) : ℝ) / (2 * ((2 * h + 1 : ℕ) : ℝ)) := by positivity
    have hy1 : π * ((2 * x + 1 : ℕ) : ℝ) / (2 * ((2 * h + 1 : ℕ) : ℝ)) ≤ π / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; push_cast; nlinarith
    refine le_trans (le_of_eq ?_) (cot_ge hy0 hy1)
    push_cast; field_simp
  have hsum := sum_le_sum hterm
  rw [sum_sub_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul] at hsum
  have hh := odd_harmonic_ge h
  push_cast at hsum ⊢
  have : 2 * (2 * (h : ℝ) + 1) / π * (Real.log (2 * h + 1) / 2) ≤
      2 * (2 * (h : ℝ) + 1) / π * ∑ j ∈ range h, 1 / (2 * (j : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hh (by positivity)
  have e : 2 * (2 * (h : ℝ) + 1) / π * (Real.log (2 * h + 1) / 2) = (2 * h + 1) / π * Real.log (2 * h + 1) := by ring
  nlinarith

/-- `|πλ I(λ) - log(1/λ)| ≤ 12` for `0 < λ ≤ 1` (weak form of Lemma 4.2 / Cor. 4.3(c)). -/
theorem I_asymp {l : ℝ} (h0 : 0 < l) (h1 : l ≤ 1) : |π * l * Ifun l - Real.log (1 / l)| ≤ 12 := by
  have hpi := Real.pi_pos
  set x := 1 / l with hx
  have hx1 : 1 ≤ x := by rw [hx, le_div_iff₀ h0]; linarith
  set h := ⌊(x - 1) / 2⌋₊ with hh
  have hfl := Nat.floor_le (show 0 ≤ (x - 1) / 2 by linarith)
  have hfl2 := Nat.lt_floor_add_one ((x - 1) / 2)
  rw [← hh] at hfl hfl2
  set m := 2 * h + 1 with hm
  have hmo : Odd m := ⟨h, rfl⟩
  have hmR : (m : ℝ) = 2 * h + 1 := by rw [hm]; push_cast; ring
  have hmx : (m : ℝ) ≤ x := by rw [hmR]; linarith
  have hxm : x < m + 2 := by rw [hmR]; linarith
  have hm1 : (1 : ℝ) ≤ m := by rw [hmR]; have : (0 : ℝ) ≤ h := h.cast_nonneg; linarith
  have hlx : l = 1 / x := by rw [hx]; field_simp
  have hl_le : l ≤ 1 / m := by rw [hlx]; exact one_div_le_one_div_of_le (by linarith) hmx
  have hl_ge : 1 / ((m : ℝ) + 2) ≤ l := by rw [hlx]; exact one_div_le_one_div_of_le (by linarith) hxm.le
  have hI1 : Ifun (1 / m) ≤ Ifun l := Ifun_anti h0 hl_le (by rw [div_le_one (by linarith)]; exact hm1)
  have hI2 : Ifun l ≤ Ifun (1 / ((m : ℝ) + 2)) := Ifun_anti (by positivity) hl_ge h1
  rw [Ifun_inv_nat hmo] at hI1
  have hm2o : Odd (m + 2) := by rw [hm]; exact ⟨h + 1, by ring⟩
  have hI2' : Ifun (1 / ((m : ℝ) + 2)) = Cp (m + 2) 1 := by
    rw [← Ifun_inv_nat hm2o]; push_cast; rfl
  rw [hI2'] at hI2
  have hup := Cp_one_le hm2o
  have hlow := Cp_one_ge hmo
  push_cast at hup
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm1
  have hlogm2 : Real.log ((m : ℝ) + 2) ≤ Real.log 3 + Real.log x := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) (by linarith)
  have hlogxm : Real.log x ≤ Real.log 3 + Real.log m := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) (by linarith)
  have hlog3 : Real.log 3 < 2 := by
    have := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num) (by norm_num); linarith
  have hlogm2' : Real.log ((m : ℝ) + 2) ≤ m + 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < m + 2 by linarith); linarith
  have hlogm' : Real.log m ≤ m := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < m by linarith); linarith
  have hlogm2pos : 0 ≤ Real.log ((m : ℝ) + 2) := Real.log_nonneg (by linarith)
  rw [abs_le]
  constructor
  · -- lower bound
    have hlm : l * m ≤ 1 := by
      calc l * m ≤ 1 / m * m := mul_le_mul_of_nonneg_right hl_le (by linarith)
        _ = 1 := by field_simp
    have hlm2 : (m : ℝ) / (m + 2) ≤ l * m := by
      calc (m : ℝ) / (m + 2) = 1 / ((m : ℝ) + 2) * m := by ring
        _ ≤ l * m := mul_le_mul_of_nonneg_right hl_ge (by linarith)
    have step1 : π * l * Ifun l ≥ π * l * Cp m 1 := mul_le_mul_of_nonneg_left hI1 (by positivity)
    have step2 : π * l * Cp m 1 ≥ π * l * ((m : ℝ) / π * Real.log m - 2 * m) :=
      mul_le_mul_of_nonneg_left hlow (by positivity)
    have e : π * l * ((m : ℝ) / π * Real.log m - 2 * m) = l * m * Real.log m - 2 * π * (l * m) := by
      field_simp
    have step3 : (m : ℝ) / (m + 2) * Real.log m ≤ l * m * Real.log m :=
      mul_le_mul_of_nonneg_right hlm2 hlogm
    have step4 : Real.log m - 2 ≤ (m : ℝ) / (m + 2) * Real.log m := by
      have : (m : ℝ) / (m + 2) * Real.log m = Real.log m - 2 / (m + 2) * Real.log m := by
        field_simp; ring
      rw [this]
      have : 2 / ((m : ℝ) + 2) * Real.log m ≤ 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
      linarith
    nlinarith [Real.pi_lt_four]
  · -- upper bound
    have step1 : π * l * Ifun l ≤ π * l * Cp (m + 2) 1 := mul_le_mul_of_nonneg_left hI2 (by positivity)
    have step2 : π * l * Cp (m + 2) 1 ≤ π * l * (((m : ℝ) + 2) / π * (Real.log ((m : ℝ) + 2) + 2)) :=
      mul_le_mul_of_nonneg_left hup (by positivity)
    have e : π * l * (((m : ℝ) + 2) / π * (Real.log ((m : ℝ) + 2) + 2)) =
        l * (m + 2) * (Real.log ((m : ℝ) + 2) + 2) := by field_simp
    have hl2 : l * ((m : ℝ) + 2) ≤ 1 + 2 / m := by
      calc l * ((m : ℝ) + 2) ≤ 1 / m * (m + 2) := mul_le_mul_of_nonneg_right hl_le (by linarith)
        _ = 1 + 2 / m := by field_simp
    have step3 : l * ((m : ℝ) + 2) * (Real.log ((m : ℝ) + 2) + 2) ≤
        (1 + 2 / m) * (Real.log ((m : ℝ) + 2) + 2) := mul_le_mul_of_nonneg_right hl2 (by linarith)
    have step4 : 2 / (m : ℝ) * (Real.log ((m : ℝ) + 2) + 2) ≤ 8 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
    have : (1 + 2 / (m : ℝ)) * (Real.log ((m : ℝ) + 2) + 2) =
        (Real.log ((m : ℝ) + 2) + 2) + 2 / (m : ℝ) * (Real.log ((m : ℝ) + 2) + 2) := by ring
    linarith

/-! ### Elementary series -/

lemma hasSum_odd_sq : HasSum (fun j : ℕ => 1 / ((2 * j + 1 : ℕ) : ℝ) ^ 2) (π ^ 2 / 8) := by
  set f : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2 with hf
  have hz : HasSum f (π ^ 2 / 6) := hasSum_zeta_two
  have he : HasSum (fun k => f (2 * k)) (π ^ 2 / 24) := by
    have := hz.mul_left (1 / 4)
    convert this using 1
    · ext k; simp only [hf]; push_cast; ring
    · ring
  have hos : Summable (fun k => f (2 * k + 1)) :=
    hz.summable.comp_injective (fun a b h => by simpa using h)
  have htot := tsum_even_add_odd he.summable hos
  rw [he.tsum_eq, hz.tsum_eq] at htot
  have : ∑' k, f (2 * k + 1) = π ^ 2 / 8 := by linarith
  rw [← this]
  exact hos.hasSum

lemma hasSum_telescope {h : ℕ} (hh : 1 ≤ h) :
    HasSum (fun j : ℕ => 1 / ((j : ℝ) + h) - 1 / ((j : ℝ) + h + 1)) (1 / h) := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · have : ∀ N : ℕ, ∑ i ∈ Finset.range N, (1 / ((i : ℝ) + h) - 1 / ((i : ℝ) + h + 1)) =
        1 / h - 1 / ((N : ℝ) + h) := by
      intro N
      induction N with
      | zero => simp
      | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
    simp_rw [this]
    have : Filter.Tendsto (fun N : ℕ => 1 / ((N : ℝ) + h)) Filter.atTop (nhds 0) := by
      apply Filter.Tendsto.div_atTop tendsto_const_nhds
      exact Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa using (tendsto_const_nhds (x := 1 / (h : ℝ))).sub this
  · intro n
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)

lemma odd_sq_partial (h : ℕ) (hh : 1 ≤ h) :
    0 ≤ π ^ 2 / 8 - ∑ j ∈ range h, 1 / ((2 * j + 1 : ℕ) : ℝ) ^ 2 ∧
      π ^ 2 / 8 - ∑ j ∈ range h, 1 / ((2 * j + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (4 * h) := by
  have hs := hasSum_odd_sq
  have hsplit := hs.summable.sum_add_tsum_nat_add h
  rw [hs.tsum_eq] at hsplit
  have htail : π ^ 2 / 8 - ∑ j ∈ range h, 1 / ((2 * j + 1 : ℕ) : ℝ) ^ 2 =
      ∑' i, 1 / ((2 * (i + h) + 1 : ℕ) : ℝ) ^ 2 := by linarith
  rw [htail]
  have hsum2 : Summable fun i : ℕ => 1 / ((2 * (i + h) + 1 : ℕ) : ℝ) ^ 2 :=
    (summable_nat_add_iff h).2 hs.summable
  constructor
  · exact tsum_nonneg fun i => by positivity
  · have ht := (hasSum_telescope hh).mul_left (1 / 4)
    calc ∑' i, 1 / ((2 * (i + h) + 1 : ℕ) : ℝ) ^ 2
        ≤ ∑' i : ℕ, 1 / 4 * (1 / ((i : ℝ) + h) - 1 / ((i : ℝ) + h + 1)) := by
          apply hsum2.tsum_le_tsum _ ht.summable
          intro i
          have hp : (1 : ℝ) ≤ (i : ℝ) + h := by
            have : (1 : ℝ) ≤ h := by exact_mod_cast hh
            have : (0 : ℝ) ≤ i := i.cast_nonneg
            linarith
          rw [show 1 / ((i : ℝ) + h) - 1 / ((i : ℝ) + h + 1) = 1 / (((i : ℝ) + h) * ((i : ℝ) + h + 1)) by
            field_simp; ring]
          push_cast
          rw [div_le_iff₀ (by positivity)]
          field_simp
          nlinarith
      _ = 1 / (4 * h) := by rw [ht.tsum_eq]; field_simp

lemma log_div_sq_le (k : ℕ) : Real.log k / (k : ℝ) ^ 2 ≤ 2 * ((k : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hl := Real.log_le_rpow_div hkR.le (show (0 : ℝ) < 1 / 2 by norm_num)
  have e : (k : ℝ) ^ (3 / 2 : ℝ) * (k : ℝ) ^ (1 / 2 : ℝ) = (k : ℝ) ^ 2 := by
    rw [← Real.rpow_add hkR]; norm_num
  have hpos : 0 < (k : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hkR _
  have hpos2 : 0 < (k : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hkR _
  rw [← e, div_le_iff₀ (by positivity)]
  have : 2 * ((k : ℝ) ^ (3 / 2 : ℝ))⁻¹ * ((k : ℝ) ^ (3 / 2 : ℝ) * (k : ℝ) ^ (1 / 2 : ℝ)) =
      2 * (k : ℝ) ^ (1 / 2 : ℝ) := by field_simp
  rw [this]; linarith

/-- A constant bounding all partial sums of `Σ log k / k²`. -/
noncomputable def Tlog : ℝ := 2 * ∑' k : ℕ, ((k : ℝ) ^ (3 / 2 : ℝ))⁻¹

lemma sum_log_div_sq_le (s : Finset ℕ) : ∑ k ∈ s, Real.log k / (k : ℝ) ^ 2 ≤ Tlog := by
  have hsum : Summable fun k : ℕ => ((k : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
    Real.summable_nat_rpow_inv.2 (by norm_num)
  calc ∑ k ∈ s, Real.log k / (k : ℝ) ^ 2 ≤ ∑ k ∈ s, 2 * ((k : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
        sum_le_sum fun k _ => log_div_sq_le k
    _ = 2 * ∑ k ∈ s, ((k : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by rw [mul_sum]
    _ ≤ Tlog := by
        unfold Tlog
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact hsum.sum_le_tsum s (fun i _ => by positivity)

/-! ### The estimate for `Ψ(p)` -/

lemma cot_near {p k : ℕ} (hk0 : 0 < k) (hkp : k < p) :
    0 ≤ 2 * p / (π * k) - Real.cot (π * k / (2 * p)) ∧
      2 * p / (π * k) - Real.cot (π * k / (2 * p)) ≤ 2 := by
  have hpi := Real.pi_pos
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hpR : (0 : ℝ) < p := by exact_mod_cast (hk0.trans hkp)
  have hkp' : (k : ℝ) < p := by exact_mod_cast hkp
  have hy0 : 0 < π * k / (2 * p) := by positivity
  have hy1 : π * k / (2 * p) < π / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hinv : 1 / (π * k / (2 * p)) = 2 * p / (π * k) := by field_simp
  have h1 := cot_le_inv hy0 hy1
  have h2 := cot_ge hy0 hy1.le
  rw [hinv] at h1 h2
  constructor <;> linarith

lemma Psi_term {p k : ℕ} (hk0 : 0 < k) (hkp : k < p) :
    |2 / p * (Real.cot (π * k / (2 * p)) * Ifun ((k : ℝ) / p)) -
      4 * p / (π ^ 2 * k ^ 2) * (Real.log p - Real.log k)| ≤
        48 * p / (π ^ 2 * k ^ 2) + 4 / (π * k) * (Real.log p + 12) := by
  have hpi := Real.pi_pos
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hpR : (0 : ℝ) < p := by exact_mod_cast (hk0.trans hkp)
  have hkp' : (k : ℝ) < p := by exact_mod_cast hkp
  have hl0 : 0 < (k : ℝ) / p := by positivity
  have hl1 : (k : ℝ) / p ≤ 1 := by rw [div_le_one hpR]; linarith
  have hasy := I_asymp hl0 hl1
  set I := Ifun ((k : ℝ) / p) with hI
  have hI0 : 0 ≤ I := Ifun_nonneg hl0 hl1
  set L := Real.log p - Real.log k with hL
  have hlog : Real.log (1 / ((k : ℝ) / p)) = L := by
    rw [one_div_div, Real.log_div hpR.ne' hkR.ne']
  rw [hlog] at hasy
  set ε := π * ((k : ℝ) / p) * I - L with hε
  have hε' : |ε| ≤ 12 := hasy
  obtain ⟨hd0, hd2⟩ := cot_near (p := p) hk0 hkp
  set δ := 2 * p / (π * k) - Real.cot (π * k / (2 * p)) with hδ
  have hcot : Real.cot (π * k / (2 * p)) = 2 * p / (π * k) - δ := by rw [hδ]; ring
  have hIeq : I = p / (π * k) * (L + ε) := by
    rw [hε]; field_simp; ring
  have hE : 2 / p * (Real.cot (π * k / (2 * p)) * I) - 4 * p / (π ^ 2 * k ^ 2) * L =
      4 * p / (π ^ 2 * k ^ 2) * ε - 2 / p * δ * I := by
    rw [hcot]
    conv_lhs => rw [hIeq]
    field_simp
    ring_nf
    rw [hIeq]
    field_simp
    ring
  rw [hE]
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk0)
  have hIle : I ≤ p / (π * k) * (Real.log p + 12) := by
    rw [hIeq]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := (abs_le.1 hε').2
    linarith
  calc |4 * p / (π ^ 2 * k ^ 2) * ε - 2 / p * δ * I|
      ≤ |4 * p / (π ^ 2 * k ^ 2) * ε| + |2 / p * δ * I| := abs_sub _ _
    _ ≤ 4 * p / (π ^ 2 * k ^ 2) * 12 + 2 / p * 2 * (p / (π * k) * (Real.log p + 12)) := by
        gcongr
        · rw [abs_mul, abs_of_pos (by positivity)]; gcongr
        · rw [abs_of_nonneg (by positivity)]
          gcongr
    _ = _ := by field_simp; ring

lemma log_sq_le {x : ℝ} (hx : 1 ≤ x) : Real.log x ^ 2 ≤ 4 * x := by
  have h := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ x) (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [← Real.sqrt_eq_rpow] at h
  have h0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hs := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ x)
  have : Real.log x ≤ 2 * Real.sqrt x := by linarith
  nlinarith [Real.sqrt_nonneg x]

lemma log_le_self' {x : ℝ} (hx : 0 < x) : Real.log x ≤ x := by
  have := Real.log_le_sub_one_of_pos hx; linarith

lemma sum_inv_odd_le (p : ℕ) : ∑ k ∈ (range p).filter Odd, 1 / (k : ℝ) ≤ 1 + Real.log p := by
  calc ∑ k ∈ (range p).filter Odd, 1 / (k : ℝ) ≤ ∑ k ∈ range (p + 1), 1 / (k : ℝ) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro k hk; simp only [mem_filter, mem_range] at hk ⊢; omega
        · intro k _ _; positivity
    _ = harmonic p := (harmonic_cast p).symm
    _ ≤ 1 + Real.log p := harmonic_le_one_add_log p

/-- `Ψ(p) = (p/2) log p + O(p)`. -/
theorem Psi_bound : ∃ C : ℝ, ∀ p : ℕ, 3 ≤ p → Odd p → |Psi p - p / 2 * Real.log p| ≤ C * p := by
  have hT : 0 ≤ Tlog := by
    unfold Tlog; apply mul_nonneg (by norm_num); exact tsum_nonneg fun k => by positivity
  refine ⟨6 + 4 * 29 + 1 + 4 * Tlog, fun p hp3 hpo => ?_⟩
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hlogp0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hlogp : Real.log p ≤ p := log_le_self' (by linarith)
  have hlog2 : Real.log p ^ 2 ≤ 4 * p := log_sq_le (by linarith)
  obtain ⟨h, rfl⟩ := hpo
  have hh1 : 1 ≤ h := by omega
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  set p := 2 * h + 1 with hp
  have hpR' : (p : ℝ) = 2 * h + 1 := by rw [hp]; push_cast; ring
  set s := (range p).filter Odd with hs
  have hmem : ∀ k ∈ s, 0 < k ∧ k < p := by
    intro k hk; simp only [hs, mem_filter, mem_range] at hk; exact ⟨hk.2.pos, hk.1⟩
  -- the sums
  set S2 := ∑ k ∈ s, 1 / (k : ℝ) ^ 2 with hS2
  set SL := ∑ k ∈ s, Real.log k / (k : ℝ) ^ 2 with hSL
  have hS2' : S2 = ∑ j ∈ range h, 1 / ((2 * j + 1 : ℕ) : ℝ) ^ 2 := by
    rw [hS2, hs, hp, sum_odd_range]
  obtain ⟨hS2a, hS2b⟩ := odd_sq_partial h hh1
  rw [← hS2'] at hS2a hS2b
  have hSL0 : 0 ≤ SL := sum_nonneg fun k hk => by
    have := (hmem k hk).1
    have : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast this)
    positivity
  have hSLT : SL ≤ Tlog := sum_log_div_sq_le s
  have hH := sum_inv_odd_le p
  rw [← hs] at hH
  set M := ∑ k ∈ s, 4 * p / (π ^ 2 * k ^ 2) * (Real.log p - Real.log k) with hM
  have hMeq : M = 4 * p / π ^ 2 * (Real.log p * S2 - SL) := by
    rw [hM, hS2, hSL, mul_sum, ← sum_sub_distrib, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have := (hmem k hk).1
    have hk : (k : ℝ) ≠ 0 := by exact_mod_cast this.ne'
    field_simp
  -- `|Ψ - M|`
  have h1 : |Psi p - M| ≤ 48 * p / π ^ 2 * S2 + 4 / π * (Real.log p + 12) * (1 + Real.log p) := by
    have : Psi p - M = ∑ k ∈ s, (2 / p * (Real.cot (π * k / (2 * p)) * Ifun ((k : ℝ) / p)) -
        4 * p / (π ^ 2 * k ^ 2) * (Real.log p - Real.log k)) := by
      rw [Psi, mul_sum, hM, ← sum_sub_distrib]
    rw [this]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ s, |2 / p * (Real.cot (π * k / (2 * p)) * Ifun ((k : ℝ) / p)) -
          4 * p / (π ^ 2 * k ^ 2) * (Real.log p - Real.log k)|
        ≤ ∑ k ∈ s, (48 * p / (π ^ 2 * k ^ 2) + 4 / (π * k) * (Real.log p + 12)) :=
          sum_le_sum fun k hk => Psi_term (hmem k hk).1 (hmem k hk).2
      _ = 48 * p / π ^ 2 * S2 + 4 / π * (Real.log p + 12) * ∑ k ∈ s, 1 / (k : ℝ) := by
          rw [sum_add_distrib, hS2, mul_sum, mul_sum]
          congr 1 <;> refine sum_congr rfl fun k hk => ?_ <;>
            (have := (hmem k hk).1; have hk : (k : ℝ) ≠ 0 := by exact_mod_cast this.ne') <;>
            field_simp
      _ ≤ _ := by gcongr
  -- `|M - (p/2) log p|`
  have h2 : |M - p / 2 * Real.log p| ≤ 4 * p / π ^ 2 * Real.log p * (1 / (4 * h)) + 4 * p / π ^ 2 * Tlog := by
    rw [hMeq]
    have e : 4 * (p : ℝ) / π ^ 2 * (Real.log p * S2 - SL) - p / 2 * Real.log p =
        -(4 * p / π ^ 2 * Real.log p * (π ^ 2 / 8 - S2)) - 4 * p / π ^ 2 * SL := by
      field_simp; ring
    rw [e]
    have hA : 0 ≤ 4 * (p : ℝ) / π ^ 2 * Real.log p * (π ^ 2 / 8 - S2) := by positivity
    have hB : 0 ≤ 4 * (p : ℝ) / π ^ 2 * SL := by positivity
    rw [abs_le]; constructor
    · have : 4 * (p : ℝ) / π ^ 2 * Real.log p * (π ^ 2 / 8 - S2) ≤
          4 * p / π ^ 2 * Real.log p * (1 / (4 * h)) := by gcongr
      have : 4 * (p : ℝ) / π ^ 2 * SL ≤ 4 * p / π ^ 2 * Tlog := by gcongr
      linarith
    · have : 0 ≤ 4 * (p : ℝ) / π ^ 2 * Real.log p * (1 / (4 * h)) := by positivity
      have : 0 ≤ 4 * (p : ℝ) / π ^ 2 * Tlog := by positivity
      linarith
  -- numerics
  have n1 : 48 * (p : ℝ) / π ^ 2 * S2 ≤ 6 * (p : ℝ) := by
    calc 48 * (p : ℝ) / π ^ 2 * S2 ≤ 48 * p / π ^ 2 * (π ^ 2 / 8) := by gcongr; linarith
      _ = 6 * (p : ℝ) := by field_simp; ring
  have n2 : 4 / π * (Real.log p + 12) * (1 + Real.log p) ≤ 4 * 29 * (p : ℝ) := by
    have : 4 / π ≤ 4 := by rw [div_le_iff₀ hpi]; nlinarith
    have : (Real.log p + 12) * (1 + Real.log p) ≤ 29 * (p : ℝ) := by nlinarith
    calc 4 / π * (Real.log p + 12) * (1 + Real.log p) = 4 / π * ((Real.log p + 12) * (1 + Real.log p)) := by ring
      _ ≤ 4 * (29 * (p : ℝ)) := by gcongr
      _ = 4 * 29 * (p : ℝ) := by ring
  have n3 : 4 * (p : ℝ) / π ^ 2 * Real.log p * (1 / (4 * h)) ≤ (p : ℝ) := by
    have : 4 * (p : ℝ) / π ^ 2 * Real.log p * (1 / (4 * h)) = (p / (π ^ 2 * h)) * Real.log p := by
      field_simp
    rw [this]
    have hq : (p : ℝ) / (π ^ 2 * h) ≤ 1 := by
      have hpi2 : 9 < π ^ 2 := by nlinarith
      rw [div_le_one (by positivity), hpR']; nlinarith
    calc (p : ℝ) / (π ^ 2 * h) * Real.log p ≤ 1 * Real.log p := by gcongr
      _ ≤ (p : ℝ) := by linarith
  have n4 : 4 * (p : ℝ) / π ^ 2 * Tlog ≤ 4 * Tlog * p := by
    have : 4 / π ^ 2 ≤ 4 := by rw [div_le_iff₀ (by positivity)]; nlinarith
    calc 4 * (p : ℝ) / π ^ 2 * Tlog = 4 / π ^ 2 * (Tlog * p) := by ring
      _ ≤ 4 * (Tlog * p) := by gcongr
      _ = 4 * Tlog * p := by ring
  calc |Psi p - p / 2 * Real.log p| ≤ |Psi p - M| + |M - p / 2 * Real.log p| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add h1 h2
    _ ≤ 6 * (p : ℝ) + 4 * 29 * (p : ℝ) + (p : ℝ) + 4 * Tlog * p := by linarith
    _ = (6 + 4 * 29 + 1 + 4 * Tlog) * p := by ring

end Analytic

section Weil
open Finset Complex
open Arxiv.«2501.03234»

/-- Weil's bound for Kloosterman sums (A. Weil, *On some exponential sums*,
Proc. Nat. Acad. Sci. U.S.A. **34** (1948), 204–207): for a prime `p` and integers `b, ℓ` with
`p ∤ b`, `|Σ_{z=1}^{p-1} e((b z* + ℓ z)/p)| ≤ 2 √p`, where `z*` is the inverse of `z` mod `p`.
We take it as a hypothesis. -/
def HW : Prop :=
  ∀ p : ℕ, p.Prime → ∀ b ℓ : ℤ, ¬ (p : ℤ) ∣ b →
    ‖∑ z ∈ Ico 1 p, Complex.exp (2 * Real.pi * I *
      (((b * (((z : ZMod p)⁻¹).val : ℤ) + ℓ * z : ℤ) : ℝ) / p))‖ ≤ 2 * Real.sqrt p

/-- Kloosterman's bound with exponent `3/4` (implied by Weil's bound `2√p`; provable by
Kloosterman's elementary fourth-moment argument):
`|Σ_{z ∈ (ℤ/p)^×} e((b z⁻¹ + ℓ z)/p)| ≤ 2 p^{3/4}` for `b ≢ 0`. Taken as a hypothesis. -/
def HK34 : Prop :=
  ∀ p : ℕ, ∀ hp : p.Prime, haveI : Fact p.Prime := ⟨hp⟩; ∀ b ℓ : ZMod p, b ≠ 0 →
    ‖∑ z ∈ (Finset.univ : Finset (ZMod p)).filter (· ≠ 0),
      Complex.exp (2 * Real.pi * I * (((b * z⁻¹ + ℓ * z).val : ℂ) / p))‖ ≤ 2 * (p : ℝ) ^ ((3 : ℝ) / 4)

/-- inverse of `k` modulo `2p`. -/
def kbar (p k : ℕ) : ℕ := ((k : ZMod (2 * p))⁻¹).val
/-- inverse of `y` modulo `p`. -/
def invp (p y : ℕ) : ℕ := ((y : ZMod p)⁻¹).val

variable {p : ℕ}

lemma kbar_mul {k : ℕ} (hp : p.Prime) (_hp2 : p ≠ 2) (hk : Odd k) (hkp : k < p) :
    (k * kbar p k) % (2 * p) = 1 := by
  have hp0 := hp.pos
  have : NeZero (2 * p) := ⟨by omega⟩
  have hcop : Nat.Coprime k (2 * p) := by
    refine Nat.Coprime.mul_right (Nat.coprime_two_right.2 hk) ?_
    exact (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2
      fun h => absurd (Nat.le_of_dvd hk.pos h) (by omega)))
  have h1 := ZMod.coe_mul_inv_eq_one k hcop
  have h2 : ((k * kbar p k : ℕ) : ZMod (2 * p)) = ((1 : ℕ) : ZMod (2 * p)) := by
    unfold kbar; push_cast; rw [ZMod.natCast_zmod_val]; exact h1
  rw [ZMod.natCast_eq_natCast_iff'] at h2
  rw [h2]; exact Nat.mod_eq_of_lt (by omega)

lemma kbar_odd {k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : Odd k) (hkp : k < p) : Odd (kbar p k) := by
  have h := kbar_mul hp hp2 hk hkp
  have h2 : (k * kbar p k) % 2 = 1 := by
    rw [← Nat.mod_mod_of_dvd (k * kbar p k) (dvd_mul_right 2 p), h]
  rw [Nat.odd_iff]
  rcases Nat.mod_two_eq_zero_or_one (kbar p k) with h3 | h3
  · rw [Nat.mul_mod, h3] at h2; simp at h2
  · exact h3

lemma kbar_mod_p {k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : Odd k) (hkp : k < p) :
    ((kbar p k : ℕ) : ZMod p) = (((p + 1) / 2 : ℕ) : ZMod p) * (invp p ((k - 1) / 2 + (p + 1) / 2) : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  have hpo : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨h0, hh0⟩ := hpo
  have h := kbar_mul hp hp2 hk hkp
  have hmodp : (k * kbar p k) % p = 1 := by
    rw [← Nat.mod_mod_of_dvd (k * kbar p k) (dvd_mul_left p 2), h]
    exact Nat.mod_eq_of_lt hp.one_lt
  have hkx : ((k : ZMod p) * (kbar p k : ZMod p)) = 1 := by
    have : ((k * kbar p k : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rw [ZMod.natCast_eq_natCast_iff', hmodp, Nat.mod_eq_of_lt hp.one_lt]
    push_cast at this; exact this
  set y := (k - 1) / 2 + (p + 1) / 2 with hy
  have hky : (k : ZMod p) = 2 * (y : ZMod p) := by
    have e : k + p = 2 * y := by
      obtain ⟨j, rfl⟩ := hk; rw [hy]; omega
    have := congrArg (Nat.cast : ℕ → ZMod p) e
    push_cast at this
    rw [ZMod.natCast_self, add_zero] at this
    exact this
  have h2h : (2 : ZMod p) * (((p + 1) / 2 : ℕ) : ZMod p) = 1 := by
    have e : 2 * ((p + 1) / 2) = p + 1 := by omega
    have := congrArg (Nat.cast : ℕ → ZMod p) e
    push_cast at this
    rw [ZMod.natCast_self, zero_add] at this
    exact this
  have hy0 : (y : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have : y < p := by obtain ⟨j, rfl⟩ := hk; rw [hy]; omega
    have : 0 < y := by rw [hy]; omega
    exact absurd (Nat.le_of_dvd this hd) (by omega)
  unfold invp
  rw [ZMod.natCast_zmod_val]
  rw [hky] at hkx
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0'; rw [h0', zero_mul] at h2h; exact zero_ne_one h2h
  have hh : (((p + 1) / 2 : ℕ) : ZMod p) = 2⁻¹ := by
    exact eq_inv_of_mul_eq_one_right h2h
  rw [hh]
  field_simp
  linear_combination hkx

lemma pow_eq_pow_of_mod {ω : ℂ} {n a b : ℕ} (hω : ω ^ n = 1) (hab : a % n = b % n) : ω ^ a = ω ^ b := by
  rw [← Nat.mod_add_div a n, ← Nat.mod_add_div b n, pow_add, pow_add, pow_mul, pow_mul, hω,
    one_pow, one_pow, hab]

lemma omega_pow_p (hp : 0 < p) : (zeta p ^ 2) ^ p = 1 := by
  rw [← pow_mul, (zeta_prim hp).pow_eq_one]

/-- `e(c k̄/2p) = (-1)^c e(c 2̄² (j+2̄)^*/p)` with `k = 2j+1`, `2̄ = (p+1)/2`. -/
lemma zeta_kbar (hp : p.Prime) (hp2 : p ≠ 2) (c : ℕ) {k : ℕ} (hk : Odd k) (hkp : k < p) :
    zeta p ^ (c * kbar p k) = (-1) ^ c *
      (zeta p ^ 2) ^ (c * ((p + 1) / 2) ^ 2 * invp p ((k - 1) / 2 + (p + 1) / 2)) := by
  have hp0 := hp.pos
  have hpo : Odd p := hp.odd_of_ne_two hp2
  set x := kbar p k with hx
  set hh := (p + 1) / 2 with hhh
  set y := (k - 1) / 2 + (p + 1) / 2 with hy
  have hxo : Odd x := kbar_odd hp hp2 hk hkp
  have h2h : 2 * hh = p + 1 := by obtain ⟨t, ht⟩ := hpo; rw [hhh]; omega
  have e1 : zeta p ^ (2 * (c * hh * x)) = zeta p ^ (c * x) * (-1) ^ c := by
    rw [show 2 * (c * hh * x) = c * x + p * (c * x) by
      rw [show 2 * (c * hh * x) = (2 * hh) * (c * x) by ring, h2h]; ring,
      pow_add, pow_mul (zeta p) p (c * x), zeta_pow_p hp0]
    have hm1 : ((-1 : ℂ)) ^ (c * x) = (-1) ^ c := by
      rw [mul_comm, pow_mul, Odd.neg_one_pow hxo]
    rw [hm1]
  have e2 : (zeta p ^ 2) ^ (c * hh * x) = (zeta p ^ 2) ^ (c * hh ^ 2 * invp p y) := by
    apply pow_eq_pow_of_mod (omega_pow_p hp0)
    rw [← ZMod.natCast_eq_natCast_iff']
    push_cast
    rw [hx, kbar_mod_p hp hp2 hk hkp]
    ring
  rw [← e2, ← pow_mul, e1]
  have : ((-1 : ℂ) ^ c) * (-1) ^ c = 1 := by rw [← mul_pow]; simp
  rw [show (-1 : ℂ) ^ c * (zeta p ^ (c * x) * (-1) ^ c) = zeta p ^ (c * x) * ((-1) ^ c * (-1) ^ c) by
    ring, this, mul_one]

lemma omega_prim (hp : 0 < p) : IsPrimitiveRoot (zeta p ^ 2) p :=
  (zeta_prim hp).pow (by omega) (by ring)

lemma sum_omega (hp : 0 < p) (t : ℕ) :
    ∑ ℓ ∈ range p, (zeta p ^ 2) ^ (ℓ * t) = if p ∣ t then (p : ℂ) else 0 := by
  have hpr := omega_prim hp
  have e : ∀ ℓ, (zeta p ^ 2) ^ (ℓ * t) = ((zeta p ^ 2) ^ t) ^ ℓ := fun ℓ => by
    rw [← pow_mul, ← pow_mul, ← pow_mul]; congr 1; ring
  simp_rw [e]
  split_ifs with h
  · rw [(hpr.pow_eq_one_iff_dvd t).2 h]; simp
  · have hne : (zeta p ^ 2) ^ t ≠ 1 := fun h' => h ((hpr.pow_eq_one_iff_dvd t).1 h')
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hpr.pow_eq_one, one_pow, sub_self, zero_div]

/-- Completion of an incomplete sum of `e(b y*/p)`. -/
lemma completion (hp : p.Prime) (b : ℕ) (Y : Finset ℕ) (hY : ∀ y ∈ Y, 1 ≤ y ∧ y < p) :
    ∑ y ∈ Y, (zeta p ^ 2) ^ (b * invp p y) =
      1 / (p : ℂ) * ∑ ℓ ∈ range p, (∑ y ∈ Y, (zeta p ^ 2) ^ (ℓ * y)) *
        (∑ z ∈ Ico 1 p, (zeta p ^ 2) ^ (b * invp p z + ℓ * (p - z))) := by
  have hp0 := hp.pos
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  set ω := zeta p ^ 2 with hω
  have key : ∀ y ∈ Y, ∑ z ∈ Ico 1 p, ω ^ (b * invp p z) * ∑ ℓ ∈ range p, ω ^ (ℓ * (y + (p - z))) =
      p * ω ^ (b * invp p y) := by
    intro y hy
    obtain ⟨hy1, hyp⟩ := hY y hy
    simp_rw [hω, sum_omega hp0]
    rw [sum_eq_single y]
    · rw [ite_eq_left (by rw [show y + (p - y) = p by omega])]; ring
    · intro z hz hzy
      simp only [mem_Ico] at hz
      rw [ite_eq_right, mul_zero]
      rintro ⟨q, hq⟩
      have hq1 : q < 2 := by
        by_contra hc; have : p * 2 ≤ p * q := Nat.mul_le_mul_left _ (by omega); omega
      interval_cases q <;> omega
    · intro hy'; exact absurd (mem_Ico.2 ⟨hy1, hyp⟩) hy'
  have hrhs : ∑ ℓ ∈ range p, (∑ y ∈ Y, ω ^ (ℓ * y)) * (∑ z ∈ Ico 1 p, ω ^ (b * invp p z + ℓ * (p - z))) =
      ∑ y ∈ Y, ∑ z ∈ Ico 1 p, ω ^ (b * invp p z) * ∑ ℓ ∈ range p, ω ^ (ℓ * (y + (p - z))) := by
    simp_rw [sum_mul_sum, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun z _ => sum_congr rfl fun ℓ _ => ?_
    rw [← pow_add, ← pow_add]; congr 1; ring
  rw [hrhs, sum_congr rfl key, ← mul_sum]
  field_simp

lemma omega_pow_eq_exp (hp : 0 < p) (n : ℕ) :
    (zeta p ^ 2) ^ n = Complex.exp (2 * Real.pi * I * ((n : ℂ) / p)) := by
  rw [← pow_mul, zeta_pow_eq_exp hp]
  congr 1
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  push_cast; field_simp

lemma kloosterman_eq (hp : 0 < p) (b ℓ : ℕ) :
    ∑ z ∈ Ico 1 p, (zeta p ^ 2) ^ (b * invp p z + ℓ * (p - z)) =
      ∑ z ∈ Ico 1 p, Complex.exp (2 * Real.pi * I *
        (((((b : ℤ) * (((z : ZMod p)⁻¹).val : ℤ) + (-(ℓ : ℤ)) * z : ℤ)) : ℝ) / p)) := by
  refine sum_congr rfl fun z hz => ?_
  simp only [mem_Ico] at hz
  rw [omega_pow_eq_exp hp, Complex.exp_eq_exp_iff_exists_int]
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  refine ⟨ℓ, ?_⟩
  unfold invp
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hz.2.le]
  push_cast
  field_simp
  ring

lemma sum_Fq_double_le (hp : 0 < p) :
    ∑ ℓ ∈ Ico 1 p, Fq p ((2 * ℓ) % (2 * p)) ≤ 2 * (1 + Real.log p) := by
  refine (sum_inj_le hp (Ico 1 p) (fun ℓ => 2 * ℓ) ?_).trans ?_
  · intro a ha b hb hab
    simp only [coe_Ico, Set.mem_Ico] at ha hb
    simp only at hab
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hab
    omega
  · have := harmonic_le_one_add_log p
    linarith

/-- A uniform bound `Bk` for the (complete) Kloosterman sums modulo `p`. -/
def KlBound (p : ℕ) (Bk : ℝ) : Prop :=
  ∀ b : ℕ, ¬ p ∣ b → ∀ ℓ : ℕ, ‖∑ z ∈ Ico 1 p, (zeta p ^ 2) ^ (b * invp p z + ℓ * (p - z))‖ ≤ Bk

lemma KlBound_of_HW (hW : HW) (hp : p.Prime) : KlBound p (2 * Real.sqrt p) := by
  intro b hb ℓ
  rw [kloosterman_eq hp.pos]
  apply hW p hp
  intro hd; exact hb (by exact_mod_cast hd)

lemma KlBound_of_HK34 (hK : HK34) (hp : p.Prime) : KlBound p (2 * (p : ℝ) ^ ((3 : ℝ) / 4)) := by
  have hF : Fact p.Prime := ⟨hp⟩
  have hp0 := hp.pos
  intro b hb ℓ
  have hb0 : (b : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hb
  have h := hK p hp (b : ZMod p) (-(ℓ : ZMod p)) hb0
  refine le_of_eq_of_le (congrArg norm ?_) h
  apply sum_nbij' (fun z : ℕ => (z : ZMod p)) (fun w : ZMod p => w.val)
  · intro z hz
    simp only [mem_Ico] at hz
    simp only [mem_filter, mem_univ, true_and, Ne, ZMod.natCast_eq_zero_iff]
    intro hd; exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw
    simp only [mem_Ico]
    exact ⟨Nat.one_le_iff_ne_zero.2 (fun h0 => hw ((ZMod.val_eq_zero w).1 h0)), ZMod.val_lt w⟩
  · intro z hz
    simp only [mem_Ico] at hz
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hz.2]
  · intro w _
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
  · intro z hz
    simp only [mem_Ico] at hz
    set N := b * invp p z + ℓ * (p - z) with hN
    have hcast : ((N : ℕ) : ZMod p) = (b : ZMod p) * ((z : ℕ) : ZMod p)⁻¹ + -(ℓ : ZMod p) * (z : ZMod p) := by
      rw [hN]; unfold invp
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_sub hz.2.le,
        ZMod.natCast_self]
      ring
    rw [← hcast, ZMod.val_natCast, ← omega_pow_eq_exp hp0]
    apply pow_eq_pow_of_mod (omega_pow_p hp0)
    rw [Nat.mod_mod]

/-- Incomplete Kloosterman-type sums over an interval, by completion. -/
lemma weil_interval {Bk : ℝ} (hKl : KlBound p Bk) (hp : p.Prime) (b : ℕ) (hb : ¬ p ∣ b) (a c : ℕ) (ha : 1 ≤ a)
    (hc : c ≤ p) :
    ‖∑ y ∈ Ico a c, (zeta p ^ 2) ^ (b * invp p y)‖ ≤
      Bk * (1 + 2 * (1 + Real.log p)) := by
  have hp0 := hp.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hK : ∀ ℓ : ℕ, ‖∑ z ∈ Ico 1 p, (zeta p ^ 2) ^ (b * invp p z + ℓ * (p - z))‖ ≤ Bk := hKl b hb
  have hsq : 0 ≤ Bk := (norm_nonneg _).trans (hK 0)
  rw [completion hp b (Ico a c) (fun y hy => by simp only [mem_Ico] at hy; omega)]
  have hG0 : ‖∑ y ∈ Ico a c, (zeta p ^ 2) ^ (0 * y)‖ ≤ p := by
    simp only [zero_mul, pow_zero, sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one, norm_natCast]
    exact_mod_cast (Nat.sub_le c a).trans hc
  have hG : ∀ ℓ ∈ Ico 1 p, ‖∑ y ∈ Ico a c, (zeta p ^ 2) ^ (ℓ * y)‖ ≤ p * Fq p ((2 * ℓ) % (2 * p)) := by
    intro ℓ hℓ
    simp only [mem_Ico] at hℓ
    have e : ∀ y, (zeta p ^ 2) ^ (ℓ * y) = (zeta p ^ (2 * ℓ)) ^ y := fun y => by
      rw [← pow_mul, ← pow_mul, mul_assoc]
    simp_rw [e]
    rcases le_or_gt a c with hac | hac
    · apply geom_bound hp0 (2 * ℓ) _ hac
      intro hd; have := Nat.le_of_dvd (by omega) hd; omega
    · rw [Ico_eq_empty_of_le hac.le]; simp only [sum_empty, norm_zero]
      exact mul_nonneg hpR.le (Fq_nonneg _ _)
  calc ‖1 / (p : ℂ) * ∑ ℓ ∈ range p, (∑ y ∈ Ico a c, (zeta p ^ 2) ^ (ℓ * y)) *
        ∑ z ∈ Ico 1 p, (zeta p ^ 2) ^ (b * invp p z + ℓ * (p - z))‖
      ≤ 1 / p * ∑ ℓ ∈ range p, ‖∑ y ∈ Ico a c, (zeta p ^ 2) ^ (ℓ * y)‖ * Bk := by
        rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
        gcongr
        refine (norm_sum_le _ _).trans (sum_le_sum fun ℓ _ => ?_)
        rw [norm_mul]; gcongr; exact hK ℓ
    _ = 1 / p * Bk * (‖∑ y ∈ Ico a c, (zeta p ^ 2) ^ (0 * y)‖ +
          ∑ ℓ ∈ Ico 1 p, ‖∑ y ∈ Ico a c, (zeta p ^ 2) ^ (ℓ * y)‖) := by
        rw [← sum_mul, range_eq_Ico, sum_eq_sum_Ico_succ_bot hp0]; ring
    _ ≤ 1 / p * Bk * (p + p * (2 * (1 + Real.log p))) := by
        apply mul_le_mul_of_nonneg_left (add_le_add hG0 ?_) (by positivity)
        calc ∑ ℓ ∈ Ico 1 p, ‖∑ y ∈ Ico a c, (zeta p ^ 2) ^ (ℓ * y)‖
              ≤ ∑ ℓ ∈ Ico 1 p, p * Fq p ((2 * ℓ) % (2 * p)) := sum_le_sum hG
            _ = p * ∑ ℓ ∈ Ico 1 p, Fq p ((2 * ℓ) % (2 * p)) := by rw [mul_sum]
            _ ≤ p * (2 * (1 + Real.log p)) := by gcongr; exact sum_Fq_double_le hp0
    _ = Bk * (1 + 2 * (1 + Real.log p)) := by field_simp

/-- **Lemma 5.2** (from Weil's bound): for `p ∤ c` and `B ≤ p`,
`|Σ_{A ≤ k < B, k odd} e(c k̄ / 2p)| ≤ 2√p (3 + 2 log p)`. -/
lemma weil_kbar {Bk : ℝ} (hKl : KlBound p Bk) (hp : p.Prime) (hp2 : p ≠ 2) (c : ℕ) (hc : ¬ p ∣ c) (A B : ℕ)
    (hB : B ≤ p) :
    ‖∑ k ∈ (Ico A B).filter Odd, zeta p ^ (c * kbar p k)‖ ≤
      Bk * (1 + 2 * (1 + Real.log p)) := by
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hp2le := hp.two_le
  obtain ⟨h0, hh0⟩ := hpo
  set hh := (p + 1) / 2 with hhh
  have hhp : hh = h0 + 1 := by omega
  have e1 : ∑ k ∈ (Ico A B).filter Odd, zeta p ^ (c * kbar p k) =
      (-1) ^ c * ∑ k ∈ (Ico A B).filter Odd,
        (zeta p ^ 2) ^ (c * hh ^ 2 * invp p ((k - 1) / 2 + hh)) := by
    rw [mul_sum]
    refine sum_congr rfl fun k hk => ?_
    simp only [mem_filter, mem_Ico] at hk
    exact zeta_kbar hp hp2 c hk.2 (by omega)
  have e2 : ∑ k ∈ (Ico A B).filter Odd, (zeta p ^ 2) ^ (c * hh ^ 2 * invp p ((k - 1) / 2 + hh)) =
      ∑ y ∈ Ico (A / 2 + hh) (B / 2 + hh), (zeta p ^ 2) ^ (c * hh ^ 2 * invp p y) := by
    apply sum_nbij' (fun k => (k - 1) / 2 + hh) (fun y => 2 * (y - hh) + 1)
    · intro k hk
      simp only [mem_filter, mem_Ico] at hk ⊢
      obtain ⟨⟨h1, h2⟩, ⟨t, rfl⟩⟩ := hk
      omega
    · intro y hy
      simp only [mem_filter, mem_Ico] at hy ⊢
      exact ⟨⟨by omega, by omega⟩, ⟨y - hh, rfl⟩⟩
    · intro k hk
      simp only [mem_filter, mem_Ico] at hk
      obtain ⟨⟨h1, h2⟩, ⟨t, rfl⟩⟩ := hk
      omega
    · intro y hy
      simp only [mem_Ico] at hy
      omega
    · intro k _; rfl
  rw [e1, e2, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  apply weil_interval hKl hp
  · intro hd
    rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
    · exact hc h
    · have := Nat.Prime.dvd_of_dvd_pow hp h
      exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  · omega
  · omega

/-- Coefficients of the finite Fourier expansion of `(-1)^⌊n/p⌋`. -/
noncomputable def cl (p l : ℕ) : ℂ := ∑ m ∈ Ico 1 (p + 1), (zeta p ^ (2 * l + 1)) ^ m

lemma sigma_expand (hp : 0 < p) (m : ℕ) :
    ((sigma p m : ℤ) : ℂ) = -(1 / (p : ℂ)) * ∑ l ∈ range p, cl p l * zeta p ^ ((2 * l + 1) * m) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have h := expansion hp m
  unfold sigma; push_cast
  have e : ∀ l ∈ range p, cl p l * zeta p ^ ((2 * l + 1) * m) =
      (∑ m' ∈ Ico 1 (p + 1), (zeta p ^ (2 * l + 1)) ^ m') * (zeta p ^ (2 * l + 1)) ^ m := by
    intro l _; rw [cl, pow_mul]
  rw [sum_congr rfl e]
  field_simp
  linear_combination h

lemma kbar_modEq {k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : Odd k) (hkp : k < p) :
    k * kbar p k ≡ 1 [MOD 2 * p] := by
  unfold Nat.ModEq
  rw [kbar_mul hp hp2 hk hkp, Nat.mod_eq_of_lt (by have := hp.two_le; omega)]

lemma norm_cl_le (hp : 0 < p) (l : ℕ) (_hl : l < p) : ‖cl p l‖ ≤ p * Fq p ((2 * l + 1) % (2 * p)) := by
  apply geom_bound hp (2 * l + 1) _ (by omega)
  intro h; have := (dvd_mul_right 2 p).trans h; omega

/-- **Lemma 5.3** (from Weil's bound): sums of `C_p(k)` over odd `k` in an interval. -/
lemma sum_Cp_interval {Bk : ℝ} (hKl : KlBound p Bk) (hp : p.Prime) (hp2 : p ≠ 2) (A B : ℕ) (hB : B ≤ p) :
    |∑ k ∈ (Ico A B).filter Odd, Cp p k| ≤
      1 / p * Cp p 1 * (2 * p * (1 + Real.log p) * (Bk * (1 + 2 * (1 + Real.log p))) + p) := by
  have hp0 := hp.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hBk : 0 ≤ Bk := (norm_nonneg _).trans (hKl 1 (fun h => by
    have := Nat.le_of_dvd one_pos h; have := hp.two_le; omega) 0)
  set W := Bk * (1 + 2 * (1 + Real.log p)) with hW'
  have hW0 : 0 ≤ W := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ p by exact_mod_cast hp.one_lt.le); positivity
  set s := (range p).filter Odd with hs
  set K := (Ico A B).filter Odd with hK
  have hKmem : ∀ k ∈ K, Odd k ∧ k < p := by
    intro k hk; simp only [hK, mem_filter, mem_Ico] at hk; exact ⟨hk.2, by omega⟩
  have hsmem : ∀ n ∈ s, Odd n ∧ n < p := by
    intro n hn; simp only [hs, mem_filter, mem_range] at hn; exact ⟨hn.2, hn.1⟩
  -- complex form
  have hC : ((∑ k ∈ K, Cp p k : ℝ) : ℂ) = -(1 / (p : ℂ)) * ∑ n ∈ s, (Real.cot (Real.pi * n / (2 * p)) : ℂ) *
      ∑ l ∈ range p, cl p l * ∑ k ∈ K, zeta p ^ (((2 * l + 1) * n) * kbar p k) := by
    have e1 : ∀ k ∈ K, Cp p k = ∑ n ∈ s, (sigma p (n * kbar p k) : ℝ) * Real.cot (Real.pi * n / (2 * p)) := by
      intro k hk
      obtain ⟨hko, hkp⟩ := hKmem k hk
      exact Cp_sign_form hp hko (fun h => absurd (Nat.le_of_dvd hko.pos h) (by omega))
        (kbar_modEq hp hp2 hko hkp)
    rw [sum_congr rfl e1]
    push_cast
    simp_rw [sigma_expand hp0]
    rw [mul_sum, sum_comm]
    refine sum_congr rfl fun n _ => ?_
    simp only [mul_sum, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun l _ => ?_
    refine sum_congr rfl fun k _ => ?_
    rw [show (2 * l + 1) * (n * kbar p k) = ((2 * l + 1) * n) * kbar p k by ring]
    ring
  have habs : |∑ k ∈ K, Cp p k| = ‖((∑ k ∈ K, Cp p k : ℝ) : ℂ)‖ := (Complex.norm_real _).symm
  rw [habs, hC]
  -- per `(n, l)` bound
  have hinner : ∀ n ∈ s, ∀ l ∈ range p,
      ‖cl p l * ∑ k ∈ K, zeta p ^ (((2 * l + 1) * n) * kbar p k)‖ ≤
        p * Fq p ((2 * l + 1) % (2 * p)) * W + (if 2 * l + 1 = p then (p : ℝ) else 0) := by
    intro n hn l hl
    simp only [mem_range] at hl
    obtain ⟨hno, hnp⟩ := hsmem n hn
    rw [norm_mul]
    have hc := norm_cl_le hp0 l hl
    by_cases hr : 2 * l + 1 = p
    · rw [ite_eq_left hr]
      have hc1 : ‖cl p l‖ ≤ 1 := by
        refine hc.trans (le_of_eq ?_)
        rw [hr, Nat.mod_eq_of_lt (by omega)]; unfold Fq
        rw [show min p (2 * p - p) = p by omega]; field_simp
      have hk : ‖∑ k ∈ K, zeta p ^ (((2 * l + 1) * n) * kbar p k)‖ ≤ p := by
        refine (norm_sum_le _ _).trans ?_
        rw [sum_congr rfl (fun k _ => by rw [norm_pow, norm_zeta hp0, one_pow])]
        simp
        have : K.card ≤ p := by
          calc K.card ≤ (range p).card := card_le_card (fun k hk => by
                  simp only [mem_range]; exact (hKmem k hk).2)
            _ = p := card_range p
        exact_mod_cast this
      have : 0 ≤ (p : ℝ) * Fq p ((2 * l + 1) % (2 * p)) * W := by
        have := Fq_nonneg p ((2 * l + 1) % (2 * p)); positivity
      calc ‖cl p l‖ * ‖∑ k ∈ K, zeta p ^ (((2 * l + 1) * n) * kbar p k)‖ ≤ 1 * p := by gcongr
        _ ≤ _ := by linarith
    · rw [ite_eq_right hr, add_zero]
      have hnd : ¬ p ∣ (2 * l + 1) * n := by
        intro hd
        rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
        · obtain ⟨q, hq⟩ := h
          have : q < 2 := by
            by_contra hcq; have : p * 2 ≤ p * q := Nat.mul_le_mul_left _ (by omega); omega
          interval_cases q <;> omega
        · exact absurd (Nat.le_of_dvd hno.pos h) (by omega)
      have hw := weil_kbar hKl hp hp2 ((2 * l + 1) * n) hnd A B hB
      have := Fq_nonneg p ((2 * l + 1) % (2 * p))
      have : 0 ≤ (p : ℝ) * Fq p ((2 * l + 1) % (2 * p)) := by positivity
      gcongr
  have hsumF : ∑ l ∈ range p, Fq p ((2 * l + 1) % (2 * p)) ≤ 2 * (1 + Real.log p) := by
    refine (sum_inj_le hp0 (range p) (fun l => 2 * l + 1) ?_).trans ?_
    · intro a ha b hb hab
      simp only [coe_range, Set.mem_Iio] at ha hb
      simp only at hab
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hab
      omega
    · have := harmonic_le_one_add_log p; linarith
  have hite : ∑ l ∈ range p, (if 2 * l + 1 = p then (p : ℝ) else 0) ≤ p := by
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
    have : ((range p).filter (fun l => 2 * l + 1 = p)).card ≤ 1 := by
      apply Finset.card_le_one.2
      intro a ha b hb
      simp only [mem_filter] at ha hb
      omega
    have : (((range p).filter (fun l => 2 * l + 1 = p)).card : ℝ) ≤ 1 := by exact_mod_cast this
    nlinarith
  have hl_sum : ∀ n ∈ s, ‖∑ l ∈ range p, cl p l * ∑ k ∈ K, zeta p ^ (((2 * l + 1) * n) * kbar p k)‖ ≤
      2 * p * (1 + Real.log p) * W + p := by
    intro n hn
    refine (norm_sum_le _ _).trans ((sum_le_sum (hinner n hn)).trans ?_)
    rw [sum_add_distrib, ← sum_mul, ← mul_sum]
    have h1 : (p : ℝ) * ∑ l ∈ range p, Fq p ((2 * l + 1) % (2 * p)) ≤ p * (2 * (1 + Real.log p)) :=
      mul_le_mul_of_nonneg_left hsumF (by positivity)
    have h2 := mul_le_mul_of_nonneg_right h1 hW0
    linarith
  calc ‖-(1 / (p : ℂ)) * ∑ n ∈ s, (Real.cot (Real.pi * n / (2 * p)) : ℂ) *
        ∑ l ∈ range p, cl p l * ∑ k ∈ K, zeta p ^ (((2 * l + 1) * n) * kbar p k)‖
      ≤ 1 / p * ∑ n ∈ s, Real.cot (Real.pi * n / (2 * p)) * (2 * p * (1 + Real.log p) * W + p) := by
        rw [norm_mul, norm_neg, norm_div, norm_one, Complex.norm_natCast]
        have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
        have hpos : 0 ≤ 2 * (p : ℝ) * (1 + Real.log p) * W + p := by positivity
        gcongr
        refine (norm_sum_le _ _).trans (sum_le_sum fun n hn => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (cot_pos_of_lt (hsmem n hn).1.pos (hsmem n hn).2)]
        gcongr
        · exact (cot_pos_of_lt (hsmem n hn).1.pos (hsmem n hn).2).le
        · exact hl_sum n hn
    _ = 1 / p * Cp p 1 * (2 * p * (1 + Real.log p) * W + p) := by
        rw [Cp_one_eq, ← sum_mul]; ring

end Weil

section Final
open Real Finset
open Arxiv.«2501.03234» Recip

lemma telescope_Ico (w : ℕ → ℝ) (K n : ℕ) :
    ∑ i ∈ Ico K (K + n), (w i - w (i + 1)) = w K - w (K + n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [← add_assoc, sum_Ico_succ_top (by omega), ih]; ring

/-- Abel summation with a nonincreasing nonnegative weight. -/
lemma abel_bound {a w : ℕ → ℝ} {K P : ℕ} (hKP : K < P)
    (hw : ∀ i, K ≤ i → i + 1 < P → w (i + 1) ≤ w i) (hw0 : 0 ≤ w (P - 1)) {M : ℝ}
    (hM : ∀ t, K ≤ t → t ≤ P → |∑ i ∈ Ico K t, a i| ≤ M) :
    |∑ i ∈ Ico K P, w i * a i| ≤ w K * M := by
  set g : ℕ → ℝ := fun i => if K ≤ i then a i else 0 with hg
  have hG : ∀ t, K ≤ t → ∑ i ∈ range t, g i = ∑ i ∈ Ico K t, a i := by
    intro t ht
    rw [← sum_range_add_sum_Ico _ ht]
    rw [sum_eq_zero (fun i hi => by simp only [mem_range] at hi; simp [hg]; omega), zero_add]
    exact sum_congr rfl fun i hi => by simp only [mem_Ico] at hi; simp [hg, hi.1]
  have hsum : ∑ i ∈ Ico K P, w i * a i = ∑ i ∈ Ico K P, w i • g i :=
    sum_congr rfl fun i hi => by simp only [mem_Ico] at hi; simp [hg, hi.1]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM K le_rfl hKP.le)
  rw [hsum, sum_Ico_by_parts w g hKP, hG K le_rfl, hG P hKP.le]
  simp only [Ico_self, sum_empty, smul_eq_mul, mul_zero, sub_zero]
  have hb : ∀ i ∈ Ico K (P - 1), |(w (i + 1) - w i) * ∑ j ∈ range (i + 1), g j| ≤ (w i - w (i + 1)) * M := by
    intro i hi
    simp only [mem_Ico] at hi
    rw [hG (i + 1) (by omega), abs_mul, abs_of_nonpos (by linarith [hw i hi.1 (by omega)])]
    have := hM (i + 1) (by omega) (by omega)
    nlinarith [hw i hi.1 (by omega)]
  have htel := telescope_Ico w K (P - 1 - K)
  rw [show K + (P - 1 - K) = P - 1 by omega] at htel
  calc |w (P - 1) * ∑ i ∈ Ico K P, a i - ∑ i ∈ Ico K (P - 1), (w (i + 1) - w i) * ∑ j ∈ range (i + 1), g j|
      ≤ |w (P - 1) * ∑ i ∈ Ico K P, a i| + |∑ i ∈ Ico K (P - 1), (w (i + 1) - w i) * ∑ j ∈ range (i + 1), g j| :=
        abs_sub _ _
    _ ≤ w (P - 1) * M + ∑ i ∈ Ico K (P - 1), (w i - w (i + 1)) * M := by
        gcongr
        · rw [abs_mul, abs_of_nonneg hw0]; gcongr; exact hM P hKP.le le_rfl
        · exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum hb)
    _ = w K * M := by rw [← sum_mul, htel]; ring

lemma cot_anti {p k : ℕ} (hk0 : 0 < k) (hkp : k + 1 < p) :
    Real.cot (π * (k + 1 : ℕ) / (2 * p)) ≤ Real.cot (π * k / (2 * p)) := by
  have hpi := Real.pi_pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hk1 : ((k + 1 : ℕ) : ℝ) < p := by exact_mod_cast hkp
  have h0 : 0 < π * k / (2 * p) := by positivity
  have h1 : π * k / (2 * p) < π * (k + 1 : ℕ) / (2 * p) := by
    apply div_lt_div_of_pos_right _ (by positivity); push_cast; nlinarith
  have h2 : π * (k + 1 : ℕ) / (2 * p) < π / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have ht := Real.tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith) h2 h1
  have htp : 0 < Real.tan (π * k / (2 * p)) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two h0 (by linarith)
  rw [← Real.tan_inv_eq_cot, ← Real.tan_inv_eq_cot]
  exact (inv_lt_inv₀ (htp.trans ht) htp).2 ht |>.le

lemma eventually_facts : ∀ᶠ p : ℕ in Filter.atTop, 3 ≤ (p : ℝ) ∧ 6 ≤ (p : ℝ) ^ ((3 : ℝ) / 4) ∧
    Real.log p ^ 5 ≤ π / 12 * (p : ℝ) ^ ((1 : ℝ) / 4) := by
  have h1 : ∀ᶠ y : ℝ in Filter.atTop, 3 ≤ y := Filter.eventually_ge_atTop 3
  have h2 : ∀ᶠ y : ℝ in Filter.atTop, 6 ≤ y ^ ((3 : ℝ) / 4) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).eventually_ge_atTop 6
  have h3 := (isLittleO_log_rpow_rpow_atTop (5 : ℝ) (by norm_num : (0 : ℝ) < 1 / 4)).bound
    (show (0 : ℝ) < π / 12 by positivity)
  have h : ∀ᶠ y : ℝ in Filter.atTop, 3 ≤ y ∧ 6 ≤ y ^ ((3 : ℝ) / 4) ∧
      Real.log y ^ 5 ≤ π / 12 * y ^ ((1 : ℝ) / 4) := by
    filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
    refine ⟨hy1, hy2, ?_⟩
    have hl : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hl _), Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _),
      show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hy3
    exact hy3
  exact tendsto_natCast_atTop_atTop.eventually h

/-- `K = ⌊p^{3/4} (log p)^4⌋`. -/
noncomputable def KW34 (p : ℕ) : ℕ := ⌊(p : ℝ) ^ ((3 : ℝ) / 4) * Real.log p ^ 4⌋₊

/-- Weak form of Theorem B(ii) with cut-off `K = p^{3/4} (log p)^4`. -/
def HBweak34 : Prop :=
  ∃ c C : ℝ, ∀ᶠ p in Filter.atTop, p.Prime →
    |(S p : ℝ) - p / 2 * Real.log p - c * p -
      4 * p / π * ∑ k ∈ (Ico 3 (KW34 p)).filter Odd, Fsum k p / (k : ℝ) ^ 2| ≤ C * p

lemma Fsum_abs_bound {k : ℕ} (hk : Odd k) (r : ℤ) : |Fsum k r| ≤ k / π * (Real.log k + 2) := by
  refine (Fsum_abs_le hk r).trans ?_
  rw [Fsum_one_eq_Cp hk]; exact Cp_one_le hk

lemma sum_inv_Ico_le (K p : ℕ) : ∑ k ∈ (Ico K p).filter Odd, 1 / (k : ℝ) ≤ 1 + Real.log p := by
  calc ∑ k ∈ (Ico K p).filter Odd, 1 / (k : ℝ) ≤ ∑ k ∈ range (p + 1), 1 / (k : ℝ) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro k hk; simp only [mem_filter, mem_Ico, mem_range] at hk ⊢; omega
        · intro k _ _; positivity
    _ = harmonic p := (harmonic_cast p).symm
    _ ≤ 1 + Real.log p := harmonic_le_one_add_log p

/-- Small `k`: replacing `2 cot(πk/2p)/k` by `4p/(πk²)`. -/
lemma small_part {p K : ℕ} (hp : p.Prime) (hKp : K ≤ p) :
    |2 * ∑ k ∈ (range K).filter Odd, Real.cot (π * k / (2 * p)) * Fsum k p / k -
      4 * p / π * ∑ k ∈ (Ico 3 K).filter Odd, Fsum k p / (k : ℝ) ^ 2| ≤
        4 / π * (Real.log p + 2) * K := by
  have hpi := Real.pi_pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hT : ∑ k ∈ (Ico 3 K).filter Odd, Fsum k p / (k : ℝ) ^ 2 =
      ∑ k ∈ (range K).filter Odd, Fsum k p / (k : ℝ) ^ 2 := by
    apply sum_subset
    · intro k hk; simp only [mem_filter, mem_Ico, mem_range] at hk ⊢; exact ⟨hk.1.2, hk.2⟩
    · intro k hk hk'
      simp only [mem_filter, mem_Ico, mem_range, not_and] at hk hk'
      have : k = 1 := by
        obtain ⟨t, rfl⟩ := hk.2
        by_contra h; exact hk' (by omega) ⟨t, rfl⟩
      subst this
      have : Fsum 1 p = 0 := by unfold Fsum; simp
      rw [this, zero_div]
  rw [hT, mul_sum, mul_sum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ (range K).filter Odd, |2 * (Real.cot (π * k / (2 * p)) * Fsum k p / k) -
        4 * p / π * (Fsum k p / (k : ℝ) ^ 2)|
      ≤ ∑ k ∈ (range K).filter Odd, 4 / π * (Real.log p + 2) := by
        refine sum_le_sum fun k hk => ?_
        simp only [mem_filter, mem_range] at hk
        have hk0 : 0 < k := hk.2.pos
        have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
        have hkp : k < p := by omega
        obtain ⟨hd0, hd2⟩ := cot_near (p := p) hk0 hkp
        have hF := Fsum_abs_bound hk.2 (p : ℤ)
        have hlk : Real.log k ≤ Real.log p := Real.log_le_log hkR (by exact_mod_cast hkp.le)
        have e : 2 * (Real.cot (π * k / (2 * p)) * Fsum k p / k) - 4 * p / π * (Fsum k p / (k : ℝ) ^ 2) =
            -(2 * Fsum k p / k) * (2 * p / (π * k) - Real.cot (π * k / (2 * p))) := by
          field_simp; ring
        rw [e, abs_mul, abs_neg, abs_of_nonneg hd0, abs_div, abs_mul, abs_two,
          abs_of_pos hkR]
        calc 2 * |Fsum k p| / k * (2 * p / (π * k) - Real.cot (π * k / (2 * p)))
            ≤ 2 * (k / π * (Real.log k + 2)) / k * 2 := by gcongr
          _ = 4 / π * (Real.log k + 2) := by field_simp; ring
          _ ≤ 4 / π * (Real.log p + 2) := by gcongr
    _ ≤ 4 / π * (Real.log p + 2) * K := by
        rw [sum_const, nsmul_eq_mul, mul_comm]
        have hl := Real.log_nonneg (show (1 : ℝ) ≤ p by exact_mod_cast hp.one_lt.le)
        have : ((range K).filter Odd).card ≤ K := (card_filter_le _ _).trans (card_range K).le
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast this) (by positivity)

/-- Splitting `Φ` at `K` and rewriting the large part with Lemma 4.1. -/
lemma Phi_split {p K : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hKp : K ≤ p) :
    Phi p = 2 * ∑ k ∈ (range K).filter Odd, Real.cot (π * k / (2 * p)) * Fsum k p / k +
      (2 / p * ∑ k ∈ (Ico K p).filter Odd, Real.cot (π * k / (2 * p)) * Cp p k -
        2 / p * ∑ k ∈ (Ico K p).filter Odd, Real.cot (π * k / (2 * p)) * Ifun ((k : ℝ) / p)) := by
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  unfold Phi
  rw [sum_filter, ← sum_range_add_sum_Ico _ hKp, ← sum_filter, ← sum_filter, mul_add]
  congr 1
  rw [mul_sum, mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun k hk => ?_
  simp only [mem_filter, mem_Ico] at hk
  have hk0 : 0 < k := hk.2.pos
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
  rw [reciprocity hpo hk.2 (coprime_of_lt hp hk0 hk.1.2)]
  field_simp
  ring

lemma large_I {p K : ℕ} (hp : p.Prime) (hK1 : 1 ≤ K) :
    |2 / p * ∑ k ∈ (Ico K p).filter Odd, Real.cot (π * k / (2 * p)) * Ifun ((k : ℝ) / p)| ≤
      2 * (p : ℝ) ^ 2 * (1 + Real.log p) / (K : ℝ) ^ 2 := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hterm : ∀ k ∈ (Ico K p).filter Odd, 0 ≤ Real.cot (π * k / (2 * p)) * Ifun ((k : ℝ) / p) ∧
      Real.cot (π * k / (2 * p)) * Ifun ((k : ℝ) / p) ≤ (p : ℝ) ^ 3 / (K : ℝ) ^ 2 * (1 / k) := by
    intro k hk
    simp only [mem_filter, mem_Ico] at hk
    have hk0 : 0 < k := by omega
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
    have hKk : (K : ℝ) ≤ k := by exact_mod_cast hk.1.1
    have hkp : (k : ℝ) < p := by exact_mod_cast hk.1.2
    have hl0 : 0 < (k : ℝ) / p := by positivity
    have hl1 : (k : ℝ) / p ≤ 1 := by rw [div_le_one hpR]; linarith
    have hc0 := (cot_pos_of_lt hk0 hk.1.2).le
    obtain ⟨hd0, _⟩ := cot_near (p := p) hk0 hk.1.2
    have hI0 := Ifun_nonneg hl0 hl1
    have hI := Ifun_le hl0 hl1
    have hc : Real.cot (π * k / (2 * p)) ≤ p / k := by
      have : 2 * (p : ℝ) / (π * k) ≤ p / k := by
        rw [div_le_div_iff₀ (by positivity) hkR]
        nlinarith [mul_pos (mul_pos hpR hkR) (by linarith : (0 : ℝ) < π - 2)]
      linarith
    have hI' : Ifun ((k : ℝ) / p) ≤ (p : ℝ) ^ 2 / (k : ℝ) ^ 2 := by
      refine hI.trans ?_
      rw [show 2 / (π * ((k : ℝ) / p) ^ 2) = 2 / π * ((p : ℝ) ^ 2 / (k : ℝ) ^ 2) by field_simp]
      have h2 : 2 / π ≤ 1 := by rw [div_le_one hpi]; linarith
      exact mul_le_of_le_one_left (by positivity) h2
    refine ⟨mul_nonneg hc0 hI0, ?_⟩
    calc Real.cot (π * k / (2 * p)) * Ifun ((k : ℝ) / p) ≤ p / k * ((p : ℝ) ^ 2 / (k : ℝ) ^ 2) := by
          gcongr
      _ = (p : ℝ) ^ 3 / ((k : ℝ) ^ 2) * (1 / k) := by field_simp
      _ ≤ (p : ℝ) ^ 3 / (K : ℝ) ^ 2 * (1 / k) := by gcongr
  have hsum0 : 0 ≤ ∑ k ∈ (Ico K p).filter Odd, Real.cot (π * k / (2 * p)) * Ifun ((k : ℝ) / p) :=
    sum_nonneg fun k hk => (hterm k hk).1
  rw [abs_of_nonneg (by positivity)]
  calc 2 / p * ∑ k ∈ (Ico K p).filter Odd, Real.cot (π * k / (2 * p)) * Ifun ((k : ℝ) / p)
      ≤ 2 / p * ∑ k ∈ (Ico K p).filter Odd, (p : ℝ) ^ 3 / (K : ℝ) ^ 2 * (1 / k) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun k hk => (hterm k hk).2) (by positivity)
    _ = 2 / p * ((p : ℝ) ^ 3 / (K : ℝ) ^ 2) * ∑ k ∈ (Ico K p).filter Odd, 1 / (k : ℝ) := by
        rw [← mul_sum]; ring
    _ ≤ 2 / p * ((p : ℝ) ^ 3 / (K : ℝ) ^ 2) * (1 + Real.log p) := by
        gcongr; exact sum_inv_Ico_le K p
    _ = 2 * (p : ℝ) ^ 2 * (1 + Real.log p) / (K : ℝ) ^ 2 := by field_simp

lemma large_C (hK : HK34) {p K : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK1 : 1 ≤ K) (hKp : K < p) :
    |2 / p * ∑ k ∈ (Ico K p).filter Odd, Real.cot (π * k / (2 * p)) * Cp p k| ≤
      2 / p * (2 * p / (π * K)) * (1 / p * Cp p 1 * (2 * p * (1 + Real.log p) *
        (2 * (p : ℝ) ^ ((3 : ℝ) / 4) * (1 + 2 * (1 + Real.log p))) + p)) := by
  have hpi := Real.pi_pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  set M := 1 / p * Cp p 1 * (2 * p * (1 + Real.log p) *
        (2 * (p : ℝ) ^ ((3 : ℝ) / 4) * (1 + 2 * (1 + Real.log p))) + p) with hM
  set a : ℕ → ℝ := fun k => if Odd k then Cp p k else 0 with ha
  have hsum : ∑ k ∈ (Ico K p).filter Odd, Real.cot (π * k / (2 * p)) * Cp p k =
      ∑ k ∈ Ico K p, Real.cot (π * k / (2 * p)) * a k := by
    rw [sum_filter]; refine sum_congr rfl fun k _ => ?_; simp only [ha, mul_ite, mul_zero]
  have hab := abel_bound (a := a) (w := fun k => Real.cot (π * k / (2 * p))) hKp
    (fun i hi hi2 => cot_anti (by omega) hi2)
    (cot_pos_of_lt (show 0 < p - 1 by have := hp.two_le; omega) (by omega)).le
    (M := M) (fun t ht htp => by
      have : ∑ i ∈ Ico K t, a i = ∑ k ∈ (Ico K t).filter Odd, Cp p k := by rw [sum_filter]
      rw [this]; exact sum_Cp_interval (KlBound_of_HK34 hK hp) hp hp2 K t htp)
  have hwK : Real.cot (π * K / (2 * p)) ≤ 2 * p / (π * K) := by
    have := (cot_near (p := p) (by omega) hKp).1; linarith
  have hM0 : 0 ≤ M := by
    have hlp := Real.log_nonneg (show (1 : ℝ) ≤ p by exact_mod_cast hp.one_lt.le)
    have := Cp_one_nonneg p
    rw [hM]; positivity
  rw [hsum, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / p)]
  calc 2 / p * |∑ k ∈ Ico K p, Real.cot (π * k / (2 * p)) * a k| ≤ 2 / p * (Real.cot (π * K / (2 * p)) * M) := by
        gcongr
    _ ≤ 2 / p * (2 * p / (π * K) * M) := by gcongr
    _ = _ := by ring

lemma arithM {p x L C1 : ℝ} (hp : 0 < p) (hx1 : 1 ≤ x) (hL0 : 0 ≤ L) (_hC0 : 0 ≤ C1)
    (hC : C1 ≤ p / π * (L + 2)) :
    1 / p * C1 * (2 * p * (1 + L) * (2 * x * (1 + 2 * (1 + L))) + p) ≤ 9 * p * x * (L + 2) ^ 3 := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hinner : 2 * p * (1 + L) * (2 * x * (1 + 2 * (1 + L))) + p ≤ 9 * p * x * (L + 2) ^ 2 := by
    have h1 : (1 + L) * (1 + 2 * (1 + L)) ≤ 2 * (L + 2) ^ 2 := by nlinarith
    have h2 : p ≤ p * x * (L + 2) ^ 2 := by
      have : 1 ≤ x * (L + 2) ^ 2 := by nlinarith
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 4 * p * x)]
  calc 1 / p * C1 * (2 * p * (1 + L) * (2 * x * (1 + 2 * (1 + L))) + p)
      ≤ 1 / p * (p / π * (L + 2)) * (9 * p * x * (L + 2) ^ 2) := by
        apply mul_le_mul _ hinner (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hC (by positivity)
    _ = 9 * p * x * (L + 2) ^ 3 / π := by field_simp
    _ ≤ 9 * p * x * (L + 2) ^ 3 := by
        rw [div_le_iff₀ hpi]; nlinarith [show (0 : ℝ) ≤ 9 * p * x * (L + 2) ^ 3 by positivity]

lemma arithC {p x L K M : ℝ} (hp : 0 < p) (hx1 : 1 ≤ x) (hL1 : 1 ≤ L) (hK : x * L ^ 4 / 2 ≤ K)
    (hM : M ≤ 9 * p * x * (L + 2) ^ 3) :
    2 / p * (2 * p / (π * K)) * M ≤ 648 * p := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hL4 : 1 ≤ L ^ 4 := one_le_pow₀ hL1
  have hKpos : 0 < K := by nlinarith
  have hL3 : (L + 2) ^ 3 ≤ 27 * L ^ 4 := by
    have : L + 2 ≤ 3 * L := by linarith
    have h3 : (L + 2) ^ 3 ≤ (3 * L) ^ 3 := by gcongr
    nlinarith
  have hM' : 2 / p * (2 * p / (π * K)) * M ≤ 2 / p * (2 * p / (π * K)) * (9 * p * x * (L + 2) ^ 3) :=
    mul_le_mul_of_nonneg_left hM (by positivity)
  refine hM'.trans ?_
  rw [show 2 / p * (2 * p / (π * K)) * (9 * p * x * (L + 2) ^ 3) = 36 * p * x * (L + 2) ^ 3 / (π * K) by
    field_simp; norm_num]
  rw [div_le_iff₀ (by positivity)]
  have hπK : x * L ^ 4 / 2 * 3 ≤ π * K := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hL3 (by positivity : (0 : ℝ) ≤ 36 * p * x)]

lemma arithI {p x L K : ℝ} (hp : 0 < p) (hx0 : 0 ≤ x) (hx2 : p ≤ x ^ 2) (hL1 : 1 ≤ L) (hK : x * L ^ 4 / 2 ≤ K)
    (hK0 : 0 < K) : 2 * p ^ 2 * (1 + L) / K ^ 2 ≤ 16 * p := by
  rw [div_le_iff₀ (by positivity)]
  have hK2' : x ^ 2 * L ^ 8 / 4 ≤ K ^ 2 := by
    have h0 : 0 ≤ x * L ^ 4 / 2 := by positivity
    have : (x * L ^ 4 / 2) ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ h0 hK 2
    nlinarith
  have hL8 : 1 + L ≤ 2 * L ^ 8 := by
    have : L ≤ L ^ 8 := by
      calc L = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ 8 := pow_le_pow_right₀ hL1 (by norm_num)
    linarith
  have h1 : p * L ^ 8 / 4 ≤ K ^ 2 := by
    have := mul_le_mul_of_nonneg_right hx2 (by positivity : (0 : ℝ) ≤ L ^ 8 / 4)
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hL8 (by positivity : (0 : ℝ) ≤ 2 * p ^ 2)]

/-- **Theorem B(ii), weak form**, from Kloosterman's `p^{3/4}` bound. -/
theorem HBweak34_of_HK34 (hK : HK34) : HBweak34 := by
  obtain ⟨Cψ, hψ⟩ := Psi_bound
  refine ⟨0, Cψ + 1000, ?_⟩
  filter_upwards [eventually_facts] with p hfacts hp
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
  have e : (S p : ℝ) - p / 2 * L - 0 * p - T =
      (Psi p - p / 2 * L) + (Φs - T) + Cpart - Ipart := by rw [hS, hΦ]; ring
  rw [e]
  have b1 : |Psi p - p / 2 * L| ≤ Cψ * p := hψ p hp3n (hp.odd_of_ne_two hp2)
  have b2 : |Φs - T| ≤ p := by
    have := small_part hp hKp.le
    have h' : 4 / π * (L + 2) * K ≤ 4 / π * (L + 2) * y := by gcongr
    linarith
  have b3 : |Cpart| ≤ 648 * p := by
    have hC := large_C hK hp hp2 (by omega) hKp
    have hMb := arithM hpR hx1 (by linarith) (Cp_one_nonneg p) (Cp_one_le (hp.odd_of_ne_two hp2))
    exact hC.trans (arithC hpR hx1 hL1 (by rw [← hydef]; exact hK2) hMb)
  have b4 : |Ipart| ≤ 16 * p :=
    (large_I hp (K := K) (by omega)).trans (arithI hpR (by linarith) hx2 hL1 (by rw [← hydef]; exact hK2) (by linarith))
  calc |Psi p - p / 2 * L + (Φs - T) + Cpart - Ipart|
      ≤ |Psi p - p / 2 * L| + |Φs - T| + |Cpart| + |Ipart| := by
        have h1 := abs_sub (Psi p - p / 2 * L + (Φs - T) + Cpart) Ipart
        have h2 := abs_add_le (Psi p - p / 2 * L + (Φs - T)) Cpart
        have h3 := abs_add_le (Psi p - p / 2 * L) (Φs - T)
        linarith
    _ ≤ Cψ * p + p + 648 * p + 16 * p := by linarith
    _ ≤ (Cψ + 1000) * p := by nlinarith

end Final

#print axioms S_eq_Psi_Phi
#print axioms I_asymp
#print axioms Psi_bound
#print axioms weil_kbar
#print axioms sum_Cp_interval
#print axioms HBweak34_of_HK34

end TheoremB
