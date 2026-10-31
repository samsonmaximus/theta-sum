import ThetaSum.Rankin
import ThetaSum.Counting

/-
The recursion in the proof of Theorem D: the base case (Lemma 7.1) at every level `j`, and the
recursive step (Lemma 7.2 with `y = (T_j R)^{1/u}`), for an abstract set of parameters.
Here `T_j = e^κ / 2^j`, `L = log q`, and progressions are admissible with `X = q²`.
-/

open Finset

namespace ThetaSum

/-- Admissible progression `{a + q t : t ∈ I}` (with `X = q²`). -/
def Adm (q : ℕ) (a : ℤ) (I : Finset ℤ) : Prop :=
  Int.gcd a q = 1 ∧ ∀ t ∈ I, a + q * t ≠ 0 ∧ ((a + q * t).natAbs : ℝ) ≤ (q : ℝ) ^ 2

lemma log_Tj (κ : ℝ) (j : ℕ) : Real.log (Real.exp κ / 2 ^ j) = κ - j * Real.log 2 := by
  rw [Real.log_div (Real.exp_pos κ).ne' (by positivity), Real.log_exp, Real.log_pow]

lemma Tj_pos (κ : ℝ) (j : ℕ) : 0 < Real.exp κ / 2 ^ j := by positivity

lemma log_natAbs_le {q : ℕ} {a t : ℤ} (h : a + q * t ≠ 0) (h2 : ((a + q * t).natAbs : ℝ) ≤ (q : ℝ) ^ 2) :
    Real.log ((a + q * t).natAbs) ≤ 2 * Real.log q := by
  have hpos : (0 : ℝ) < (a + q * t).natAbs := by
    exact_mod_cast Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr h)
  calc Real.log ((a + q * t).natAbs) ≤ Real.log ((q : ℝ) ^ 2) := Real.log_le_log hpos h2
    _ = 2 * Real.log q := by rw [Real.log_pow]; norm_num

/-- Base case at level `j ≤ J`: if `log R ≤ βκ` then
`Δ(A; T_j R) ≤ exp(βκ - ακ + αJ log 2) · exp(4 L^α (1/α + 2))`. -/
theorem base_level (q : ℕ) {κ α β : ℝ} (J j : ℕ) (hj : j ≤ J) (hα : 0 < α) (hα2 : α ≤ 1 / 2)
    (hL : Real.exp 1 ≤ Real.log q) (a t0 : ℤ) (len : ℕ) (R : ℝ)
    (hA : Adm q a (Ico t0 (t0 + len))) (hlen : (len : ℝ) ≤ R) (hR : 1 ≤ R)
    (hRb : Real.log R ≤ β * κ) :
    Delta q a (Ico t0 (t0 + len)) (Real.exp κ / 2 ^ j * R) ≤
      Real.exp (β * κ - α * κ + α * J * Real.log 2) *
        Real.exp (4 * (Real.log q ^ α * (1 / α + 2))) := by
  set Y := Real.exp κ / 2 ^ j * R
  have hR0 : 0 < R := by linarith
  have hY : 0 < Y := mul_pos (Tj_pos κ j) hR0
  have h1 := rankin_delta q a t0 len hY hα hα2 hL
    (fun t ht => ⟨(hA.2 t ht).1, log_natAbs_le (hA.2 t ht).1 (hA.2 t ht).2⟩)
  refine h1.trans ?_
  set Pb := Real.exp (4 * (Real.log q ^ α * (1 / α + 2)))
  have hlogY : Real.log Y = κ - j * Real.log 2 + Real.log R := by
    simp only [Y]; rw [Real.log_mul (Tj_pos κ j).ne' hR0.ne', log_Tj]
  have hYa : Y ^ (-α) ≤ Real.exp (-α * κ + α * J * Real.log 2) := by
    rw [Real.rpow_def_of_pos hY, hlogY]
    apply Real.exp_le_exp.mpr
    have hjJ : (j : ℝ) ≤ J := by exact_mod_cast hj
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlR : 0 ≤ Real.log R := Real.log_nonneg hR
    have e : (κ - j * Real.log 2 + Real.log R) * -α =
        -(α * κ) + α * (j * Real.log 2) - α * Real.log R := by ring
    have h3 : α * (j * Real.log 2) ≤ α * (J * Real.log 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hjJ hl2) hα.le
    have h4 : 0 ≤ α * Real.log R := mul_nonneg hα.le hlR
    rw [e]; nlinarith
  have hRe : R ≤ Real.exp (β * κ) := by
    rw [← Real.exp_log hR0]; exact Real.exp_le_exp.mpr hRb
  calc (len : ℝ) * (Y ^ (-α) * Pb) ≤ R * (Real.exp (-α * κ + α * J * Real.log 2) * Pb) := by
        apply mul_le_mul hlen _ (by positivity) hR0.le
        exact mul_le_mul_of_nonneg_right hYa (by positivity)
    _ ≤ Real.exp (β * κ) * (Real.exp (-α * κ + α * J * Real.log 2) * Pb) := by
        apply mul_le_mul_of_nonneg_right hRe (by positivity)
    _ = Real.exp (β * κ - α * κ + α * J * Real.log 2) * Pb := by
        rw [← mul_assoc, ← Real.exp_add]; ring_nf

/-- The recursive step at level `j`. -/
theorem rec_step (q : ℕ) {κ u β b xj xj1 : ℝ} (j : ℕ)
    (hL1 : 1 ≤ Real.log (Real.log q + 1)) (hL0 : 0 ≤ Real.log q)
    (hu : 1 ≤ u) (huβ : 1 ≤ (u - 1) * β) (hκ0 : 0 ≤ κ)
    (hj : (j : ℝ) * Real.log 2 ≤ κ / 2)
    (hθ : 4 * Real.log (Real.log q + 1) * u ≤ κ)
    (hx : Real.log 2 + (κ + xj) / u ≤ xj1) (hb : 0 ≤ b)
    (IH : ∀ (a' : ℤ) (m : ℕ) (R' : ℝ), Adm q a' (Ico 0 m) → (m : ℝ) ≤ R' → 1 ≤ R' →
      Real.log R' ≤ xj1 → Delta q a' (Ico 0 m) (Real.exp κ / 2 ^ (j + 1) * R') ≤ b)
    (a t0 : ℤ) (len : ℕ) (R : ℝ) (hA : Adm q a (Ico t0 (t0 + len))) (hlen : (len : ℝ) ≤ R)
    (hR : 1 ≤ R) (hRb : β * κ < Real.log R) (hRx : Real.log R ≤ xj) :
    Delta q a (Ico t0 (t0 + len)) (Real.exp κ / 2 ^ j * R) ≤
      8 * (1 + xj) * 2 ^ j * Real.exp (-(κ / 2)) + (1 + xj) * b := by
  classical
  set L := Real.log q
  set Tj := Real.exp κ / 2 ^ j
  have hR0 : 0 < R := by linarith
  have hlR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hu0 : 0 < u := by linarith
  have hlogTj : Real.log Tj = κ - j * Real.log 2 := log_Tj κ j
  have hj0 : (0 : ℝ) ≤ j * Real.log 2 := by positivity
  have hTj0 : 0 < Tj := Tj_pos κ j
  have hTj1 : 1 ≤ Tj := by
    rw [← Real.exp_log hTj0, hlogTj]; exact Real.one_le_exp (by linarith)
  set P := Tj * R
  have hP0 : 0 < P := mul_pos hTj0 hR0
  have hP1 : 1 ≤ P := by nlinarith
  have hlogP : Real.log P = Real.log Tj + Real.log R := Real.log_mul hTj0.ne' hR0.ne'
  set y := P ^ (1 / u)
  have hy0 : 0 < y := Real.rpow_pos_of_pos hP0 _
  have hlogy : Real.log y = Real.log P / u := by
    rw [Real.log_rpow hP0]; ring
  have hlogy2 : 2 * Real.log (L + 1) ≤ Real.log y := by
    rw [hlogy, le_div_iff₀ hu0]
    nlinarith
  have hlogy2' : 2 ≤ Real.log y := by linarith
  have hy2 : 2 ≤ y := by
    rw [← Real.exp_log hy0]; linarith [Real.add_one_le_exp (Real.log y)]
  have hyR : y ≤ R := by
    rw [← Real.exp_log hy0, ← Real.exp_log hR0]
    apply Real.exp_le_exp.mpr
    rw [hlogy, div_le_iff₀ hu0, hlogP, hlogTj]
    have h1 : κ ≤ (u - 1) * β * κ := by nlinarith
    have h2 : (u - 1) * (β * κ) ≤ (u - 1) * Real.log R :=
      mul_le_mul_of_nonneg_left hRb.le (by linarith)
    nlinarith
  obtain ⟨J', hJ'⟩ := pow_unbounded_of_one_lt ((q : ℝ) ^ 2) (by norm_num : (1 : ℝ) < 2)
  have hJ : (q : ℝ) ^ 2 ≤ 2 ^ J' * (Tj * R) := by
    have : (2 : ℝ) ^ J' ≤ 2 ^ J' * P := le_mul_of_one_le_right (by positivity) hP1
    linarith
  have hstep := one_step_harmonic q a t0 len J' hA.1 hA.2 hlen hTj1 hy2 hyR hJ
  refine hstep.trans (add_le_add ?_ ?_)
  · -- first term
    set θ := Real.log ((Ny ((q : ℝ) ^ 2) y : ℝ) + 1) / Real.log y
    have hNy : (Ny ((q : ℝ) ^ 2) y : ℝ) ≤ L := by
      unfold Ny
      have hX : Real.log ((q : ℝ) ^ 2) = 2 * L := by rw [Real.log_pow]; push_cast; ring
      rw [hX]
      have hpos : 0 ≤ 2 * L / Real.log y := div_nonneg (by linarith) (by linarith)
      refine (Nat.floor_le hpos).trans ?_
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have hθ1 : θ ≤ Real.log (L + 1) / Real.log y := by
      apply div_le_div_of_nonneg_right _ (by linarith)
      exact Real.log_le_log (by positivity) (by linarith)
    have hθhalf : θ ≤ 1 / 2 := by
      refine hθ1.trans ?_
      rw [div_le_iff₀ (by linarith)]; linarith
    have hsum := dyadic_sum_le ((q : ℝ) ^ 2) (by linarith : (1 : ℝ) < y) hP1 hθhalf J'
    have hlog2P : Real.log (2 * P) ≤ 2 * u * Real.log y := by
      rw [Real.log_mul (by norm_num) hP0.ne']
      have : Real.log P = u * Real.log y := by rw [hlogy]; field_simp
      have hy1 : Real.log y ≤ u * Real.log y := le_mul_of_one_le_left (by linarith) hu
      nlinarith
    have hpow : (2 * P) ^ θ ≤ Real.exp (κ / 2) := by
      rw [Real.rpow_def_of_pos (by positivity)]
      apply Real.exp_le_exp.mpr
      have hθ0 : 0 ≤ θ := div_nonneg (Real.log_nonneg (by
        have := (Ny ((q : ℝ) ^ 2) y).cast_nonneg (α := ℝ); linarith)) (by linarith)
      have hl2P : 0 ≤ Real.log (2 * P) := Real.log_nonneg (by linarith)
      calc Real.log (2 * P) * θ ≤ (2 * u * Real.log y) * (Real.log (L + 1) / Real.log y) :=
            mul_le_mul hlog2P hθ1 hθ0 (by positivity)
        _ = 2 * u * Real.log (L + 1) := by field_simp
        _ ≤ κ / 2 := by linarith
    have hcoef : 0 ≤ 2 * (1 + Real.log R) / Tj := by positivity
    calc 2 * (1 + Real.log R) / Tj *
          ∑ j ∈ range J', (1 / 2 : ℝ) ^ j * G ((q : ℝ) ^ 2) y (2 ^ (j + 1) * (Tj * R))
        ≤ 2 * (1 + Real.log R) / Tj * (4 * Real.exp (κ / 2)) :=
          mul_le_mul_of_nonneg_left (hsum.trans (by linarith)) hcoef
      _ ≤ 2 * (1 + xj) / Tj * (4 * Real.exp (κ / 2)) := by gcongr
      _ = 8 * (1 + xj) * 2 ^ j * Real.exp (-(κ / 2)) := by
          simp only [Tj]
          have : Real.exp (κ / 2) = Real.exp κ * Real.exp (-(κ / 2)) := by
            rw [← Real.exp_add]; ring_nf
          rw [this]
          field_simp
          ring
  · -- second term
    have hSb : ∀ s ∈ Sset R y, DeltaSub q a (Ico t0 (t0 + len)) s (Tj * R / s) ≤ b := by
      intro s hs
      by_cases hne : ((Ico t0 (t0 + len)).filter (fun t : ℤ => (s : ℤ) ∣ a + q * t)).Nonempty
      · obtain ⟨a', m, hc, hm, hv, hD⟩ :=
          admissible_of_mem_S q a t0 len s hA.1 hA.2 hlen hs hne
        rw [hD]
        have hs' := hs
        simp only [Sset, mem_filter, mem_Icc] at hs'
        have hs0 : (0 : ℝ) < s := by exact_mod_cast hs'.1.1
        have hsR : (s : ℝ) ≤ R := le_trans (by exact_mod_cast hs'.1.2) (Nat.floor_le hR0.le)
        have hR' : 1 ≤ 2 * R / s := by rw [le_div_iff₀ hs0]; linarith
        have hlogR' : Real.log (2 * R / s) ≤ xj1 := by
          have h1 : 2 * R / s ≤ 2 * y := by
            rw [div_le_iff₀ hs0]
            have := hs'.2.1
            rw [div_lt_iff₀ hy0] at this
            linarith
          have h2 : Real.log (2 * R / s) ≤ Real.log 2 + Real.log y := by
            rw [← Real.log_mul (by norm_num) hy0.ne']
            exact Real.log_le_log (by positivity) h1
          have h3 : Real.log y ≤ (κ + xj) / u := by
            rw [hlogy, hlogP, hlogTj]
            apply div_le_div_of_nonneg_right _ hu0.le
            linarith
          linarith
        have hthr : Tj * R / s = Real.exp κ / 2 ^ (j + 1) * (2 * R / s) := by
          simp only [Tj]; rw [pow_succ]; field_simp
        rw [hthr]
        exact IH a' m (2 * R / s) ⟨hc, hv⟩ hm hR' hlogR'
      · unfold DeltaSub
        rw [not_nonempty_iff_eq_empty.mp hne, sum_empty]
        exact hb
    calc ∑ s ∈ Sset R y, (1 / s : ℝ) * DeltaSub q a (Ico t0 (t0 + len)) s (Tj * R / s)
        ≤ ∑ s ∈ Sset R y, (1 / s : ℝ) * b :=
          sum_le_sum (fun s hs => mul_le_mul_of_nonneg_left (hSb s hs) (by positivity))
      _ = (∑ s ∈ Sset R y, (1 / s : ℝ)) * b := by rw [sum_mul]
      _ ≤ (1 + Real.log R) * b := mul_le_mul_of_nonneg_right (sum_Sset_le hR) hb
      _ ≤ (1 + xj) * b := by gcongr

end ThetaSum
