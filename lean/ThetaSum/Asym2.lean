import ThetaSum.Asymptotics

/-
The final asymptotic inequality: the explicit bound `Gb C' L` for `|R_{K_W}(p)|`
(with `L = log p`) satisfies `(4/π) Gb C' L + c < L/2` for all large `L`.
-/

open Filter

namespace ThetaSum

/-- `A(L) = L^{1/20} + 2 log L + 4` (bounds `2 + log N`). -/
noncomputable def Aterm (L : ℝ) : ℝ := L ^ (1 / 20 : ℝ) + 2 * Real.log L + 4

/-- The explicit bound for `|R_{K_W}(p)|` in terms of `L = log p`. -/
noncomputable def Gb (C' L : ℝ) : ℝ :=
  2 / Real.pi * Aterm L * (L ^ (9 / 10 : ℝ) + 2) +
  2 / L ^ 2 * (2 / Real.pi * Aterm L * (1 + L)) +
  (2 * L + 1) * ((8 + 4 * Real.log L) * (16 / Real.pi * Aterm L *
    (C' * (Real.log L ^ 3 * L) * (L ^ (9 / 10 : ℝ) / 2) ^ (-(3 / 2 : ℝ))))) +
  2 * Real.pi * (1 + 1 / L) +
  L / Real.pi * (2 * (2 * L ^ 2) * (2 * L) * Real.exp (-(L ^ (1 / 20 : ℝ) / 80)))

lemma rpow_le_rpow_exp {L a b : ℝ} (hL : 1 ≤ L) (hab : a ≤ b) : L ^ a ≤ L ^ b :=
  Real.rpow_le_rpow_of_exponent_le hL hab

set_option maxHeartbeats 2000000 in
theorem Gb_small (C' c : ℝ) (hC : 0 ≤ C') :
    ∀ᶠ L : ℝ in atTop, 4 / Real.pi * Gb C' L + c < L / 2 := by
  have hpi := Real.pi_pos
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have e1 := ev_log_pow_le 1 1 (show (0 : ℝ) < 1 / 100 by norm_num)
  have e2 := ev_rpow_le (4 / Real.pi * 21 * 8) (show (19 / 20 : ℝ) < 1 by norm_num)
  have e3 := ev_rpow_le (4 / Real.pi * (4536 * C') * 8) (show (37 / 50 : ℝ) < 1 by norm_num)
  have e4 := ev_log_pow_le 1 640 (show (0 : ℝ) < 1 / 20 by norm_num)
  have e5 := ev_rpow_le 1280 (show (0 : ℝ) < 1 / 20 by norm_num)
  filter_upwards [e1, e2, e3, e4, e5, eventually_ge_atTop (2 : ℝ),
    eventually_ge_atTop (8 * (|c| + 4 / Real.pi * 29 + 17))] with L h1 h2 h3 h4 h5 hL2 hLc
  simp only [pow_one, one_mul, Real.rpow_zero, mul_one] at h1 h2 h3 h4 h5
  rw [Real.rpow_one] at h2 h3
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have p20 : 1 ≤ L ^ (1 / 20 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have p100 : L ^ (1 / 100 : ℝ) ≤ L ^ (1 / 20 : ℝ) := rpow_le_rpow_exp hL1 (by norm_num)
  have p910 : 1 ≤ L ^ (9 / 10 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have p20L : L ^ (1 / 20 : ℝ) ≤ L := by
    have := rpow_le_rpow_exp hL1 (show (1 / 20 : ℝ) ≤ 1 by norm_num); rwa [Real.rpow_one] at this
  -- `A ≤ 7 L^{1/20}`
  have hA : Aterm L ≤ 7 * L ^ (1 / 20 : ℝ) := by unfold Aterm; linarith
  have hA0 : 0 ≤ Aterm L := by unfold Aterm; positivity
  -- term 1
  have t1 : 2 / Real.pi * Aterm L * (L ^ (9 / 10 : ℝ) + 2) ≤ 21 * L ^ (19 / 20 : ℝ) := by
    have hpi1 : 2 / Real.pi ≤ 1 := by rw [div_le_one hpi]; linarith
    have e : L ^ (19 / 20 : ℝ) = L ^ (1 / 20 : ℝ) * L ^ (9 / 10 : ℝ) := by
      rw [← Real.rpow_add hL0]; norm_num
    rw [e]
    calc 2 / Real.pi * Aterm L * (L ^ (9 / 10 : ℝ) + 2) ≤ 1 * (7 * L ^ (1 / 20 : ℝ)) * (3 * L ^ (9 / 10 : ℝ)) := by
          apply mul_le_mul (mul_le_mul hpi1 hA hA0 (by norm_num)) (by linarith) (by positivity) (by positivity)
      _ = 21 * (L ^ (1 / 20 : ℝ) * L ^ (9 / 10 : ℝ)) := by ring
  -- term 2
  have t2 : 2 / L ^ 2 * (2 / Real.pi * Aterm L * (1 + L)) ≤ 28 := by
    have hpi1 : 2 / Real.pi ≤ 1 := by rw [div_le_one hpi]; linarith
    calc 2 / L ^ 2 * (2 / Real.pi * Aterm L * (1 + L)) ≤ 2 / L ^ 2 * (1 * (7 * L) * (2 * L)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul (mul_le_mul hpi1 (hA.trans (by linarith)) hA0 (by norm_num)) (by linarith)
            (by positivity) (by positivity)
      _ = 28 := by field_simp; ring
  -- term 3
  have t3 : (2 * L + 1) * ((8 + 4 * Real.log L) * (16 / Real.pi * Aterm L *
      (C' * (Real.log L ^ 3 * L) * (L ^ (9 / 10 : ℝ) / 2) ^ (-(3 / 2 : ℝ))))) ≤
      4536 * C' * L ^ (37 / 50 : ℝ) := by
    have hlogp : Real.log L ≤ L ^ (1 / 100 : ℝ) := h1
    have hl3 : Real.log L ^ 3 ≤ L ^ (3 / 100 : ℝ) := by
      calc Real.log L ^ 3 ≤ (L ^ (1 / 100 : ℝ)) ^ 3 := pow_le_pow_left₀ hlog0 hlogp 3
        _ = L ^ (3 / 100 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
    have hpow : (L ^ (9 / 10 : ℝ) / 2) ^ (-(3 / 2 : ℝ)) ≤ 3 * L ^ (-(27 / 20 : ℝ)) := by
      rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hL0.le]
      have h2r : (2 : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / 2 ^ (3 / 2 : ℝ) := by rw [Real.rpow_neg (by norm_num)]; ring
      rw [h2r, div_div_eq_mul_div, div_one]
      have : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 3 := by
        rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one,
          ← Real.sqrt_eq_rpow]
        have : Real.sqrt 2 < 1.5 := by
          rw [Real.sqrt_lt' (by norm_num)]; norm_num
        linarith
      have hq : (9 / 10 : ℝ) * -(3 / 2) = -(27 / 20) := by norm_num
      rw [hq, mul_comm]
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have hlin : 2 * L + 1 ≤ 3 * L := by linarith
    have hlog8 : 8 + 4 * Real.log L ≤ 12 * L ^ (1 / 100 : ℝ) := by
      have : 1 ≤ L ^ (1 / 100 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
      linarith
    have hpi6 : 16 / Real.pi ≤ 6 := by rw [div_le_iff₀ hpi]; linarith
    have hexp : L * L ^ (1 / 100 : ℝ) * L ^ (1 / 20 : ℝ) * (L ^ (3 / 100 : ℝ) * L) * L ^ (-(27 / 20 : ℝ)) =
        L ^ (37 / 50 : ℝ) := by
      have e : (37 / 50 : ℝ) = 1 + 1 / 100 + 1 / 20 + (3 / 100 + 1) + (-(27 / 20)) := by norm_num
      rw [e, Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_add hL0,
        Real.rpow_add hL0, Real.rpow_one]
    calc (2 * L + 1) * ((8 + 4 * Real.log L) * (16 / Real.pi * Aterm L *
          (C' * (Real.log L ^ 3 * L) * (L ^ (9 / 10 : ℝ) / 2) ^ (-(3 / 2 : ℝ)))))
        ≤ (3 * L) * ((12 * L ^ (1 / 100 : ℝ)) * (6 * (7 * L ^ (1 / 20 : ℝ)) *
          (C' * (L ^ (3 / 100 : ℝ) * L) * (3 * L ^ (-(27 / 20 : ℝ)))))) := by
          have hC3 : 0 ≤ C' * (Real.log L ^ 3 * L) := by positivity
          have hP : 0 ≤ (L ^ (9 / 10 : ℝ) / 2) ^ (-(3 / 2 : ℝ)) := by positivity
          apply mul_le_mul hlin _ (by positivity) (by positivity)
          apply mul_le_mul hlog8 _ (by positivity) (by positivity)
          apply mul_le_mul (mul_le_mul hpi6 hA hA0 (by norm_num)) _ (by positivity) (by positivity)
          apply mul_le_mul _ hpow hP (by positivity)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hl3 hL0.le) hC
      _ = 4536 * C' * (L * L ^ (1 / 100 : ℝ) * L ^ (1 / 20 : ℝ) * (L ^ (3 / 100 : ℝ) * L) *
            L ^ (-(27 / 20 : ℝ))) := by ring
      _ = 4536 * C' * L ^ (37 / 50 : ℝ) := by rw [hexp]
  -- term 4
  have t4 : 2 * Real.pi * (1 + 1 / L) ≤ 4 * Real.pi := by
    have : 1 / L ≤ 1 := by rw [div_le_one hL0]; exact hL1
    nlinarith
  -- term 5
  have t5 : L / Real.pi * (2 * (2 * L ^ 2) * (2 * L) * Real.exp (-(L ^ (1 / 20 : ℝ) / 80))) ≤ 1 := by
    -- `L^4 ≤ exp(L^{1/20}/80)` since `4 log L ≤ L^{1/20}/80`
    have hlog : 80 * (4 * Real.log L) + 80 * 2 ≤ L ^ (1 / 20 : ℝ) := by linarith
    have hL4 : L ^ 4 * Real.exp 2 ≤ Real.exp (L ^ (1 / 20 : ℝ) / 80) := by
      have e4 : Real.exp (4 * Real.log L) = L ^ 4 := by
        rw [show (4 : ℝ) * Real.log L = Real.log (L ^ 4) by rw [Real.log_pow]; norm_num]
        exact Real.exp_log (by positivity)
      rw [← e4, ← Real.exp_add]
      apply Real.exp_le_exp.mpr; linarith
    have he2 : (7 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2 : ℝ)
      have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      have := Real.exp_one_gt_d9
      rw [e]; nlinarith
    have hE : 0 < Real.exp (L ^ (1 / 20 : ℝ) / 80) := Real.exp_pos _
    rw [Real.exp_neg]
    have e : L / Real.pi * (2 * (2 * L ^ 2) * (2 * L) * (Real.exp (L ^ (1 / 20 : ℝ) / 80))⁻¹) =
        8 / Real.pi * (L ^ 4 / Real.exp (L ^ (1 / 20 : ℝ) / 80)) := by
      field_simp; ring
    rw [e, div_mul_eq_mul_div, div_le_one hpi]
    have : L ^ 4 / Real.exp (L ^ (1 / 20 : ℝ) / 80) ≤ 1 / 7 := by
      rw [div_le_iff₀ hE]
      have : L ^ 4 * 7 ≤ L ^ 4 * Real.exp 2 := mul_le_mul_of_nonneg_left he2 (by positivity)
      linarith
    have h0 : 0 ≤ L ^ 4 / Real.exp (L ^ (1 / 20 : ℝ) / 80) := by positivity
    nlinarith
  -- combine
  have hG : Gb C' L ≤ 21 * L ^ (19 / 20 : ℝ) + 28 + 4536 * C' * L ^ (37 / 50 : ℝ) + 4 * Real.pi + 1 := by
    unfold Gb; linarith
  have h4pi : 4 / Real.pi * (4 * Real.pi) = 16 := by field_simp; ring
  have hfin : 4 / Real.pi * Gb C' L ≤ 4 / Real.pi * 21 * L ^ (19 / 20 : ℝ) + 4 / Real.pi * 28 +
      4 / Real.pi * (4536 * C') * L ^ (37 / 50 : ℝ) + 16 + 4 / Real.pi := by
    have := mul_le_mul_of_nonneg_left hG (by positivity : (0 : ℝ) ≤ 4 / Real.pi)
    nlinarith
  have hc1 : 4 / Real.pi * 21 * L ^ (19 / 20 : ℝ) ≤ L / 8 := by linarith
  have hc2 : 4 / Real.pi * (4536 * C') * L ^ (37 / 50 : ℝ) ≤ L / 8 := by linarith
  have hc := le_abs_self c
  have h29 : 0 ≤ 4 / Real.pi * 29 := by positivity
  nlinarith

end ThetaSum
