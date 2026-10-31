import ThetaSum.FormalConjectures

/-!
# Weakening the hypothesis: any power-of-log saving for short Kloosterman sums

`HKS`: for some `δ > 0`, `θ < 1` and `C`, for all large primes `p`, every `b ≢ 0` and every
`N < p` with `log N ≥ (log p)^θ`,
`|∑_{n ≤ N} e(b n⁻¹/p)| ≤ C N (log p)^{-δ}`.

* `HKS_of_HBG : HBG → HKS` (with `θ = 9/10`, `δ = 1/4`), so (HKS) is weaker than (HBG).
* `lower_half_gen_KS`: the lower half of Conjecture 3.3 from (HKS), with
  `K_* = exp((log p)^{θ'})`, `θ' = (1+θ)/2`, and `T = exp((log p)^γ)`, `γ = min(δ, (1-θ)/8)/2`.
* `conjecture_3_3_of_HKS`, `Arxiv.«2501.03234».conjecture_4_4_of_HKS`.
-/

open Finset Filter

namespace ThetaSum

/-- **(HKS)** A power-of-log saving for incomplete Kloosterman sums of length
`N ≥ exp((log p)^θ)`, for some `θ < 1` and `δ > 0`. -/
def HKS : Prop :=
  ∃ δ θ C : ℝ, 0 < δ ∧ θ < 1 ∧ ∀ᶠ p : ℕ in Filter.atTop, p.Prime →
    ∀ b : ZMod p, b ≠ 0 → ∀ N : ℕ, Real.log p ^ θ ≤ Real.log N → N < p →
      ‖∑ n ∈ Icc 1 N, psiP p (b * (n : ZMod p)⁻¹)‖ ≤ C * N * Real.log p ^ (-δ)

/-- (HBG) implies (HKS), with `θ = 9/10` and `δ = 1/4`. -/
theorem HKS_of_HBG (hBG : HBG) : HKS := by
  obtain ⟨C, hC⟩ := hBG
  refine ⟨1 / 4, 9 / 10, max C 0, by norm_num, by norm_num, ?_⟩
  have hlogt : Tendsto (fun p : ℕ => Real.log p) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have e1 := hlogt.eventually (ev_log_pow_le 3 1 (show (0 : ℝ) < 1 / 10 by norm_num))
  have e2 := hlogt.eventually (eventually_ge_atTop (3 : ℝ))
  filter_upwards [hC, e1, e2] with p hp h1 h2 hpr b hb N hN hNp
  simp only [one_mul] at h1
  set L := Real.log p
  have hL0 : 0 < L := by linarith
  have h910 : 0 < L ^ (9 / 10 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hN' : L ^ (9 / 10 : ℝ) / 2 ≤ Real.log N := by linarith
  refine (hp hpr b hb N hN' hNp).trans ?_
  have hlogN : 0 < Real.log N := by linarith
  have hll : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hpow : Real.log N ^ (-(3 / 2 : ℝ)) ≤ L ^ (-(27 / 20 : ℝ)) := by
    have := Real.rpow_le_rpow_of_nonpos h910 hN (show -(3 / 2 : ℝ) ≤ 0 by norm_num)
    rwa [← Real.rpow_mul hL0.le, show (9 / 10 : ℝ) * -(3 / 2) = -(27 / 20) by norm_num] at this
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hC' : C ≤ max C 0 := le_max_left _ _
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hexp : L ^ (1 / 10 : ℝ) * L * L ^ (-(27 / 20 : ℝ)) = L ^ (-(1 / 4 : ℝ)) := by
    rw [show (-(1 / 4 : ℝ)) = 1 / 10 + 1 + (-(27 / 20)) by norm_num, Real.rpow_add hL0,
      Real.rpow_add hL0, Real.rpow_one]
  calc C * Real.log L ^ 3 * L * Real.log N ^ (-(3 / 2 : ℝ)) * N
      ≤ max C 0 * Real.log L ^ 3 * L * Real.log N ^ (-(3 / 2 : ℝ)) * N := by
        have : 0 ≤ Real.log L ^ 3 * L * Real.log N ^ (-(3 / 2 : ℝ)) * N := by positivity
        nlinarith
    _ ≤ max C 0 * L ^ (1 / 10 : ℝ) * L * L ^ (-(27 / 20 : ℝ)) * N := by
        gcongr
    _ = max C 0 * N * L ^ (-(1 / 4 : ℝ)) := by rw [← hexp]; ring

lemma one_term_KS (C δ θ : ℝ) (hC : 0 ≤ C) (p : ℕ) (_hp : 3 ≤ p) (b : ZMod p) (hb : b ≠ 0)
    (hKS : ∀ b : ZMod p, b ≠ 0 → ∀ N : ℕ, Real.log p ^ θ ≤ Real.log N → N < p →
      ‖Tsum p b N‖ ≤ C * N * Real.log p ^ (-δ))
    (a N' : ℕ) (ha : 6 ≤ a) (h1 : a ≤ 3 * N') (h2 : N' ≤ 2 * a) (h2a : 2 * a < p)
    (hlog : Real.log p ^ θ ≤ Real.log ((a : ℝ) / 3)) :
    ‖Tsum p b N'‖ ≤ C * Real.log p ^ (-δ) * (2 * a) := by
  have hN'R : (a : ℝ) / 3 ≤ N' := by
    rw [div_le_iff₀ (by norm_num)]; have : (a : ℝ) ≤ 3 * N' := by exact_mod_cast h1
    linarith
  have ha3 : (0 : ℝ) < (a : ℝ) / 3 := by
    have : (6 : ℝ) ≤ a := by exact_mod_cast ha
    positivity
  have hlN : Real.log ((a : ℝ) / 3) ≤ Real.log N' := Real.log_le_log ha3 hN'R
  refine (hKS b hb N' (hlog.trans hlN) (by omega)).trans ?_
  have hN2 : (N' : ℝ) ≤ 2 * a := by exact_mod_cast h2
  have hp1 : (0 : ℝ) ≤ Real.log p := Real.log_natCast_nonneg p
  have hX : 0 ≤ C * Real.log p ^ (-δ) := mul_nonneg hC (Real.rpow_nonneg hp1 _)
  calc C * N' * Real.log p ^ (-δ) = (C * Real.log p ^ (-δ)) * N' := by ring
    _ ≤ (C * Real.log p ^ (-δ)) * (2 * a) := mul_le_mul_of_nonneg_left hN2 hX

/-- Block Kloosterman bound from (HKS), through Lemma 6.4 (`odd_interval_bound`). -/
theorem block_kloost_KS (C δ θ : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (_hp2 : p ≠ 2)
    (hKS : ∀ b : ZMod p, b ≠ 0 → ∀ N : ℕ, Real.log p ^ θ ≤ Real.log N → N < p →
      ‖Tsum p b N‖ ≤ C * N * Real.log p ^ (-δ))
    (a b : ℕ) (ha : 6 ≤ a) (hb : b ≤ 2 * a) (h2a : 2 * a < p)
    (hlog : Real.log p ^ θ ≤ Real.log ((a : ℝ) / 3)) :
    ∀ c : ZMod p, c ≠ 0 → ∀ x, a ≤ x → x ≤ b →
      ‖∑ k ∈ (Ico a x).filter Odd, psiP p (c * ((2 * k : ℕ) : ZMod p)⁻¹)‖ ≤
        4 * (C * Real.log p ^ (-δ) * (2 * a)) := by
  have := Fact.mk hp
  intro c hc x hax hxb
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this; omega
  have h4 : (4 : ZMod p) ≠ 0 := by
    have : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hb1 : c * 2⁻¹ ≠ 0 := mul_ne_zero hc (inv_ne_zero h2)
  have hb2 : c * 4⁻¹ ≠ 0 := mul_ne_zero hc (inv_ne_zero h4)
  refine (odd_interval_bound p hp c a x (by omega) hax).trans ?_
  have t1 := one_term_KS C δ θ hC p hp3 _ hb1 hKS a (x - 1) ha (by omega) (by omega) h2a hlog
  have t2 := one_term_KS C δ θ hC p hp3 _ hb1 hKS a (a - 1) ha (by omega) (by omega) h2a hlog
  have t3 := one_term_KS C δ θ hC p hp3 _ hb2 hKS a ((x + 1) / 2 - 1) ha (by omega) (by omega) h2a hlog
  have t4 := one_term_KS C δ θ hC p hp3 _ hb2 hKS a ((a + 1) / 2 - 1) ha (by omega) (by omega) h2a hlog
  linarith

/-! ### The explicit bound and its asymptotics -/

/-- `L^γ + 2 log L + 4` (a bound for `2 + log N`). -/
noncomputable def AtermK (γ L : ℝ) : ℝ := L ^ γ + 2 * Real.log L + 4

/-- The explicit bound for `|R_{K}(p)|` under (HKS), in terms of `L = log p`. -/
noncomputable def GbK (C' γ θ' δ L : ℝ) : ℝ :=
  2 / Real.pi * AtermK γ L * (L ^ θ' + 2) +
  2 / L ^ 2 * (2 / Real.pi * AtermK γ L * (1 + L)) +
  (2 * L + 1) * ((8 + 4 * Real.log L) * (16 / Real.pi * AtermK γ L * (C' * L ^ (-δ)))) +
  2 * Real.pi * (1 + 1 / L) +
  L / Real.pi * (2 * (2 * L ^ 2) * (2 * L) * Real.exp (-(γ * L ^ γ / 4)))

lemma one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9; linarith

set_option maxHeartbeats 2000000 in
theorem GbK_small (C' c γ θ' δ : ℝ) (hC : 0 ≤ C') (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hθ' : 0 < θ')
    (hsum : γ + θ' < 1) (hγδ : γ < δ) :
    ∀ᶠ L : ℝ in atTop, 4 / Real.pi * GbK C' γ θ' δ L + c < L / 2 := by
  have hpi := Real.pi_pos
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  set η := (δ - γ) / 2 with hηdef
  have hη : 0 < η := by simp only [hηdef]; linarith
  have e1 := ev_log_pow_le 1 1 hγ
  have e1' := ev_log_pow_le 1 1 hη
  have e2 := ev_rpow_le (4 / Real.pi * 21 * 8) hsum
  have he3 : 1 + η + γ - δ < 1 := by simp only [hηdef]; linarith
  have e3 := ev_rpow_le (4 / Real.pi * (1512 * C') * 8) he3
  have e4 := ev_log_pow_le 1 (32 / γ) hγ
  filter_upwards [e1, e1', e2, e3, e4, eventually_ge_atTop (3 : ℝ),
    eventually_ge_atTop (8 * (|c| + 4 / Real.pi * 29 + 17))] with L h1 h1' h2 h3 h4 hL3 hLc
  simp only [pow_one, one_mul] at h1 h1' h4
  rw [Real.rpow_one] at h2 h3
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hlog1 : 1 ≤ Real.log L := by
    have := one_lt_log_three
    have := Real.log_le_log (by norm_num) hL3
    linarith
  have hlog0 : 0 ≤ Real.log L := by linarith
  have pγ : 1 ≤ L ^ γ := Real.one_le_rpow hL1 hγ.le
  have pθ : 1 ≤ L ^ θ' := Real.one_le_rpow hL1 hθ'.le
  have pη : 1 ≤ L ^ η := Real.one_le_rpow hL1 hη.le
  have pγL : L ^ γ ≤ L := by
    have := Real.rpow_le_rpow_of_exponent_le hL1 hγ1; rwa [Real.rpow_one] at this
  have hA : AtermK γ L ≤ 7 * L ^ γ := by unfold AtermK; linarith
  have hA0 : 0 ≤ AtermK γ L := by unfold AtermK; positivity
  have hpi1 : 2 / Real.pi ≤ 1 := by rw [div_le_one hpi]; linarith
  -- term 1
  have t1 : 2 / Real.pi * AtermK γ L * (L ^ θ' + 2) ≤ 21 * L ^ (γ + θ') := by
    rw [Real.rpow_add hL0]
    calc 2 / Real.pi * AtermK γ L * (L ^ θ' + 2) ≤ 1 * (7 * L ^ γ) * (3 * L ^ θ') := by
          apply mul_le_mul (mul_le_mul hpi1 hA hA0 (by norm_num)) (by linarith) (by positivity)
            (by positivity)
      _ = 21 * (L ^ γ * L ^ θ') := by ring
  -- term 2
  have t2 : 2 / L ^ 2 * (2 / Real.pi * AtermK γ L * (1 + L)) ≤ 28 := by
    calc 2 / L ^ 2 * (2 / Real.pi * AtermK γ L * (1 + L)) ≤ 2 / L ^ 2 * (1 * (7 * L) * (2 * L)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul (mul_le_mul hpi1 (hA.trans (by linarith)) hA0 (by norm_num)) (by linarith)
            (by positivity) (by positivity)
      _ = 28 := by field_simp; ring
  -- term 3
  have t3 : (2 * L + 1) * ((8 + 4 * Real.log L) * (16 / Real.pi * AtermK γ L * (C' * L ^ (-δ)))) ≤
      1512 * C' * L ^ (1 + η + γ - δ) := by
    have hlin : 2 * L + 1 ≤ 3 * L := by linarith
    have hlog8 : 8 + 4 * Real.log L ≤ 12 * L ^ η := by linarith
    have hpi6 : 16 / Real.pi ≤ 6 := by rw [div_le_iff₀ hpi]; linarith
    have hexp : L * L ^ η * L ^ γ * L ^ (-δ) = L ^ (1 + η + γ - δ) := by
      rw [show 1 + η + γ - δ = 1 + η + γ + (-δ) by ring, Real.rpow_add hL0, Real.rpow_add hL0,
        Real.rpow_add hL0, Real.rpow_one]
    have hd : 0 ≤ L ^ (-δ) := Real.rpow_nonneg hL0.le _
    calc (2 * L + 1) * ((8 + 4 * Real.log L) * (16 / Real.pi * AtermK γ L * (C' * L ^ (-δ))))
        ≤ (3 * L) * ((12 * L ^ η) * (6 * (7 * L ^ γ) * (C' * L ^ (-δ)))) := by
          apply mul_le_mul hlin _ (by positivity) (by positivity)
          apply mul_le_mul hlog8 _ (by positivity) (by positivity)
          apply mul_le_mul (mul_le_mul hpi6 hA hA0 (by norm_num)) le_rfl (by positivity)
            (by positivity)
      _ = 1512 * C' * (L * L ^ η * L ^ γ * L ^ (-δ)) := by ring
      _ = 1512 * C' * L ^ (1 + η + γ - δ) := by rw [hexp]
  -- term 4
  have t4 : 2 * Real.pi * (1 + 1 / L) ≤ 4 * Real.pi := by
    have : 1 / L ≤ 1 := by rw [div_le_one hL0]; exact hL1
    nlinarith
  -- term 5
  have t5 : L / Real.pi * (2 * (2 * L ^ 2) * (2 * L) * Real.exp (-(γ * L ^ γ / 4))) ≤ 1 := by
    have hγL : 32 * Real.log L ≤ γ * L ^ γ := by
      have := mul_le_mul_of_nonneg_left h4 hγ.le
      rw [← mul_assoc, mul_div_cancel₀ _ hγ.ne'] at this
      linarith
    have hL4 : L ^ 4 * Real.exp 2 ≤ Real.exp (γ * L ^ γ / 4) := by
      have e4 : Real.exp (4 * Real.log L) = L ^ 4 := by
        rw [show (4 : ℝ) * Real.log L = Real.log (L ^ 4) by rw [Real.log_pow]; norm_num]
        exact Real.exp_log (by positivity)
      rw [← e4, ← Real.exp_add]
      apply Real.exp_le_exp.mpr; linarith
    have he2 : (7 : ℝ) ≤ Real.exp 2 := by
      have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      have := Real.exp_one_gt_d9
      rw [e]; nlinarith
    have hE : 0 < Real.exp (γ * L ^ γ / 4) := Real.exp_pos _
    rw [Real.exp_neg]
    have e : L / Real.pi * (2 * (2 * L ^ 2) * (2 * L) * (Real.exp (γ * L ^ γ / 4))⁻¹) =
        8 / Real.pi * (L ^ 4 / Real.exp (γ * L ^ γ / 4)) := by
      field_simp; ring
    rw [e, div_mul_eq_mul_div, div_le_one hpi]
    have : L ^ 4 / Real.exp (γ * L ^ γ / 4) ≤ 1 / 7 := by
      rw [div_le_iff₀ hE]
      have : L ^ 4 * 7 ≤ L ^ 4 * Real.exp 2 := mul_le_mul_of_nonneg_left he2 (by positivity)
      linarith
    have h0 : 0 ≤ L ^ 4 / Real.exp (γ * L ^ γ / 4) := by positivity
    nlinarith
  -- combine
  have hG : GbK C' γ θ' δ L ≤ 21 * L ^ (γ + θ') + 28 + 1512 * C' * L ^ (1 + η + γ - δ) +
      4 * Real.pi + 1 := by
    unfold GbK; linarith
  have hfin : 4 / Real.pi * GbK C' γ θ' δ L ≤ 4 / Real.pi * 21 * L ^ (γ + θ') + 4 / Real.pi * 28 +
      4 / Real.pi * (1512 * C') * L ^ (1 + η + γ - δ) + 16 + 4 / Real.pi := by
    have h4p : 4 / Real.pi * (4 * Real.pi) = 16 := by field_simp; ring
    have := mul_le_mul_of_nonneg_left hG (by positivity : (0 : ℝ) ≤ 4 / Real.pi)
    nlinarith
  have hc1 : 4 / Real.pi * 21 * L ^ (γ + θ') ≤ L / 8 := by linarith
  have hc2 : 4 / Real.pi * (1512 * C') * L ^ (1 + η + γ - δ) ≤ L / 8 := by linarith
  have hc := le_abs_self c
  have h29 : 0 ≤ 4 / Real.pi * 29 := by positivity
  nlinarith

/-- The real inequalities (in `L = log p`) used to check all side conditions under (HKS). -/
def GoodK (L₀ C' c γ θ θ' δ L : ℝ) : Prop :=
  max L₀ 1000 ≤ L ∧ L ^ γ + 2 + 2 * Real.log L ≤ L - 1 ∧ 4 * Real.log L + 3 ≤ L / 4 ∧
    L ^ γ + 2 * Real.log L + 4 ≤ L ^ θ' ∧ L ^ θ' + 1 ≤ L / 2 ∧ 4 ≤ L ^ θ' ∧
    L ^ θ + Real.log 3 ≤ L ^ θ' ∧ 4 / Real.pi * GbK C' γ θ' δ L + c < L / 2

lemma eventually_goodK (L₀ C' c γ θ θ' δ : ℝ) (hC : 0 ≤ C') (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hsum : γ + θ' < 1) (hγδ : γ < δ) (hθθ' : θ < θ') (hθ'1 : θ' < 1) (hγθ' : γ < θ') :
    ∀ᶠ L : ℝ in atTop, GoodK L₀ C' c γ θ θ' δ L := by
  have hθ'0 : 0 < θ' := by linarith
  have a1 := ev_rpow_le 4 (show γ < 1 by linarith)
  have a2 := ev_log_pow_le 1 8 (show (0 : ℝ) < 1 by norm_num)
  have a3 := ev_log_pow_le 1 32 (show (0 : ℝ) < 1 by norm_num)
  have a4 := ev_rpow_le 3 hγθ'
  have a5 := ev_log_pow_le 1 6 hθ'0
  have a6 := ev_rpow_le 12 hθ'0
  have a7 := ev_rpow_le 4 hθ'1
  have a8 := ev_rpow_le 2 hθθ'
  filter_upwards [a1, a2, a3, a4, a5, a6, a7, a8, GbK_small C' c γ θ' δ hC hγ hγ1 hθ'0 hsum hγδ,
    eventually_ge_atTop (max L₀ 1000)] with L h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp only [pow_one, Real.rpow_one, Real.rpow_zero, mul_one] at h1 h2 h3 h4 h5 h6 h7 h8
  have hL : 1000 ≤ L := le_trans (le_max_right _ _) h10
  have hγ0 : 0 ≤ L ^ γ := Real.rpow_nonneg (by linarith) _
  have hθ0 : 0 ≤ L ^ θ := Real.rpow_nonneg (by linarith) _
  have hl3 := log_three_lt
  refine ⟨h10, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, h9⟩

/-- The right-hand side of `R_bound_gen` with the (HKS) parameters is at most `GbK`. -/
lemma rhs_le_GbK (C' L γ θ' δ lN lKs H lK J Hs M I e : ℝ) (hC : 0 ≤ C')
    (hL : 1000 ≤ L) (hlN0 : 0 ≤ lN) (hlN : 2 + lN ≤ AtermK γ L) (hlKs0 : 0 ≤ 1 + lKs)
    (hlKs : 1 + lKs ≤ L ^ θ' + 2) (hH : L ^ 2 ≤ H) (hlK0 : 0 ≤ 1 + lK) (hlK : lK ≤ L)
    (hJ : J ≤ 2 * L + 1) (hHs0 : 0 ≤ Hs + 4) (hHs : Hs + 4 ≤ 8 + 4 * Real.log L)
    (hM : M ≤ 2 * L ^ 2) (hI0 : 0 ≤ I) (hI : I ≤ 2 * L) (he0 : 0 ≤ e)
    (he : e ≤ Real.exp (-(γ * L ^ γ / 4))) :
    2 / Real.pi * (2 + lN) * (1 + lKs) + 2 / (H + 1) * (2 / Real.pi * (2 + lN) * (1 + lK)) +
      J * ((Hs + 4) * (16 / Real.pi * (2 + lN) * (C' * L ^ (-δ)))) +
      2 * Real.pi * (1 + 1 / L) + L / Real.pi * (2 * M * I * e) ≤ GbK C' γ θ' δ L := by
  have hpi := Real.pi_pos
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hL0 : 0 ≤ L := by linarith
  have hA : 0 ≤ AtermK γ L := by linarith
  have hA2 : 0 ≤ 2 / Real.pi * AtermK γ L := mul_nonneg (by positivity) hA
  have hA16 : 0 ≤ 16 / Real.pi * AtermK γ L := mul_nonneg (by positivity) hA
  have hX : 0 ≤ C' * L ^ (-δ) := mul_nonneg hC (Real.rpow_nonneg hL0 _)
  have hHL : L ^ 2 ≤ H + 1 := by linarith
  have hL2 : 0 < L ^ 2 := by positivity
  have t1 : 2 / Real.pi * (2 + lN) * (1 + lKs) ≤ 2 / Real.pi * AtermK γ L * (L ^ θ' + 2) := by
    gcongr
  have t2 : 2 / (H + 1) * (2 / Real.pi * (2 + lN) * (1 + lK)) ≤
      2 / L ^ 2 * (2 / Real.pi * AtermK γ L * (1 + L)) := by
    gcongr
  have t3 : J * ((Hs + 4) * (16 / Real.pi * (2 + lN) * (C' * L ^ (-δ)))) ≤
      (2 * L + 1) * ((8 + 4 * Real.log L) * (16 / Real.pi * AtermK γ L * (C' * L ^ (-δ)))) := by
    gcongr
  have t5 : L / Real.pi * (2 * M * I * e) ≤
      L / Real.pi * (2 * (2 * L ^ 2) * (2 * L) * Real.exp (-(γ * L ^ γ / 4))) := by
    gcongr
  unfold GbK
  linarith

/-! ### The lower half under (HKS) -/

set_option maxHeartbeats 1000000 in
/-- **The lower half of Conjecture 3.3** with the cutoff `K = ⌊p^θ (log p)^4⌋`, `1/2 ≤ θ ≤ 3/4`,
conditional on the corresponding one-sided Theorem B, (HV) and (HKS). -/
theorem lower_half_gen_KS (θ : ℝ) (hθ1 : 1 / 2 ≤ θ) (hθ2 : θ ≤ 3 / 4)
    (hB : ∃ C : ℝ, ∀ᶠ p : ℕ in Filter.atTop, p.Prime →
      (p : ℝ) / 2 * Real.log p + 4 * p / Real.pi * RsumK (KWθ θ p) p - C * p ≤ (S p : ℝ))
    (hV : HV) (hK : HKS) :
    ∀ n : ℕ, ∀ᶠ k in Filter.atTop, k.Prime → (n : ℤ) * k < S k := by
  intro n
  obtain ⟨C1, hC1⟩ := hB
  obtain ⟨δ, θK, C, hδ, hθK, hC⟩ := hK
  set C' := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  -- normalized exponents: `1/2 ≤ θ₁ < 1`, `0 < δ₁ ≤ 1/2`
  set θ₁ := max θK (1 / 2) with hθ₁def
  set δ₁ := min δ (1 / 2) with hδ₁def
  have hθ₁1 : θ₁ < 1 := max_lt hθK (by norm_num)
  have hθ₁h : 1 / 2 ≤ θ₁ := le_max_right _ _
  have hδ₁ : 0 < δ₁ := lt_min hδ (by norm_num)
  -- parameters: `θ' = (1 + θ₁)/2`, `γ = min δ₁ ((1-θ₁)/8) / 2`
  set θ' := (1 + θ₁) / 2 with hθ'def
  set γ := min δ₁ ((1 - θ₁) / 8) / 2 with hγdef
  have hγ0 : 0 < γ := by
    have : 0 < min δ₁ ((1 - θ₁) / 8) := lt_min hδ₁ (by linarith)
    simp only [hγdef]; linarith
  have hγm1 : γ ≤ δ₁ / 2 := by
    have := min_le_left δ₁ ((1 - θ₁) / 8); simp only [hγdef]; linarith
  have hγm2 : γ ≤ (1 - θ₁) / 16 := by
    have := min_le_right δ₁ ((1 - θ₁) / 8); simp only [hγdef]; linarith
  have hγ1 : γ < 1 := by linarith
  have hγθ' : γ + θ' < 1 := by simp only [hθ'def]; linarith
  have hγδ : γ < δ₁ := by linarith
  have hθθ' : θ₁ < θ' := by simp only [hθ'def]; linarith
  have hθ'0 : 0 < θ' := by simp only [hθ'def]; linarith
  have hθ'1 : θ' < 1 := by simp only [hθ'def]; linarith
  have hγθ'' : γ < θ' := by linarith
  obtain ⟨L₀, hL₀⟩ := tails_sum_explicit (γ₀ := γ) hγ0 hγ1
  have hlogt : Tendsto (fun p : ℕ => Real.log p) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev := hlogt.eventually (eventually_goodK L₀ C' (C1 + n) γ θ₁ θ' δ₁ hC' hγ0 hγ1.le
    hγθ' hγδ hθθ' hθ'1 hγθ'')
  filter_upwards [hev, hC1, hC] with p hG hS hKSp hp
  obtain ⟨hL0, hR1, hR2, hR4, hR5, hR3, hR6, hfin⟩ := hG
  have hS := hS hp
  have hKSp := hKSp hp
  set L := Real.log p with hLdef
  have hpi := Real.pi_pos
  have hL1000 : 1000 ≤ L := le_trans (le_max_right _ _) hL0
  have hLL₀ : L₀ ≤ L := le_trans (le_max_left _ _) hL0
  have hLpos : 0 < L := by linarith
  have hL2 : 1000 * L ≤ L ^ 2 := by rw [sq]; exact mul_le_mul_of_nonneg_right hL1000 hLpos.le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpL : (p : ℝ) = Real.exp L := (Real.exp_log hp0).symm
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have heL : (100 : ℝ) ≤ Real.exp L := by
    have := Real.add_one_le_exp L; linarith
  have hp5 : 5 ≤ p := by
    have : (5 : ℝ) ≤ p := by rw [hpL]; linarith
    exact_mod_cast this
  have hp2 : p ≠ 2 := by omega
  -- `T`
  set T := Real.exp (L ^ γ) with hTdef
  have hT1 : 1 ≤ L ^ γ := Real.one_le_rpow (by linarith) hγ0.le
  have hT2 : 2 ≤ T := by
    have := Real.add_one_le_exp (L ^ γ); linarith
  have hT0 : 0 < T := Real.exp_pos _
  -- `T (L² + 2) ≤ exp(L - 1)`
  have hlogL2 : Real.log (L ^ 2 + 2) ≤ 2 + 2 * Real.log L := by
    have h1 : L ^ 2 + 2 ≤ Real.exp 2 * L ^ 2 := by
      have : (2 : ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp (2 : ℝ); linarith
      have := mul_le_mul_of_nonneg_right this (sq_nonneg L)
      linarith
    calc Real.log (L ^ 2 + 2) ≤ Real.log (Real.exp 2 * L ^ 2) := Real.log_le_log (by positivity) h1
      _ = 2 + 2 * Real.log L := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow]; push_cast; ring
  have hTL : T * (L ^ 2 + 2) ≤ Real.exp (L ^ γ + 2 + 2 * Real.log L) := by
    rw [show L ^ γ + 2 + 2 * Real.log L = L ^ γ + (2 + 2 * Real.log L) by ring,
      Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hT0.le
    calc L ^ 2 + 2 = Real.exp (Real.log (L ^ 2 + 2)) := (Real.exp_log (by positivity)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlogL2
  have hTLp : T * (L ^ 2 + 2) ≤ Real.exp (L - 1) := hTL.trans (Real.exp_le_exp.mpr hR1)
  have hexpL1 : Real.exp (L - 1) * 2 ≤ Real.exp L := by
    rw [show L = (L - 1) + 1 by ring, Real.exp_add]; simp only [add_sub_cancel_right]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have := Real.add_one_le_exp (1 : ℝ); linarith
  -- `M`, `N`, `H`
  set M := ⌈L ^ 2⌉₊
  have hM1 : L ^ 2 ≤ M := Nat.le_ceil _
  have hM2 : (M : ℝ) < L ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  set N := ⌈T * M⌉₊
  have hN1 : T * M ≤ N := Nat.le_ceil _
  have hN2 : (N : ℝ) < T * M + 1 := Nat.ceil_lt_add_one (by positivity)
  have hTM : T * M ≤ T * (L ^ 2 + 1) := mul_le_mul_of_nonneg_left hM2.le hT0.le
  have h2M : 2 * (M : ℝ) ≤ T * M := mul_le_mul_of_nonneg_right hT2 (Nat.cast_nonneg M)
  have hNTL : (N : ℝ) ≤ T * (L ^ 2 + 2) := by linarith
  have hNp : N < p := by
    have : (N : ℝ) < p := by rw [hpL]; linarith [Real.exp_pos (L - 1)]
    exact_mod_cast this
  have hM1' : 1 ≤ M := by
    have : (1 : ℝ) ≤ M := by linarith
    exact_mod_cast this
  have hMN : M ≤ N := by
    have : (M : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hN2' : 2 ≤ N := by
    have : (2 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hMp : M < p := lt_of_le_of_lt hMN hNp
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogN : Real.log N ≤ L ^ γ + 2 + 2 * Real.log L := by
    rw [Real.log_le_iff_le_exp hNpos]; exact hNTL.trans hTL
  -- `K_*`
  set E := Real.exp (L ^ θ')
  set Ks := ⌈E⌉₊
  have hKs1 : E ≤ Ks := Nat.le_ceil _
  have hKs2 : (Ks : ℝ) < E + 1 := Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hE4 : (6 : ℝ) ≤ E := six_le_exp hR3
  have hKs6 : 6 ≤ Ks := by
    have : (6 : ℝ) ≤ Ks := hE4.trans hKs1
    exact_mod_cast this
  have h3TL : 3 * (T * (L ^ 2 + 2)) ≤ E := by
    calc 3 * (T * (L ^ 2 + 2)) ≤ Real.exp 2 * Real.exp (L ^ γ + 2 + 2 * Real.log L) := by
          apply mul_le_mul _ hTL (by positivity) (Real.exp_pos _).le
          have := Real.add_one_le_exp (2 : ℝ); linarith
      _ = Real.exp (L ^ γ + 2 * Real.log L + 4) := by rw [← Real.exp_add]; ring_nf
      _ ≤ E := Real.exp_le_exp.mpr hR4
  have hNKs : 2 * N + 1 ≤ Ks := by
    have : ((2 * N + 1 : ℕ) : ℝ) ≤ Ks := by
      push_cast
      have := mul_le_mul_of_nonneg_right hT2 (by positivity : (0 : ℝ) ≤ L ^ 2 + 2)
      linarith
    exact_mod_cast this
  -- `K = K_W`
  set V := Real.exp (L * θ) * L ^ 4
  have hKWe : KWθ θ p = ⌊V⌋₊ := by
    unfold KWθ; rw [hpL, ← Real.exp_mul, Real.log_exp]
  have hV0 : 0 ≤ V := by positivity
  have hK1 : (KWθ θ p : ℝ) ≤ V := by rw [hKWe]; exact Nat.floor_le hV0
  have hK2 : V < KWθ θ p + 1 := by rw [hKWe]; exact Nat.lt_floor_add_one V
  have hLθ1 : L / 2 ≤ L * θ := by
    have := mul_le_mul_of_nonneg_left hθ1 hLpos.le; linarith
  have hLθ2 : L * θ ≤ L * (3 / 4) := mul_le_mul_of_nonneg_left hθ2 hLpos.le
  have hEL2 : Real.exp (L / 2) ≤ V :=
    (Real.exp_le_exp.mpr hLθ1).trans
      (le_mul_of_one_le_right (Real.exp_pos _).le (one_le_pow₀ (by linarith)))
  have hVbig : 2 ≤ V := by
    have := Real.add_one_le_exp (L / 2); linarith
  have hV20 : V * 20 ≤ Real.exp L := by
    have h1 : V = Real.exp (L * θ + 4 * Real.log L) := by
      rw [Real.exp_add, show (4 : ℝ) * Real.log L = Real.log (L ^ 4) by rw [Real.log_pow]; norm_num,
        Real.exp_log (pow_pos hLpos 4)]
    have h2 : Real.exp (L * θ + 4 * Real.log L) * Real.exp 3 ≤ Real.exp L := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    rw [h1]
    exact (mul_le_mul_of_nonneg_left exp_three_ge (Real.exp_pos _).le).trans h2
  have hKpos' : (0 : ℝ) < KWθ θ p := by linarith
  have hK8 : (KWθ θ p : ℝ) * 8 ≤ p := by rw [hpL]; linarith
  have hKp : KWθ θ p ≤ p := by
    have : (KWθ θ p : ℝ) ≤ p := by linarith
    exact_mod_cast this
  have hK2p : 2 * KWθ θ p < p := by
    have : ((2 * KWθ θ p : ℕ) : ℝ) < p := by push_cast; linarith
    exact_mod_cast this
  have hKsK : Ks ≤ KWθ θ p := by
    have h2E : E * 2 ≤ Real.exp (L / 2) := by
      calc E * 2 ≤ E * Real.exp 1 := by
            apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
            have := Real.add_one_le_exp (1 : ℝ); linarith
        _ = Real.exp (L ^ θ' + 1) := by rw [Real.exp_add]
        _ ≤ Real.exp (L / 2) := Real.exp_le_exp.mpr hR5
    have : (Ks : ℝ) < KWθ θ p + 1 := by linarith
    have : Ks < KWθ θ p + 1 := by exact_mod_cast this
    omega
  have hlogKs : L ^ θ₁ ≤ Real.log ((Ks : ℝ) / 3) := by
    rw [Real.log_div (by positivity) (by norm_num)]
    have : L ^ θ' ≤ Real.log Ks := by
      rw [Real.le_log_iff_exp_le (by positivity)]; exact hKs1
    linarith
  -- `J`
  set J := ⌈2 * L⌉₊
  have hJ1 : 2 * L ≤ J := Nat.le_ceil _
  have hJ2 : (J : ℝ) < 2 * L + 1 := Nat.ceil_lt_add_one (by positivity)
  have hKJ : KWθ θ p ≤ 2 ^ J * Ks := by
    have h1 : Real.exp L ≤ (2 : ℝ) ^ J := by
      have : Real.exp L ≤ Real.exp (J * Real.log 2) := by
        apply Real.exp_le_exp.mpr
        have h1 := mul_le_mul_of_nonneg_right hJ1 (Real.log_pos one_lt_two).le
        have h2 := mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le hLpos.le
        linarith
      rw [show Real.exp (J * Real.log 2) = (2 : ℝ) ^ J by
        rw [← Real.log_pow, Real.exp_log (by positivity)]] at this
      exact this
    have : (KWθ θ p : ℝ) ≤ 2 ^ J * Ks := by
      have hKs1' : (1 : ℝ) ≤ Ks := by exact_mod_cast (by omega : 1 ≤ Ks)
      have : (KWθ θ p : ℝ) ≤ Real.exp L := by rw [← hpL]; exact_mod_cast hKp
      have := le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ 2 ^ J) hKs1'
      linarith
    exact_mod_cast this
  -- `I`
  set I := Nat.log 2 (KWθ θ p) + 1
  have hKpos : 0 < KWθ θ p := by exact_mod_cast hKpos'
  have hI1 : KWθ θ p < 2 ^ I := Nat.lt_pow_succ_log_self (by norm_num) _
  have hI2 : 2 ^ (I - 1) ≤ KWθ θ p := by
    simp only [I, Nat.add_sub_cancel]; exact Nat.pow_log_le_self 2 hKpos.ne'
  have hI2' : (2 : ℝ) ^ I ≤ 2 * KWθ θ p := by
    have : 2 ^ I ≤ 2 * KWθ θ p := by
      have e : I = (I - 1) + 1 := by simp only [I]; omega
      rw [e, pow_succ]; omega
    exact_mod_cast this
  have hIL : (I : ℝ) ≤ 2 * L := by
    have h1 : ((I - 1 : ℕ) : ℝ) * Real.log 2 ≤ L := by
      rw [← Real.log_pow]
      have : ((2 : ℝ) ^ (I - 1)) ≤ Real.exp L := by
        rw [← hpL]; have : (2 : ℝ) ^ (I - 1) ≤ KWθ θ p := by exact_mod_cast hI2
        linarith
      calc Real.log ((2 : ℝ) ^ (I - 1)) ≤ Real.log (Real.exp L) := Real.log_le_log (by positivity) this
        _ = L := Real.log_exp L
    have hI1' : ((I - 1 : ℕ) : ℝ) = I - 1 := by
      rw [Nat.cast_sub (by simp only [I]; omega)]; simp
    rw [hI1'] at h1
    have hI0 : (0 : ℝ) ≤ I - 1 := by rw [← hI1']; exact Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le hI0
    linarith
  -- the tails
  have hTI : (KWθ θ p : ℝ) ≤ T * 2 ^ I := by
    have : (KWθ θ p : ℝ) ≤ 2 ^ I := by exact_mod_cast hI1.le
    have := le_mul_of_one_le_left (by positivity : (0 : ℝ) ≤ 2 ^ I) (by linarith : (1 : ℝ) ≤ T)
    linarith
  have hpI : (p : ℝ) * 2 ^ I + M ≤ (p : ℝ) ^ 2 := by
    have hMp' : (M : ℝ) ≤ p := by exact_mod_cast hMp.le
    have hp4 : (4 : ℝ) ≤ p := by exact_mod_cast (by omega : 4 ≤ p)
    have h1 := mul_le_mul_of_nonneg_left (by linarith : (2 : ℝ) ^ I ≤ p / 4) hp0.le
    have h2 := mul_le_mul_of_nonneg_right hp4 hp0.le
    linarith
  have hdiv : ∀ k ∈ (Ioo (N + 1) (KWθ θ p)).filter Odd, (k : ℤ) ∣ 2 * p * uInv p k - 1 := by
    intro k hk
    simp only [mem_filter, mem_Ioo] at hk
    apply uInv_spec p k (by omega)
    have hcop : Nat.Coprime p k := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]; intro h; have := Nat.le_of_dvd (by omega) h; omega
    exact Nat.coprime_mul_iff_left.mpr ⟨Nat.coprime_two_left.mpr hk.2, hcop⟩
  have htail := hL₀ p hp hLL₀ M N (KWθ θ p) I (uInv p) hM1' hMN hN2' hMp hT2 hTI hpI hM1 hN1 hKp hdiv
  rw [← hLdef, ← hTdef] at htail
  -- the (HKS) input with normalized constants
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hKS' : ∀ b : ZMod p, b ≠ 0 → ∀ N' : ℕ, Real.log p ^ θ₁ ≤ Real.log N' → N' < p →
      ‖Tsum p b N'‖ ≤ C' * N' * Real.log p ^ (-δ₁) := by
    intro b hb N' hN' hN'p
    have hθle : L ^ θK ≤ L ^ θ₁ := Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _)
    refine (hKSp b hb N' (hθle.trans hN') hN'p).trans ?_
    have hδle : L ^ (-δ) ≤ L ^ (-δ₁) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by have := min_le_left δ (1 / 2); linarith)
    have hN0 : (0 : ℝ) ≤ N' := Nat.cast_nonneg _
    calc C * N' * L ^ (-δ) ≤ C' * N' * L ^ (-δ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hN0)
            (Real.rpow_nonneg hLpos.le _)
      _ ≤ C' * N' * L ^ (-δ₁) := mul_le_mul_of_nonneg_left hδle (mul_nonneg hC' hN0)
  have hQ0 : 0 ≤ C' * L ^ (-δ₁) := mul_nonneg hC' (Real.rpow_nonneg hLpos.le _)
  have hblk : ∀ a b : ℕ, Ks ≤ a → b ≤ 2 * a → 2 * a < p → ∀ c : ZMod p, c ≠ 0 → ∀ x, a ≤ x →
      x ≤ b → ‖∑ k ∈ (Ico a x).filter Odd, psiP p (c * ((2 * k : ℕ) : ZMod p)⁻¹)‖ ≤
        4 * (C' * L ^ (-δ₁) * (2 * a)) := by
    intro a b hKa hb2 h2a c hc x hax hxb
    have hlogA : Real.log p ^ θ₁ ≤ Real.log ((a : ℝ) / 3) := by
      refine hlogKs.trans (Real.log_le_log (by positivity) ?_)
      have : (Ks : ℝ) ≤ a := by exact_mod_cast hKa
      linarith
    exact block_kloost_KS C' δ₁ θ₁ hC' p hp (by omega) hp2 hKS' a b (le_trans hKs6 hKa) hb2 h2a
      hlogA c hc x hax hxb
  have hRb := R_bound_gen hV p hp hp5 (KWθ θ p) N M Ks J (by omega) hM1' hMp hNp hKs6 hNKs hKsK hK2p
    hKJ (C' * L ^ (-δ₁)) hQ0 hblk _ htail
  -- bounding the right-hand side by `GbK C' γ θ' δ₁ L`
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have hAt : 2 + Real.log N ≤ AtermK γ L := by unfold AtermK; linarith
  have hKs0 : (0 : ℝ) < Ks := by exact_mod_cast (by omega : 0 < Ks)
  have hlKs : 1 + Real.log (Ks : ℝ) ≤ L ^ θ' + 2 := by
    have : Real.log (Ks : ℝ) ≤ L ^ θ' + 1 := by
      rw [Real.log_le_iff_le_exp hKs0, Real.exp_add]
      have : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
      have : (1 : ℝ) ≤ E := by linarith
      change (Ks : ℝ) ≤ E * Real.exp 1
      have hE2 : E * 2 ≤ E * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (by assumption) (by linarith)
      linarith
    linarith
  have hlKs0 : 0 ≤ 1 + Real.log (Ks : ℝ) := by
    have := Real.log_natCast_nonneg Ks; linarith
  have hlK : Real.log (KWθ θ p : ℝ) ≤ L :=
    Real.log_le_log hKpos' (by exact_mod_cast hKp)
  have hlK0 : 0 ≤ 1 + Real.log (KWθ θ p : ℝ) := by
    have := Real.log_natCast_nonneg (KWθ θ p); linarith
  have hHsum : ∑ h ∈ Icc 1 M, 4 / (Real.pi * h) = 4 / Real.pi * ∑ h ∈ Icc 1 M, (1 / h : ℝ) := by
    rw [mul_sum]; apply sum_congr rfl; intro h _; rw [mul_one_div, div_div]
  have hHs0 : 0 ≤ ∑ h ∈ Icc 1 M, 4 / (Real.pi * h) + 4 := by
    have : 0 ≤ ∑ h ∈ Icc 1 M, 4 / (Real.pi * h) := sum_nonneg (fun h _ => by positivity)
    linarith
  have hHs : ∑ h ∈ Icc 1 M, 4 / (Real.pi * h) + 4 ≤ 8 + 4 * Real.log L := by
    rw [hHsum]
    have h1 := sum_inv_le_log (M + 1) (Icc 1 M) (fun k hk => by simp only [mem_Icc] at hk; omega)
    push_cast at h1
    have h2 : Real.log ((M : ℝ) + 1) ≤ Real.log 2 + 2 * Real.log L := by
      rw [← Real.log_rpow (by linarith), ← Real.log_mul (by norm_num) (by positivity)]
      apply Real.log_le_log (by positivity)
      rw [show L ^ (2 : ℝ) = L ^ 2 by norm_cast]
      linarith
    have h3 := Real.log_two_lt_d9
    have h4 := Real.pi_gt_three
    have hs0 : 0 ≤ ∑ h ∈ Icc 1 M, (1 / h : ℝ) := sum_nonneg (fun h _ => by positivity)
    have h5 : 4 / Real.pi ≤ 4 / 3 := by gcongr
    have h6 : 4 / Real.pi * ∑ h ∈ Icc 1 M, (1 / h : ℝ) ≤ 4 / 3 * ∑ h ∈ Icc 1 M, (1 / h : ℝ) :=
      mul_le_mul_of_nonneg_right h5 hs0
    linarith
  have hM2' : (M : ℝ) ≤ 2 * L ^ 2 := by linarith
  have he : T ^ (-(γ / 4)) = Real.exp (-(γ * L ^ γ / 4)) := by
    change Real.exp (L ^ γ) ^ (-(γ / 4)) = _
    rw [← Real.exp_mul]; congr 1; ring
  have key := rhs_le_GbK C' L γ θ' δ₁ (Real.log N) (Real.log Ks) M (Real.log (KWθ θ p)) J
    (∑ h ∈ Icc 1 M, 4 / (Real.pi * h)) M I
    (T ^ (-(γ / 4))) hC' hL1000 hlogN0 hAt hlKs0 hlKs hM1 hlK0 hlK
    hJ2.le hHs0 hHs hM2' (Nat.cast_nonneg _) hIL
    (Real.rpow_nonneg hT0.le _) he.le
  have hR : |RsumK (KWθ θ p) p| ≤ GbK C' γ θ' δ₁ L := by
    refine hRb.trans (le_trans (le_of_eq ?_) key)
    ring
  -- conclusion
  have hR' : -GbK C' γ θ' δ₁ L ≤ RsumK (KWθ θ p) p := (abs_le.mp hR).1
  have h1 : 4 * (p : ℝ) / Real.pi * (-GbK C' γ θ' δ₁ L) ≤ 4 * (p : ℝ) / Real.pi * RsumK (KWθ θ p) p :=
    mul_le_mul_of_nonneg_left hR' (by positivity)
  have h2 : (p : ℝ) * (4 / Real.pi * GbK C' γ θ' δ₁ L + (C1 + n)) < p * (L / 2) :=
    mul_lt_mul_of_pos_left hfin hp0
  have h3 : ((n : ℤ) * p : ℝ) < (S p : ℝ) := by
    have e1 : 4 * (p : ℝ) / Real.pi * (-GbK C' γ θ' δ₁ L) = -((p : ℝ) * (4 / Real.pi * GbK C' γ θ' δ₁ L)) := by ring
    rw [e1] at h1
    have e2 : (p : ℝ) * (4 / Real.pi * GbK C' γ θ' δ₁ L + (C1 + n)) =
        (p : ℝ) * (4 / Real.pi * GbK C' γ θ' δ₁ L) + C1 * p + n * p := by ring
    rw [e2] at h2
    have e3 : (p : ℝ) / 2 * L = (p : ℝ) * (L / 2) := by ring
    push_cast
    linarith
  exact_mod_cast h3


/-- **The lower half of Conjecture 3.3 from (HKS)** (Theorem B with Kloosterman's bound and Vaaler's
lemma are proved). -/
theorem lower_half_HKS (hK : HKS) :
    ∀ n : ℕ, ∀ᶠ k in Filter.atTop, k.Prime → (n : ℤ) * k < S k :=
  lower_half_gen_KS (3 / 4) (by norm_num) le_rfl (HB34_of_HBweak34 hBweak34) hV_holds hK

/-- **Conjecture 3.3** of arXiv:2501.03234, assuming only (HKS): a power-of-log saving for short
Kloosterman sums of length `≥ exp((log p)^θ)`, some `θ < 1`. -/
theorem conjecture_3_3_of_HKS (hK : HKS) : ∀ C₁ C₂ ε : ℝ, 0 < C₁ → 0 < C₂ → 0 < ε →
    ∀ᶠ k : ℕ in Filter.atTop, k.Prime →
      C₁ * k < (S k : ℝ) ∧ (S k : ℝ) < C₂ * (k : ℝ) ^ (1 + ε) :=
  conj_of_lower (lower_half_HKS hK)

end ThetaSum

namespace Arxiv.«2501.03234»

/-- **Conjecture 4.4** (formal-conjectures), in full for every `n`, assuming only (HKS). -/
theorem conjecture_4_4_of_HKS (hK : ThetaSum.HKS) (n : ℕ) : conjecture_4_4 n := by
  unfold conjecture_4_4
  filter_upwards [ThetaSum.lower_half_HKS hK n] with k hk hp _
  rw [ThetaSum.S_bridge]; exact hk hp

end Arxiv.«2501.03234»

#print axioms ThetaSum.HKS_of_HBG
#print axioms ThetaSum.conjecture_3_3_of_HKS
#print axioms Arxiv.«2501.03234».conjecture_4_4_of_HKS
