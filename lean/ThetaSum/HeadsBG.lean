import ThetaSum.Heads

/-
The incomplete Kloosterman sums over odd `k` in a block `[a, x) ⊆ [a, 2a]`, bounded by the
Bourgain–Garaev hypothesis through Lemma 6.4 (`odd_interval_bound`).
-/

open Finset

namespace ThetaSum

/-- The bound of (HBG) at `N`, as a function. -/
noncomputable def bgB (C : ℝ) (p N : ℕ) : ℝ :=
  C * Real.log (Real.log p) ^ 3 * Real.log p * Real.log N ^ (-(3 / 2 : ℝ)) * N

lemma one_term (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 3 ≤ p) (b : ZMod p) (hb : b ≠ 0)
    (hBG : ∀ b : ZMod p, b ≠ 0 → ∀ N : ℕ, Real.log p ^ (9 / 10 : ℝ) / 2 ≤ Real.log N → N < p →
      ‖Tsum p b N‖ ≤ bgB C p N)
    (a N' : ℕ) (ha : 6 ≤ a) (h1 : a ≤ 3 * N') (h2 : N' ≤ 2 * a) (h2a : 2 * a < p)
    (hlog : Real.log p ^ (9 / 10 : ℝ) / 2 ≤ Real.log ((a : ℝ) / 3)) :
    ‖Tsum p b N'‖ ≤ C * Real.log (Real.log p) ^ 3 * Real.log p *
      Real.log ((a : ℝ) / 3) ^ (-(3 / 2 : ℝ)) * (2 * a) := by
  have ha3 : (1 : ℝ) < (a : ℝ) / 3 := by
    rw [lt_div_iff₀ (by norm_num)]; have : (6 : ℝ) ≤ a := by exact_mod_cast ha
    linarith
  have hN'R : (a : ℝ) / 3 ≤ N' := by
    rw [div_le_iff₀ (by norm_num)]; have : (a : ℝ) ≤ 3 * N' := by exact_mod_cast h1
    linarith
  have hla : 0 < Real.log ((a : ℝ) / 3) := Real.log_pos ha3
  have hlN : Real.log ((a : ℝ) / 3) ≤ Real.log N' := Real.log_le_log (by linarith) hN'R
  have hb' := hBG b hb N' (hlog.trans hlN) (by omega)
  refine hb'.trans ?_
  unfold bgB
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hlp : 0 < Real.log p := Real.log_pos hp1
  have hX : 0 ≤ C * Real.log (Real.log p) ^ 3 * Real.log p := by
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
    have : 1 ≤ Real.log p := by
      rw [← Real.log_exp 1]
      apply Real.log_le_log (Real.exp_pos 1)
      linarith [Real.exp_one_lt_d9]
    have : 0 ≤ Real.log (Real.log p) := Real.log_nonneg this
    positivity
  have hpow : Real.log N' ^ (-(3 / 2 : ℝ)) ≤ Real.log ((a : ℝ) / 3) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hla hlN (by norm_num)
  have hN2 : (N' : ℝ) ≤ 2 * a := by exact_mod_cast h2
  have hpos : 0 ≤ Real.log N' ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  calc C * Real.log (Real.log p) ^ 3 * Real.log p * Real.log N' ^ (-(3 / 2 : ℝ)) * N'
      = (C * Real.log (Real.log p) ^ 3 * Real.log p) * (Real.log N' ^ (-(3 / 2 : ℝ)) * N') := by ring
    _ ≤ (C * Real.log (Real.log p) ^ 3 * Real.log p) *
          (Real.log ((a : ℝ) / 3) ^ (-(3 / 2 : ℝ)) * (2 * a)) := by
        apply mul_le_mul_of_nonneg_left _ hX
        exact mul_le_mul hpow hN2 (Nat.cast_nonneg _) (Real.rpow_nonneg hla.le _)
    _ = _ := by ring

/-- **Block Kloosterman bound** from (HBG): for `6 ≤ a`, `x ≤ b ≤ 2a`, `2a < p` and
`log(a/3) ≥ (log p)^{9/10}/2`, every `c ≢ 0` gives
`‖∑_{k ∈ [a,x), k odd} e(c (2k)^{-1}/p)‖ ≤ 4 · C (log log p)³ (log p) (log(a/3))^{-3/2} (2a)`. -/
theorem block_kloost (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hp2 : p ≠ 2)
    (hBG : ∀ b : ZMod p, b ≠ 0 → ∀ N : ℕ, Real.log p ^ (9 / 10 : ℝ) / 2 ≤ Real.log N → N < p →
      ‖Tsum p b N‖ ≤ bgB C p N)
    (a b : ℕ) (ha : 6 ≤ a) (hb : b ≤ 2 * a) (h2a : 2 * a < p)
    (hlog : Real.log p ^ (9 / 10 : ℝ) / 2 ≤ Real.log ((a : ℝ) / 3)) :
    ∀ c : ZMod p, c ≠ 0 → ∀ x, a ≤ x → x ≤ b →
      ‖∑ k ∈ (Ico a x).filter Odd, psiP p (c * ((2 * k : ℕ) : ZMod p)⁻¹)‖ ≤
        4 * (C * Real.log (Real.log p) ^ 3 * Real.log p *
          Real.log ((a : ℝ) / 3) ^ (-(3 / 2 : ℝ)) * (2 * a)) := by
  haveI := Fact.mk hp
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
  have t1 := one_term C hC p hp3 _ hb1 hBG a (x - 1) ha (by omega) (by omega) h2a hlog
  have t2 := one_term C hC p hp3 _ hb1 hBG a (a - 1) ha (by omega) (by omega) h2a hlog
  have t3 := one_term C hC p hp3 _ hb2 hBG a ((x + 1) / 2 - 1) ha (by omega) (by omega) h2a hlog
  have t4 := one_term C hC p hp3 _ hb2 hBG a ((a + 1) / 2 - 1) ha (by omega) (by omega) h2a hlog
  linarith

end ThetaSum

#print axioms ThetaSum.block_kloost
