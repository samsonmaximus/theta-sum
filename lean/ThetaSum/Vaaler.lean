-- Copied verbatim from the companion project (lean-upper/Upper/Vaaler.lean); imports only Mathlib.
import Mathlib

/-!
# Vaaler's lemma

For `H ≥ 1` there are coefficients `a_ℓ` with `|a_ℓ| ≤ 1/(2π|ℓ|)` such that for all real `x`
`|((x)) - Σ_{1≤|ℓ|≤H} a_ℓ e(ℓx)| ≤ (1/(2H+2)) Σ_{|ℓ|≤H} (1 - |ℓ|/(H+1)) e(ℓx)`
(Vaaler, Bull. AMS 12 (1985), Thm 18; Graham–Kolesnik, Thm A.6).

We use Vaaler's explicit coefficients `a_ℓ = -(1/(2πiℓ)) φ(ℓ/(H+1))`,
`φ(t) = πt(1-|t|)cot(πt) + |t|`, and a self-contained *finite* proof (no Fourier analysis on `ℝ`):
with `N = H+1` and `M = ψ* + K/(2N)` (a real trigonometric polynomial of degree `N-1`)
we compute `M(k/N) = k/N - 1/2`, `M'(k/N) = 1` (`1 ≤ k ≤ N-1`), `M(0) = 1/2`, `M'(0) = 1-N`
from finite root-of-unity sums, and then show `D(x) = M(x) - (x - 1/2) ≥ 0` on `[0,1]` by
counting zeros (a nonzero trigonometric polynomial of degree `n` has at most `2n` zeros per
period) of `D'` and `D''` together with Rolle's theorem. The lower bound follows by symmetry.
-/

set_option linter.unusedSectionVars false

namespace Vaaler
open Finset Polynomial Complex

/-- Real trigonometric polynomial `c + Σ_{h=1}^{n} (p_h cos 2πhx + q_h sin 2πhx)`. -/
noncomputable def trig (n : ℕ) (c : ℝ) (p q : ℕ → ℝ) (x : ℝ) : ℝ :=
  c + ∑ h ∈ Ico 1 (n + 1), (p h * Real.cos (2 * Real.pi * h * x) + q h * Real.sin (2 * Real.pi * h * x))

noncomputable def ex (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * x * I)

lemma ex_pow (x : ℝ) (h : ℕ) : ex x ^ h = (Real.cos (2 * Real.pi * h * x) : ℂ) +
    (Real.sin (2 * Real.pi * h * x) : ℂ) * I := by
  unfold ex
  rw [← Complex.exp_nat_mul, show (h : ℂ) * (2 * Real.pi * x * I) =
    ((2 * Real.pi * h * x : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma ex_ne_zero (x : ℝ) : ex x ≠ 0 := Complex.exp_ne_zero _

lemma ex_inj {x y : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) (hy : y ∈ Set.Ico (0 : ℝ) 1)
    (h : ex x = ex y) : x = y := by
  unfold ex at h
  rw [Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨n, hn⟩ := h
  have hn' : (2 * Real.pi * x : ℂ) = 2 * Real.pi * y + n * (2 * Real.pi) := by
    have hI : (I : ℂ) ≠ 0 := I_ne_zero
    have := hn
    rw [show (2 * Real.pi * x * I : ℂ) = (2 * Real.pi * x) * I by ring,
      show (2 * Real.pi * y * I + n * (2 * Real.pi * I) : ℂ) =
        (2 * Real.pi * y + n * (2 * Real.pi)) * I by ring] at this
    exact mul_right_cancel₀ hI this
  have hR : (2 * Real.pi * x : ℝ) = 2 * Real.pi * y + n * (2 * Real.pi) := by exact_mod_cast hn'
  have hxy : x = y + n := by
    have := Real.pi_pos
    have h2 : 2 * Real.pi * x = 2 * Real.pi * (y + n) := by rw [hR]; ring
    exact mul_left_cancel₀ (by positivity) h2
  simp only [Set.mem_Ico] at hx hy
  have : n = 0 := by
    have h1 : (n : ℝ) < 1 := by linarith
    have h2 : (-1 : ℝ) < n := by linarith
    have h1' : n < 1 := by exact_mod_cast h1
    have h2' : -1 < n := by exact_mod_cast h2
    omega
  rw [hxy, this]; simp

/-- The associated polynomial. -/
noncomputable def trigPoly (n : ℕ) (c : ℝ) (p q : ℕ → ℝ) : ℂ[X] :=
  C (c : ℂ) * X ^ n + ∑ h ∈ Ico 1 (n + 1),
    (C (((p h : ℂ) - q h * I) / 2) * X ^ (n + h) + C (((p h : ℂ) + q h * I) / 2) * X ^ (n - h))

lemma trigPoly_natDegree (n : ℕ) (c : ℝ) (p q : ℕ → ℝ) :
    (trigPoly n c p q).natDegree ≤ 2 * n := by
  unfold trigPoly
  apply natDegree_add_le_of_degree_le
  · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  · apply natDegree_sum_le_of_forall_le
    intro h hh
    simp only [mem_Ico] at hh
    apply natDegree_add_le_of_degree_le
    · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
    · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

lemma trigPoly_eval (n : ℕ) (c : ℝ) (p q : ℕ → ℝ) (x : ℝ) :
    (trigPoly n c p q).eval (ex x) = ex x ^ n * (trig n c p q x : ℂ) := by
  unfold trigPoly trig
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_finsetSum, Complex.ofReal_add,
    Complex.ofReal_sum, Complex.ofReal_mul]
  rw [mul_add, mul_sum, mul_comm]
  congr 1
  refine sum_congr rfl fun h hh => ?_
  simp only [mem_Ico] at hh
  have hz := ex_ne_zero x
  have e1 : ex x ^ (n + h) = ex x ^ n * ex x ^ h := pow_add _ _ _
  have e2 : ex x ^ (n - h) = ex x ^ n * (ex x ^ h)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hz), ← pow_add, Nat.sub_add_cancel (by omega)]
  set Cc : ℂ := (Real.cos (2 * Real.pi * h * x) : ℂ) with hCc
  set Ss : ℂ := (Real.sin (2 * Real.pi * h * x) : ℂ) with hSs
  have hcs : Cc ^ 2 + Ss ^ 2 = 1 := by
    have := Real.cos_sq_add_sin_sq (2 * Real.pi * h * x)
    rw [hCc, hSs]; exact_mod_cast this
  have hw : ex x ^ h = Cc + Ss * I := ex_pow x h
  have hinv : (ex x ^ h)⁻¹ = Cc - Ss * I := by
    rw [hw]
    apply inv_eq_of_mul_eq_one_right
    linear_combination hcs - Ss ^ 2 * I_sq
  rw [e1, e2, hinv, hw]
  linear_combination (-(ex x ^ n) * (q h : ℂ) * Ss) * I_sq

/-- A real trigonometric polynomial of degree `≤ n` with more than `2n` distinct zeros in
`[0,1)` vanishes identically. -/
theorem trig_eq_zero_of_card {n : ℕ} {c : ℝ} {p q : ℕ → ℝ} (S : Finset ℝ)
    (hS : ∀ x ∈ S, x ∈ Set.Ico (0 : ℝ) 1) (hz : ∀ x ∈ S, trig n c p q x = 0)
    (hcard : 2 * n < S.card) (y : ℝ) : trig n c p q y = 0 := by
  have hP : trigPoly n c p q = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero (trigPoly n c p q)
      (f := fun x : S => ex x)
    · intro a b hab
      exact Subtype.ext (ex_inj (hS a a.2) (hS b b.2) hab)
    · intro a
      rw [trigPoly_eval, hz a a.2]; simp
    · rw [Fintype.card_coe]; exact (trigPoly_natDegree n c p q).trans_lt hcard
  have := trigPoly_eval n c p q y
  rw [hP, eval_zero] at this
  have h2 : (trig n c p q y : ℂ) = 0 := by
    rcases mul_eq_zero.1 this.symm with h | h
    · exact absurd h (pow_ne_zero _ (ex_ne_zero y))
    · exact h
  exact_mod_cast h2

/-- Formal derivative of a trigonometric polynomial. -/
noncomputable def trigD (n : ℕ) (p q : ℕ → ℝ) (x : ℝ) : ℝ :=
  trig n 0 (fun h => 2 * Real.pi * h * q h) (fun h => -(2 * Real.pi * h) * p h) x

lemma hasDerivAt_trig (n : ℕ) (c : ℝ) (p q : ℕ → ℝ) (x : ℝ) :
    HasDerivAt (trig n c p q) (trigD n p q x) x := by
  unfold trigD trig
  rw [zero_add]
  apply HasDerivAt.const_add
  apply HasDerivAt.fun_sum
  intro h _
  have hc : HasDerivAt (fun y : ℝ => Real.cos (2 * Real.pi * h * y))
      (-Real.sin (2 * Real.pi * h * x) * (2 * Real.pi * h)) x := by
    have := ((hasDerivAt_id x).const_mul (2 * Real.pi * h)).cos
    simpa using this
  have hs : HasDerivAt (fun y : ℝ => Real.sin (2 * Real.pi * h * y))
      (Real.cos (2 * Real.pi * h * x) * (2 * Real.pi * h)) x := by
    have := ((hasDerivAt_id x).const_mul (2 * Real.pi * h)).sin
    simpa using this
  convert (hc.const_mul (p h)).add (hs.const_mul (q h)) using 1
  ring

lemma trig_add_int (n : ℕ) (c : ℝ) (p q : ℕ → ℝ) (x : ℝ) (m : ℤ) :
    trig n c p q (x + m) = trig n c p q x := by
  unfold trig
  congr 1
  refine sum_congr rfl fun h _ => ?_
  have e : 2 * Real.pi * h * (x + m) = 2 * Real.pi * h * x + ((h * m : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast; ring
  rw [e, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

lemma continuous_trig (n : ℕ) (c : ℝ) (p q : ℕ → ℝ) : Continuous (trig n c p q) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_trig n c p q x).continuousAt

/-! ### Finite trigonometric sums at the grid points `k/N` -/

lemma sum_reflect (N : ℕ) (f : ℕ → ℝ) : ∑ h ∈ Ico 1 N, f h = ∑ h ∈ Ico 1 N, f (N - h) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have := sum_Ico_reflect f 1 (n := N) (m := N) (by omega)
  rw [show N + 1 - N = 1 by omega, show N + 1 - 1 = N by omega] at this
  exact this.symm

lemma sum_reflect_avg (N : ℕ) (f : ℕ → ℝ) :
    ∑ h ∈ Ico 1 N, f h = (1 / 2) * ∑ h ∈ Ico 1 N, (f h + f (N - h)) := by
  rw [sum_add_distrib, ← sum_reflect]; ring

lemma sum_reflect_odd (N : ℕ) (f : ℕ → ℝ) (hf : ∀ h ∈ Ico 1 N, f (N - h) = - f h) :
    ∑ h ∈ Ico 1 N, f h = 0 := by
  have h1 := sum_reflect N f
  rw [sum_congr rfl hf, sum_neg_distrib] at h1
  linarith

lemma ex_grid_pow_N {N : ℕ} (hN : 0 < N) (k : ℕ) : ex ((k : ℝ) / N) ^ N = 1 := by
  unfold ex
  rw [← Complex.exp_nat_mul]
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [show (N : ℂ) * (2 * Real.pi * ((k : ℝ) / N : ℝ) * I) = k * (2 * Real.pi * I) by
    push_cast; field_simp]
  exact Complex.exp_nat_mul_two_pi_mul_I k

lemma ex_grid_ne_one {N : ℕ} (hN : 0 < N) {k : ℕ} (hk : ¬ N ∣ k) : ex ((k : ℝ) / N) ≠ 1 := by
  have hprim := Complex.isPrimitiveRoot_exp N hN.ne'
  have e : ex ((k : ℝ) / N) = Complex.exp (2 * Real.pi * I / N) ^ k := by
    unfold ex
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [e, Ne, hprim.pow_eq_one_iff_dvd]
  exact hk

lemma geom_grid_zero {N : ℕ} (hN : 0 < N) {k : ℕ} (hk : ¬ N ∣ k) :
    ∑ h ∈ range N, ex ((k : ℝ) / N) ^ h = 0 := by
  rw [geom_sum_eq (ex_grid_ne_one hN hk), ex_grid_pow_N hN, sub_self, zero_div]

lemma sum_cos_grid {N : ℕ} (hN : 0 < N) {k : ℕ} (hk : ¬ N ∣ k) :
    ∑ h ∈ Ico 1 N, Real.cos (2 * Real.pi * h * ((k : ℝ) / N)) = -1 := by
  have h0 := congrArg Complex.re (geom_grid_zero hN hk)
  simp only [Complex.re_sum, ex_pow, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
    Complex.zero_re] at h0
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hN] at h0
  simp only [Nat.cast_zero, mul_zero, zero_mul, Real.cos_zero] at h0
  linarith

lemma sum_sin_grid {N : ℕ} (hN : 0 < N) (k : ℕ) :
    ∑ h ∈ Ico 1 N, Real.sin (2 * Real.pi * h * ((k : ℝ) / N)) = 0 := by
  apply sum_reflect_odd
  intro h hh
  simp only [mem_Ico] at hh
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Nat.cast_sub hh.2.le, show 2 * Real.pi * ((N : ℝ) - h) * ((k : ℝ) / N) =
    ((k : ℕ) : ℝ) * (2 * Real.pi) - 2 * Real.pi * h * ((k : ℝ) / N) by field_simp,
    Real.sin_nat_mul_two_pi_sub]

/-- `Σ_{h<n} h z^h` closed form. -/
lemma sum_mul_geom (z : ℂ) (n : ℕ) :
    (z - 1) * ∑ h ∈ range n, (h : ℂ) * z ^ h = n * z ^ n - ∑ h ∈ range (n + 1), z ^ h + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih, sum_range_succ _ (n + 1)]
    push_cast
    ring

lemma sum_h_cos_grid {N : ℕ} (hN : 0 < N) {k : ℕ} (hk : ¬ N ∣ k) :
    ∑ h ∈ Ico 1 N, (h : ℝ) * Real.cos (2 * Real.pi * h * ((k : ℝ) / N)) = -(N : ℝ) / 2 := by
  set z := ex ((k : ℝ) / N) with hz
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.2 (ex_grid_ne_one hN hk)
  have hS := sum_mul_geom z N
  rw [sum_range_succ, geom_grid_zero hN hk, ex_grid_pow_N hN] at hS
  have hS' : ∑ h ∈ range N, (h : ℂ) * z ^ h = N / (z - 1) := by
    rw [eq_div_iff hz1, mul_comm, hS]; ring
  -- real part of `N/(z-1)` is `-N/2`
  set c := Real.cos (2 * Real.pi * ((k : ℝ) / N)) with hc
  set s := Real.sin (2 * Real.pi * ((k : ℝ) / N)) with hs
  have hzcs : z = (c : ℂ) + (s : ℂ) * I := by
    have := ex_pow ((k : ℝ) / N) 1
    simp only [pow_one, Nat.cast_one, mul_one] at this
    rw [hz, this]
  have hcs : c ^ 2 + s ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  have hc1 : c ≠ 1 := by
    intro h1
    have : s = 0 := by nlinarith
    apply hz1; rw [hzcs, h1, this]; simp
  have hre : (N / (z - 1) : ℂ).re = -(N : ℝ) / 2 := by
    rw [hzcs, Complex.div_re]
    simp only [Complex.natCast_re, Complex.natCast_im, Complex.sub_re, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      Complex.one_re, Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.one_im,
      Complex.normSq_apply]
    have hd : (c - 1) * (c - 1) + s * s ≠ 0 := by
      have : (c - 1) ^ 2 > 0 := by
        have : c - 1 ≠ 0 := sub_ne_zero.2 hc1
        positivity
      nlinarith
    norm_num
    have hd' : (c - 1) * (c - 1) + s * s = 2 * (1 - c) := by nlinarith
    have h1c : 1 - c ≠ 0 := sub_ne_zero.2 (Ne.symm hc1)
    rw [hd', div_eq_iff (by positivity), eq_comm]
    field_simp
    ring
  have h0 := congrArg Complex.re hS'
  rw [hre, Complex.re_sum] at h0
  simp only [hz, ex_pow, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.add_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, add_zero] at h0
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hN] at h0
  simp only [Nat.cast_zero, zero_mul, zero_add] at h0
  linarith

lemma cos_refl {N : ℕ} (hN : 0 < N) {h : ℕ} (hh : h ≤ N) (k : ℕ) :
    Real.cos (2 * Real.pi * ((N - h : ℕ) : ℝ) * ((k : ℝ) / N)) =
      Real.cos (2 * Real.pi * h * ((k : ℝ) / N)) := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Nat.cast_sub hh, show 2 * Real.pi * ((N : ℝ) - h) * ((k : ℝ) / N) =
    ((k : ℕ) : ℝ) * (2 * Real.pi) - 2 * Real.pi * h * ((k : ℝ) / N) by field_simp,
    Real.cos_nat_mul_two_pi_sub]

lemma sin_refl {N : ℕ} (hN : 0 < N) {h : ℕ} (hh : h ≤ N) (k : ℕ) :
    Real.sin (2 * Real.pi * ((N - h : ℕ) : ℝ) * ((k : ℝ) / N)) =
      -Real.sin (2 * Real.pi * h * ((k : ℝ) / N)) := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Nat.cast_sub hh, show 2 * Real.pi * ((N : ℝ) - h) * ((k : ℝ) / N) =
    ((k : ℕ) : ℝ) * (2 * Real.pi) - 2 * Real.pi * h * ((k : ℝ) / N) by field_simp,
    Real.sin_nat_mul_two_pi_sub]

lemma cot_refl {N : ℕ} (hN : 0 < N) {h : ℕ} (hh : h ≤ N) :
    Real.cot (Real.pi * ((N - h : ℕ) : ℝ) / N) = -Real.cot (Real.pi * h / N) := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Nat.cast_sub hh, show Real.pi * ((N : ℝ) - h) / N = Real.pi - Real.pi * h / N by field_simp,
    Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cos_pi_sub, Real.sin_pi_sub, neg_div]

/-- `Σ_{h=1}^{N-1} cot(πh/N) sin(2πhk/N) = N - 2k` for `1 ≤ k ≤ N - 1`. -/
lemma sum_cot_sin_grid {N : ℕ} (hN : 0 < N) (k : ℕ) (hk : k ≤ N - 1) :
    ∑ h ∈ Ico 1 N, Real.cot (Real.pi * h / N) * Real.sin (2 * Real.pi * h * ((k : ℝ) / N)) =
      if k = 0 then 0 else (N : ℝ) - 2 * k := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  induction k with
  | zero => simp
  | succ k ih =>
    have ih := ih (by omega)
    have step : ∀ h ∈ Ico 1 N, Real.cot (Real.pi * h / N) *
        Real.sin (2 * Real.pi * h * (((k + 1 : ℕ) : ℝ) / N)) =
        Real.cot (Real.pi * h / N) * Real.sin (2 * Real.pi * h * ((k : ℝ) / N)) +
        (Real.cos (2 * Real.pi * h * (((k + 1 : ℕ) : ℝ) / N)) +
          Real.cos (2 * Real.pi * h * ((k : ℝ) / N))) := by
      intro h hh
      simp only [mem_Ico] at hh
      have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh.1
      have hhN : (h : ℝ) < N := by exact_mod_cast hh.2
      set a := Real.pi * h / N with ha
      have hsa : Real.sin a ≠ 0 := by
        apply (Real.sin_pos_of_pos_of_lt_pi (by positivity) _).ne'
        rw [ha, div_lt_iff₀ hNR]; nlinarith [Real.pi_pos]
      set u := a * (2 * k + 1) with hu
      have e1 : 2 * Real.pi * h * (((k + 1 : ℕ) : ℝ) / N) = u + a := by
        rw [hu, ha]; push_cast; field_simp; ring
      have e2 : 2 * Real.pi * h * ((k : ℝ) / N) = u - a := by
        rw [hu, ha]; field_simp; ring
      rw [e1, e2, Real.sin_add, Real.sin_sub, Real.cos_add, Real.cos_sub, Real.cot_eq_cos_div_sin]
      field_simp
      ring
    rw [sum_congr rfl step, sum_add_distrib, sum_add_distrib, ih,
      sum_cos_grid hN (k := k + 1) (by intro hd; exact absurd (Nat.le_of_dvd (by omega) hd) (by omega))]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [Nat.cast_zero, zero_div, mul_zero, Real.cos_zero, sum_const, Nat.card_Ico,
        nsmul_eq_mul, mul_one, ite_true]
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    · rw [sum_cos_grid hN (k := k) (by intro hd; exact absurd (Nat.le_of_dvd hk0 hd) (by omega))]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      push_cast; ring

/-! ### Vaaler's polynomial -/

/-- Sine coefficients of `ψ*`: `-(1/N)((1-h/N) cot(πh/N) + 1/π)`. -/
noncomputable def al (N : ℕ) (h : ℕ) : ℝ :=
  -(1 / N) * ((1 - h / N) * Real.cot (Real.pi * h / N) + 1 / Real.pi)

/-- Cosine coefficients of `K/(2N)`: `(1/N)(1 - h/N)`. -/
noncomputable def be (N : ℕ) (h : ℕ) : ℝ := (1 / N) * (1 - h / N)

/-- The majorant `M = ψ* + K/(2N)`. -/
noncomputable def Mf (N : ℕ) : ℝ → ℝ := trig (N - 1) (1 / (2 * N)) (be N) (al N)
noncomputable def M1 (N : ℕ) : ℝ → ℝ := trigD (N - 1) (be N) (al N)
noncomputable def M2 (N : ℕ) : ℝ → ℝ :=
  trigD (N - 1) (fun h => 2 * Real.pi * h * al N h) (fun h => -(2 * Real.pi * h) * be N h)

lemma Ico_N {N : ℕ} (hN : 0 < N) : Ico 1 (N - 1 + 1) = Ico 1 N := by
  rw [Nat.sub_add_cancel hN]

lemma Mf_grid {N : ℕ} (hN : 0 < N) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ N - 1) :
    Mf N ((k : ℝ) / N) = k / N - 1 / 2 := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hnd : ¬ N ∣ k := fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega)
  unfold Mf trig
  rw [Ico_N hN, sum_add_distrib]
  have h1 : ∑ h ∈ Ico 1 N, be N h * Real.cos (2 * Real.pi * h * ((k : ℝ) / N)) = -1 / (2 * N) := by
    rw [sum_reflect_avg]
    have : ∀ h ∈ Ico 1 N, be N h * Real.cos (2 * Real.pi * h * ((k : ℝ) / N)) +
        be N (N - h) * Real.cos (2 * Real.pi * ((N - h : ℕ) : ℝ) * ((k : ℝ) / N)) =
        (1 / N) * Real.cos (2 * Real.pi * h * ((k : ℝ) / N)) := by
      intro h hh
      simp only [mem_Ico] at hh
      rw [cos_refl hN hh.2.le, be, be, Nat.cast_sub hh.2.le]
      field_simp; ring
    rw [sum_congr rfl this, ← mul_sum, sum_cos_grid hN hnd]
    field_simp
  have h2 : ∑ h ∈ Ico 1 N, al N h * Real.sin (2 * Real.pi * h * ((k : ℝ) / N)) =
      k / N - 1 / 2 := by
    have : ∀ h ∈ Ico 1 N, al N h * Real.sin (2 * Real.pi * h * ((k : ℝ) / N)) =
        -(1 / N) * ((1 - h / N) * (Real.cot (Real.pi * h / N) *
          Real.sin (2 * Real.pi * h * ((k : ℝ) / N)))) +
        -(1 / (N * Real.pi)) * Real.sin (2 * Real.pi * h * ((k : ℝ) / N)) := by
      intro h _; rw [al]; field_simp; ring
    rw [sum_congr rfl this, sum_add_distrib, ← mul_sum, ← mul_sum, sum_sin_grid hN, mul_zero,
      add_zero, sum_reflect_avg]
    have : ∀ h ∈ Ico 1 N, (1 - (h : ℝ) / N) * (Real.cot (Real.pi * h / N) *
          Real.sin (2 * Real.pi * h * ((k : ℝ) / N))) +
        (1 - ((N - h : ℕ) : ℝ) / N) * (Real.cot (Real.pi * ((N - h : ℕ) : ℝ) / N) *
          Real.sin (2 * Real.pi * ((N - h : ℕ) : ℝ) * ((k : ℝ) / N))) =
        Real.cot (Real.pi * h / N) * Real.sin (2 * Real.pi * h * ((k : ℝ) / N)) := by
      intro h hh
      simp only [mem_Ico] at hh
      rw [cot_refl hN hh.2.le, sin_refl hN hh.2.le, Nat.cast_sub hh.2.le]
      field_simp; ring
    rw [sum_congr rfl this, sum_cot_sin_grid hN k hk, ite_eq_right (by omega)]
    field_simp; ring
  rw [h1, h2]; field_simp; ring

lemma Mf_zero {N : ℕ} (hN : 0 < N) : Mf N 0 = 1 / 2 := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold Mf trig
  simp only [mul_zero, Real.cos_zero, Real.sin_zero, mul_one, add_zero]
  rw [Ico_N hN, sum_reflect_avg]
  have : ∀ h ∈ Ico 1 N, be N h + be N (N - h) = 1 / N := by
    intro h hh
    simp only [mem_Ico] at hh
    rw [be, be, Nat.cast_sub hh.2.le]; field_simp; ring
  rw [sum_congr rfl this, sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub (by omega)]
  field_simp; push_cast; ring

lemma M1_grid {N : ℕ} (hN : 0 < N) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ N - 1) :
    M1 N ((k : ℝ) / N) = 1 := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hnd : ¬ N ∣ k := fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega)
  unfold M1 trigD trig
  rw [Ico_N hN, zero_add, sum_add_distrib]
  have h1 : ∑ h ∈ Ico 1 N, 2 * Real.pi * h * al N h * Real.cos (2 * Real.pi * h * ((k : ℝ) / N)) = 1 := by
    have : ∀ h ∈ Ico 1 N, 2 * Real.pi * h * al N h * Real.cos (2 * Real.pi * h * ((k : ℝ) / N)) =
        -(2 * Real.pi / N) * ((h * (1 - h / N)) * Real.cot (Real.pi * h / N) *
          Real.cos (2 * Real.pi * h * ((k : ℝ) / N))) +
        -(2 / N) * ((h : ℝ) * Real.cos (2 * Real.pi * h * ((k : ℝ) / N))) := by
      intro h _; rw [al]; field_simp; ring
    rw [sum_congr rfl this, sum_add_distrib, ← mul_sum, ← mul_sum, sum_h_cos_grid hN hnd]
    rw [sum_reflect_odd N _ (fun h hh => by
      simp only [mem_Ico] at hh
      rw [cot_refl hN hh.2.le, cos_refl hN hh.2.le, Nat.cast_sub hh.2.le]
      field_simp; ring)]
    field_simp; ring
  have h2 : ∑ h ∈ Ico 1 N, -(2 * Real.pi * h) * be N h * Real.sin (2 * Real.pi * h * ((k : ℝ) / N)) = 0 := by
    apply sum_reflect_odd
    intro h hh
    simp only [mem_Ico] at hh
    rw [sin_refl hN hh.2.le, be, be, Nat.cast_sub hh.2.le]
    field_simp; ring
  rw [h1, h2, add_zero]

lemma M1_zero {N : ℕ} (hN : 0 < N) : M1 N 0 = 1 - N := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold M1 trigD trig
  simp only [mul_zero, Real.cos_zero, Real.sin_zero, mul_one, add_zero, zero_add]
  rw [Ico_N hN]
  have : ∀ h ∈ Ico 1 N, 2 * Real.pi * h * al N h =
      -(2 * Real.pi / N) * ((h * (1 - h / N)) * Real.cot (Real.pi * h / N)) + -(2 / N) * (h : ℝ) := by
    intro h _; rw [al]; field_simp; ring
  rw [sum_congr rfl this, sum_add_distrib, ← mul_sum, ← mul_sum]
  rw [sum_reflect_odd N _ (fun h hh => by
      simp only [mem_Ico] at hh
      rw [cot_refl hN hh.2.le, Nat.cast_sub hh.2.le]
      field_simp; ring)]
  have hs : ∑ h ∈ Ico 1 N, (h : ℝ) = N * (N - 1) / 2 := by
    rw [sum_reflect_avg]
    have : ∀ h ∈ Ico 1 N, (h : ℝ) + ((N - h : ℕ) : ℝ) = N := by
      intro h hh; simp only [mem_Ico] at hh; rw [Nat.cast_sub hh.2.le]; ring
    rw [sum_congr rfl this, sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub (by omega)]
    push_cast; ring
  rw [hs]; field_simp; ring

/-! ### The sign analysis: `M(x) ≥ x - 1/2` on `[0,1]` -/

noncomputable def Dv (N : ℕ) (x : ℝ) : ℝ := Mf N x - x + 1 / 2
noncomputable def Ev (N : ℕ) (x : ℝ) : ℝ := M1 N x - 1

lemma hasDerivAt_Mf (N : ℕ) (x : ℝ) : HasDerivAt (Mf N) (M1 N x) x :=
  hasDerivAt_trig _ _ _ _ x

lemma hasDerivAt_M1 (N : ℕ) (x : ℝ) : HasDerivAt (M1 N) (M2 N x) x :=
  hasDerivAt_trig _ _ _ _ x

lemma hasDerivAt_Dv (N : ℕ) (x : ℝ) : HasDerivAt (Dv N) (Ev N x) x := by
  unfold Dv Ev
  exact ((hasDerivAt_Mf N x).sub (hasDerivAt_id x)).add_const _

lemma hasDerivAt_Ev (N : ℕ) (x : ℝ) : HasDerivAt (Ev N) (M2 N x) x := by
  unfold Ev
  exact (hasDerivAt_M1 N x).sub_const _

lemma continuous_Dv (N : ℕ) : Continuous (Dv N) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_Dv N x).continuousAt

lemma continuous_Ev (N : ℕ) : Continuous (Ev N) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_Ev N x).continuousAt

lemma Ev_add_int (N : ℕ) (x : ℝ) (m : ℤ) : Ev N (x + m) = Ev N x := by
  unfold Ev M1 trigD; rw [trig_add_int]

lemma M2_add_int (N : ℕ) (x : ℝ) (m : ℤ) : M2 N (x + m) = M2 N x := by
  unfold M2 trigD; rw [trig_add_int]

lemma Ev_trig (N : ℕ) (x : ℝ) : Ev N x = trig (N - 1) (-1)
    (fun h => 2 * Real.pi * h * al N h) (fun h => -(2 * Real.pi * h) * be N h) x := by
  unfold Ev M1 trigD trig; ring

lemma M2_trig (N : ℕ) (x : ℝ) : M2 N x = trig (N - 1) 0
    (fun h => 2 * Real.pi * h * (-(2 * Real.pi * h) * be N h))
    (fun h => -(2 * Real.pi * h) * (2 * Real.pi * h * al N h)) x := rfl

section Sign

variable {N : ℕ} (hN : 2 ≤ N)
include hN

lemma Dv_grid {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ N - 1) : Dv N ((k : ℝ) / N) = 0 := by
  unfold Dv; rw [Mf_grid (by omega) hk1 hk]; ring

lemma Dv_one : Dv N 1 = 0 := by
  have := trig_add_int (N - 1) (1 / (2 * N)) (be N) (al N) 0 1
  simp only [zero_add, Int.cast_one] at this
  unfold Dv; rw [Mf, this, ← Mf, Mf_zero (by omega)]; ring

lemma Dv_zero : Dv N 0 = 1 := by
  unfold Dv; rw [Mf_zero (by omega)]; ring

lemma Ev_grid {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ N - 1) : Ev N ((k : ℝ) / N) = 0 := by
  unfold Ev; rw [M1_grid (by omega) hk1 hk]; ring

lemma Ev_zero : Ev N 0 = -N := by
  unfold Ev; rw [M1_zero (by omega)]; ring

lemma grid_lt {k l : ℕ} (h : k < l) : (k : ℝ) / N < (l : ℝ) / N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  exact div_lt_div_of_pos_right (by exact_mod_cast h) hNR

lemma grid_N : ((N : ℕ) : ℝ) / N = 1 := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  field_simp

/-- Rolle points `r_k ∈ (k/N, (k+1)/N)` with `E(r_k) = 0`. -/
lemma exists_rolle (k : ℕ) : ∃ r : ℝ, 1 ≤ k → k ≤ N - 1 →
    r ∈ Set.Ioo ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N) ∧ Ev N r = 0 := by
  by_cases hk : 1 ≤ k ∧ k ≤ N - 1
  · have hlt := grid_lt hN (show k < k + 1 by omega)
    have h1 : Dv N ((k : ℝ) / N) = Dv N (((k + 1 : ℕ) : ℝ) / N) := by
      rw [Dv_grid hN hk.1 hk.2]
      rcases Nat.lt_or_ge (k + 1) N with h | h
      · rw [Dv_grid hN (by omega) (by omega)]
      · rw [show k + 1 = N by omega, grid_N hN, Dv_one hN]
    obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hlt (continuous_Dv N).continuousOn h1
      (fun x _ => hasDerivAt_Dv N x)
    exact ⟨c, fun _ _ => ⟨hc, hc0⟩⟩
  · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩

end Sign

noncomputable def rr (N k : ℕ) : ℝ :=
  if h : 2 ≤ N then Classical.choose (exists_rolle h k) else 0

noncomputable def gr (N k : ℕ) : ℝ := (k : ℝ) / N

/-- Knots: `z_{2i} = (i+1)/N`, `z_{2i+1} = r_{i+1}`. -/
noncomputable def zk (N j : ℕ) : ℝ := if j % 2 = 0 then gr N (j / 2 + 1) else rr N (j / 2 + 1)

section Sign2

variable {N : ℕ} (hN : 2 ≤ N)
include hN

lemma rr_spec {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ N - 1) :
    rr N k ∈ Set.Ioo (gr N k) (gr N (k + 1)) ∧ Ev N (rr N k) = 0 := by
  unfold rr gr; rw [dite_eq_left hN]
  exact Classical.choose_spec (exists_rolle hN k) hk1 hk

lemma zk_lt_succ {j : ℕ} (hj : j + 1 < 2 * N - 2) : zk N j < zk N (j + 1) := by
  unfold zk
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [ite_eq_left h, ite_eq_right (by omega), show (j + 1) / 2 = j / 2 by omega]
    exact (rr_spec hN (by omega) (by omega)).1.1
  · rw [ite_eq_right (by omega), ite_eq_left (by omega), show (j + 1) / 2 = j / 2 + 1 by omega]
    exact (rr_spec hN (by omega) (by omega)).1.2

lemma zk_strictMono {a b : ℕ} (hab : a < b) (hb : b < 2 * N - 2) : zk N a < zk N b := by
  induction b, hab using Nat.le_induction with
  | base => exact zk_lt_succ hN hb
  | succ b hab ih => exact (ih (by omega)).trans (zk_lt_succ hN hb)

lemma zk_mono {a b : ℕ} (hab : a ≤ b) (hb : b < 2 * N - 2) : zk N a ≤ zk N b := by
  rcases hab.lt_or_eq with h | h
  · exact (zk_strictMono hN h hb).le
  · rw [h]

lemma zk_zero : zk N 0 = gr N 1 := by unfold zk; simp

lemma zk_last : zk N (2 * N - 3) = rr N (N - 1) := by
  unfold zk; rw [ite_eq_right (by omega), show (2 * N - 3) / 2 + 1 = N - 1 by omega]

lemma zk_grid {k : ℕ} (hk1 : 1 ≤ k) : zk N (2 * k - 2) = gr N k := by
  unfold zk; rw [ite_eq_left (by omega), show (2 * k - 2) / 2 + 1 = k by omega]

lemma zk_rr {k : ℕ} (hk1 : 1 ≤ k) : zk N (2 * k - 1) = rr N k := by
  unfold zk; rw [ite_eq_right (by omega), show (2 * k - 1) / 2 + 1 = k by omega]

lemma gr_pos {k : ℕ} (hk : 1 ≤ k) : 0 < gr N k := by
  unfold gr
  have : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  positivity

lemma gr_N : gr N N = 1 := grid_N hN

lemma gr_lt {k l : ℕ} (h : k < l) : gr N k < gr N l := grid_lt hN h

lemma zk_mem {j : ℕ} (hj : j < 2 * N - 2) : zk N j ∈ Set.Ioo (0 : ℝ) 1 ∧ gr N 1 ≤ zk N j ∧
    zk N j ≤ rr N (N - 1) := by
  have h0 : gr N 1 ≤ zk N j := zk_zero hN ▸ zk_mono hN (Nat.zero_le j) hj
  have h1 : zk N j ≤ rr N (N - 1) := zk_last hN ▸ zk_mono hN (by omega) (by omega)
  have h2 : rr N (N - 1) < 1 := by
    have := (rr_spec hN (k := N - 1) (by omega) le_rfl).1.2
    rwa [show N - 1 + 1 = N by omega, gr_N hN] at this
  exact ⟨⟨(gr_pos hN le_rfl).trans_le h0, h1.trans_lt h2⟩, h0, h1⟩

lemma Ev_zk {j : ℕ} (hj : j < 2 * N - 2) : Ev N (zk N j) = 0 := by
  unfold zk
  split_ifs with h
  · unfold gr; exact Ev_grid hN (by omega) (by omega)
  · exact (rr_spec hN (by omega) (by omega)).2

lemma zk_injOn : Set.InjOn (zk N) (range (2 * N - 2) : Set ℕ) := by
  intro a ha b hb hab
  simp only [coe_range, Set.mem_Iio] at ha hb
  rcases lt_trichotomy a b with h | h | h
  · exact absurd hab (zk_strictMono hN h hb).ne
  · exact h
  · exact absurd hab (zk_strictMono hN h ha).ne'

/-- The zeros of `E` in `[0,1)` are exactly the knots. -/
lemma Ev_zero_knot {y : ℝ} (hy : y ∈ Set.Ico (0 : ℝ) 1) (hE : Ev N y = 0) :
    ∃ j < 2 * N - 2, zk N j = y := by
  by_contra hcon
  push Not at hcon
  have hyS : y ∉ (range (2 * N - 2)).image (zk N) := by
    simp only [mem_image, mem_range, not_exists, not_and]
    exact fun j hj => hcon j hj
  set S := insert y ((range (2 * N - 2)).image (zk N)) with hS
  have hcard : S.card = 2 * N - 1 := by
    rw [hS, card_insert_of_notMem hyS, card_image_of_injOn (zk_injOn hN), card_range]; omega
  have := trig_eq_zero_of_card (n := N - 1) (c := -1)
    (p := fun h => 2 * Real.pi * h * al N h) (q := fun h => -(2 * Real.pi * h) * be N h) S
    (by
      intro x hx
      rw [hS, mem_insert, mem_image] at hx
      rcases hx with rfl | ⟨j, hj, rfl⟩
      · exact hy
      · simp only [mem_range] at hj
        exact ⟨(zk_mem hN hj).1.1.le, (zk_mem hN hj).1.2⟩)
    (by
      intro x hx
      rw [← Ev_trig]
      rw [hS, mem_insert, mem_image] at hx
      rcases hx with rfl | ⟨j, hj, rfl⟩
      · exact hE
      · simp only [mem_range] at hj; exact Ev_zk hN hj)
    (by omega) 0
  rw [← Ev_trig, Ev_zero hN] at this
  have : (N : ℝ) = 0 := by linarith
  have : N = 0 := by exact_mod_cast this
  omega

end Sign2


section Sign3

variable {N : ℕ} (hN : 2 ≤ N)
include hN

/-- Upper knot used for Rolle on `E`: `z_{j+1}`, or `1 + z_0` after the last knot. -/
noncomputable def zk' (N j : ℕ) : ℝ := if j + 1 < 2 * N - 2 then zk N (j + 1) else 1 + zk N 0

omit hN in
lemma zk'_eq {j : ℕ} (hj : j + 1 < 2 * N - 2) : zk' N j = zk N (j + 1) := by
  unfold zk'; rw [ite_eq_left hj]

lemma Ev_zk' {j : ℕ} (hj : j < 2 * N - 2) : Ev N (zk' N j) = 0 := by
  unfold zk'
  split_ifs with h
  · exact Ev_zk hN h
  · rw [add_comm, show (1 : ℝ) = ((1 : ℤ) : ℝ) by simp, Ev_add_int]
    exact Ev_zk hN (by omega)

lemma zk_lt_zk' {j : ℕ} (hj : j < 2 * N - 2) : zk N j < zk' N j := by
  unfold zk'
  split_ifs with h
  · exact zk_lt_succ hN h
  · have := (zk_mem hN hj).1.2
    have := (zk_mem hN (j := 0) (by omega)).1.1
    linarith

lemma zk'_le {j : ℕ} (_hj : j < 2 * N - 2) : zk' N j ≤ 1 + zk N 0 := by
  unfold zk'
  split_ifs with h
  · have := (zk_mem hN h).1.2
    have := (zk_mem hN (j := 0) (by omega)).1.1
    linarith
  · exact le_rfl

lemma exists_w (j : ℕ) : ∃ w : ℝ, j < 2 * N - 2 → w ∈ Set.Ioo (zk N j) (zk' N j) ∧ M2 N w = 0 := by
  by_cases hj : j < 2 * N - 2
  · obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero (zk_lt_zk' hN hj)
      (continuous_Ev N).continuousOn (by rw [Ev_zk hN hj, Ev_zk' hN hj])
      (fun x _ => hasDerivAt_Ev N x)
    exact ⟨c, fun _ => ⟨hc, hc0⟩⟩
  · exact ⟨0, fun h => absurd h hj⟩

omit hN in
lemma M1_const_of (h : ∀ x, M2 N x = 0) : M1 N 0 = M1 N (gr N 1) := by
  have hd : Differentiable ℝ (M1 N) := fun x => (hasDerivAt_M1 N x).differentiableAt
  exact is_const_of_deriv_eq_zero hd (fun x => by rw [(hasDerivAt_M1 N x).deriv, h]) _ _

/-- `E'' = M2` does not vanish at the interior grid points. -/
lemma M2_grid_ne {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ N - 1) : M2 N (gr N k) ≠ 0 := by
  intro hM
  choose w hw using exists_w hN
  have hz0 := (zk_mem hN (j := 0) (by omega)).1.1
  have hwI : ∀ j < 2 * N - 2, zk N 0 < w j ∧ w j < 1 + zk N 0 := by
    intro j hj
    obtain ⟨⟨h1, h2⟩, _⟩ := hw j hj
    exact ⟨(zk_mono hN (Nat.zero_le j) hj).trans_lt h1, h2.trans_le (zk'_le hN hj)⟩
  have hwlt : ∀ a b, a < b → b < 2 * N - 2 → w a < w b := by
    intro a b hab hb
    induction b, hab using Nat.le_induction with
    | base =>
      have h1 := (hw a (by omega)).1.2
      rw [zk'_eq (by omega)] at h1
      exact h1.trans (hw (a + 1) hb).1.1
    | succ b hab ih =>
      have h1 := (hw b (by omega)).1.2
      rw [zk'_eq (by omega)] at h1
      exact (ih (by omega)).trans (h1.trans (hw (b + 1) hb).1.1)
  -- equal fractional parts inside a unit window
  have hwin : ∀ a b : ℝ, zk N 0 ≤ a → a < 1 + zk N 0 → zk N 0 ≤ b → b < 1 + zk N 0 →
      Int.fract a = Int.fract b → a = b := by
    intro a b ha1 ha2 hb1 hb2 hab
    obtain ⟨m, hm⟩ := Int.fract_eq_fract.1 hab
    have h1 : (m : ℝ) < 1 := by linarith
    have h2 : (-1 : ℝ) < m := by linarith
    have : m = 0 := by
      have h1' : m < 1 := by exact_mod_cast h1
      have h2' : -1 < m := by exact_mod_cast h2
      omega
    rw [this] at hm; simp at hm; linarith
  set v : ℕ → ℝ := fun j => Int.fract (w j) with hv
  have hvinj : Set.InjOn v (range (2 * N - 2) : Set ℕ) := by
    intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    have := hwin _ _ (hwI a ha).1.le (hwI a ha).2 (hwI b hb).1.le (hwI b hb).2 hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd this (hwlt a b h hb).ne
    · exact h
    · exact absurd this (hwlt b a h ha).ne'
  have hgk : gr N k = zk N (2 * k - 2) := (zk_grid hN hk1).symm
  have hgnot : gr N k ∉ (range (2 * N - 2)).image v := by
    simp only [mem_image, mem_range, not_exists, not_and]
    intro j hj hvj
    have hgm := zk_mem hN (j := 2 * k - 2) (by omega)
    have hgw : zk N 0 ≤ gr N k := by rw [hgk]; exact zk_mono hN (Nat.zero_le _) (by omega)
    have hfr : Int.fract (gr N k) = gr N k := by
      rw [Int.fract_eq_self]; exact ⟨(gr_pos hN hk1).le, hgk ▸ hgm.1.2⟩
    have heq : w j = gr N k := hwin _ _ (hwI j hj).1.le (hwI j hj).2 hgw
      (by linarith [hgm.1.2]) (by rw [hfr]; exact hvj)
    obtain ⟨⟨h1, h2⟩, _⟩ := hw j hj
    rcases Nat.lt_or_ge j (2 * k - 2) with hjk | hjk
    · have := zk_mono hN (show j + 1 ≤ 2 * k - 2 by omega) (by omega)
      rw [zk'_eq (by omega)] at h2
      rw [heq, hgk] at h2
      linarith
    · have := zk_mono hN hjk hj
      rw [heq, hgk] at h1
      linarith
  set T := insert (gr N k) ((range (2 * N - 2)).image v) with hT
  have hcard : T.card = 2 * N - 1 := by
    rw [hT, card_insert_of_notMem hgnot, card_image_of_injOn hvinj, card_range]; omega
  have hall := trig_eq_zero_of_card (n := N - 1) (c := 0)
    (p := fun h => 2 * Real.pi * h * (-(2 * Real.pi * h) * be N h))
    (q := fun h => -(2 * Real.pi * h) * (2 * Real.pi * h * al N h)) T
    (by
      intro x hx
      rw [hT, mem_insert, mem_image] at hx
      rcases hx with rfl | ⟨j, hj, rfl⟩
      · exact ⟨(gr_pos hN hk1).le, hgk ▸ (zk_mem hN (j := 2 * k - 2) (by omega)).1.2⟩
      · exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩)
    (by
      intro x hx
      rw [← M2_trig]
      rw [hT, mem_insert, mem_image] at hx
      rcases hx with rfl | ⟨j, hj, rfl⟩
      · exact hM
      · simp only [mem_range] at hj
        simp only [hv]
        rw [Int.fract, sub_eq_add_neg, show -((⌊w j⌋ : ℤ) : ℝ) = ((-⌊w j⌋ : ℤ) : ℝ) by push_cast; ring,
          M2_add_int]
        exact (hw j hj).2)
    (by omega)
  have hc := M1_const_of (N := N) (fun x => by rw [M2_trig]; exact hall x)
  rw [M1_zero (by omega)] at hc
  unfold gr at hc
  rw [show ((1 : ℕ) : ℝ) = 1 by simp] at hc
  have := M1_grid (N := N) (by omega) (k := 1) le_rfl (by omega)
  push_cast at this
  rw [this] at hc
  have : (N : ℝ) = 0 := by linarith
  have : N = 0 := by exact_mod_cast this
  omega

end Sign3


lemma neg_on_of {f : ℝ → ℝ} (hf : Continuous f) {p q y0 : ℝ} (hy0 : y0 ∈ Set.Ioo p q)
    (hneg : f y0 < 0) (hnz : ∀ y ∈ Set.Ioo p q, f y ≠ 0) : ∀ y ∈ Set.Ioo p q, f y < 0 := by
  intro y hy
  by_contra h
  push Not at h
  have h0 : (0 : ℝ) ∈ Set.uIcc (f y0) (f y) := Set.mem_uIcc.2 (Or.inl ⟨hneg.le, h⟩)
  obtain ⟨c, hc, hfc⟩ := intermediate_value_uIcc hf.continuousOn h0
  have hcI : c ∈ Set.Ioo p q := by
    rcases Set.mem_uIcc.1 hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hy0.1.trans_le h1, h2.trans_lt hy.2⟩
    · exact ⟨hy.1.trans_le h1, h2.trans_lt hy0.2⟩
  exact hnz c hcI hfc

lemma pos_on_of {f : ℝ → ℝ} (hf : Continuous f) {p q y0 : ℝ} (hy0 : y0 ∈ Set.Ioo p q)
    (hpos : 0 < f y0) (hnz : ∀ y ∈ Set.Ioo p q, f y ≠ 0) : ∀ y ∈ Set.Ioo p q, 0 < f y := by
  have := neg_on_of (f := fun x => -f x) hf.neg hy0 (by simpa using hpos)
    (fun y hy => by simpa using hnz y hy)
  intro y hy; simpa using this y hy

lemma neg_on_Ico {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (ha : f a < 0)
    (hnz : ∀ y ∈ Set.Ico a b, f y ≠ 0) : ∀ y ∈ Set.Ico a b, f y < 0 := by
  intro y hy
  by_contra h
  push Not at h
  obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc hy.1 hf.continuousOn ⟨ha.le, h⟩
  exact hnz c ⟨hc.1, hc.2.trans_lt hy.2⟩ hfc

lemma Dv_mono_of (N : ℕ) {p q : ℝ} (hpq : p ≤ q) (h : ∀ y ∈ Set.Ioo p q, 0 ≤ Ev N y) :
    Dv N p ≤ Dv N q := by
  rcases hpq.lt_or_eq with hlt | heq
  · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (Dv N) (Ev N) hlt
      (continuous_Dv N).continuousOn (fun x _ => hasDerivAt_Dv N x)
    have := h c hc
    rw [hcd, le_div_iff₀ (by linarith)] at this
    linarith
  · rw [heq]

lemma Dv_anti_of (N : ℕ) {p q : ℝ} (hpq : p ≤ q) (h : ∀ y ∈ Set.Ioo p q, Ev N y ≤ 0) :
    Dv N q ≤ Dv N p := by
  rcases hpq.lt_or_eq with hlt | heq
  · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (Dv N) (Ev N) hlt
      (continuous_Dv N).continuousOn (fun x _ => hasDerivAt_Dv N x)
    have := h c hc
    rw [hcd, div_le_iff₀ (by linarith)] at this
    linarith
  · rw [heq]

lemma Dv_strict_of (N : ℕ) {p q : ℝ} (hpq : p < q) (h : ∀ y ∈ Set.Ioo p q, 0 < Ev N y) :
    Dv N p < Dv N q := by
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (Dv N) (Ev N) hpq
    (continuous_Dv N).continuousOn (fun x _ => hasDerivAt_Dv N x)
  have := h c hc
  rw [hcd, lt_div_iff₀ (by linarith)] at this
  linarith

section Sign4

variable {N : ℕ} (hN : 2 ≤ N)
include hN

lemma noz_between {a : ℕ} (ha : a + 1 < 2 * N - 2) {y : ℝ}
    (hy : y ∈ Set.Ioo (zk N a) (zk N (a + 1))) : Ev N y ≠ 0 := by
  intro hE
  have hy01 : y ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨((zk_mem hN (j := a) (by omega)).1.1.trans hy.1).le, hy.2.trans (zk_mem hN ha).1.2⟩
  obtain ⟨j, hj, rfl⟩ := Ev_zero_knot hN hy01 hE
  rcases Nat.lt_or_ge a j with h | h
  · have := zk_mono hN (show a + 1 ≤ j by omega) hj
    linarith [hy.2]
  · have := zk_mono hN h (by omega)
    linarith [hy.1]

lemma noz_last {y : ℝ} (hy : y ∈ Set.Ioo (rr N (N - 1)) 1) : Ev N y ≠ 0 := by
  intro hE
  obtain ⟨j, hj, rfl⟩ := Ev_zero_knot hN ⟨((zk_mem hN (j := 0) (by omega)).1.1.trans_le
    ((zk_mem hN (j := 0) (by omega)).2.2) |>.trans hy.1).le, hy.2⟩ hE
  linarith [(zk_mem hN hj).2.2, hy.1]

lemma noz_first {y : ℝ} (hy : y ∈ Set.Ico 0 (gr N 1)) : Ev N y ≠ 0 := by
  intro hE
  have hy01 : y ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨hy.1, hy.2.trans ((zk_zero hN) ▸ (zk_mem hN (j := 0) (by omega)).1.2)⟩
  obtain ⟨j, hj, rfl⟩ := Ev_zero_knot hN hy01 hE
  linarith [(zk_mem hN hj).2.1, hy.2]

lemma noz_left {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ N - 1) {y : ℝ}
    (hy : y ∈ Set.Ioo (gr N k) (rr N k)) : Ev N y ≠ 0 := by
  apply noz_between hN (a := 2 * k - 2) (by omega)
  rw [zk_grid hN hk1, show 2 * k - 2 + 1 = 2 * k - 1 by omega, zk_rr hN hk1]; exact hy

lemma noz_right {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ N - 1) {y : ℝ}
    (hy : y ∈ Set.Ioo (rr N k) (gr N (k + 1))) : Ev N y ≠ 0 := by
  rcases Nat.lt_or_ge (k + 1) N with h | h
  · apply noz_between hN (a := 2 * k - 1) (by omega)
    rw [zk_rr hN hk1, show 2 * k - 1 + 1 = 2 * (k + 1) - 2 by omega, zk_grid hN (by omega)]
    exact hy
  · have hk' : k = N - 1 := by omega
    subst hk'
    rw [show N - 1 + 1 = N by omega, gr_N hN] at hy
    exact noz_last hN hy

lemma Dv_gr_succ {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ N - 1) : Dv N (gr N (k + 1)) = 0 := by
  rcases Nat.lt_or_ge (k + 1) N with h | h
  · exact Dv_grid hN (by omega) (by omega)
  · rw [show k + 1 = N by omega, gr_N hN, Dv_one hN]

lemma Ev_P0 : ∀ y ∈ Set.Ico 0 (gr N 1), Ev N y < 0 := by
  apply neg_on_Ico (continuous_Ev N)
  · rw [Ev_zero hN]
    have : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    linarith
  · exact fun y hy => noz_first hN hy

lemma Ev_step {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ N - 1) {a : ℝ} (ha : a < gr N k)
    (hleft : ∀ y ∈ Set.Ioo a (gr N k), Ev N y < 0) :
    (∀ y ∈ Set.Ioo (gr N k) (rr N k), 0 < Ev N y) ∧
      (∀ y ∈ Set.Ioo (rr N k) (gr N (k + 1)), Ev N y < 0) := by
  have hspec := rr_spec hN hk1 hk
  have hpos : ∀ y ∈ Set.Ioo (gr N k) (rr N k), 0 < Ev N y := by
    by_contra h
    push Not at h
    obtain ⟨y0, hy0, hy0'⟩ := h
    have hy0n : Ev N y0 < 0 := lt_of_le_of_ne hy0' (noz_left hN hk1 hk hy0)
    have hneg := neg_on_of (continuous_Ev N) hy0 hy0n (fun y hy => noz_left hN hk1 hk hy)
    have hmax : IsLocalMax (Ev N) (gr N k) := by
      have hgk0 : Ev N (gr N k) = 0 := by unfold gr; exact Ev_grid hN hk1 hk
      filter_upwards [Ioo_mem_nhds ha hspec.1.1] with y hy
      rw [hgk0]
      rcases lt_trichotomy y (gr N k) with h | h | h
      · exact (hleft y ⟨hy.1, h⟩).le
      · rw [h, hgk0]
      · exact (hneg y ⟨h, hy.2⟩).le
    exact M2_grid_ne hN hk1 hk (hmax.hasDerivAt_eq_zero (hasDerivAt_Ev N _))
  refine ⟨hpos, ?_⟩
  by_contra h
  push Not at h
  obtain ⟨y0, hy0, hy0'⟩ := h
  have hy0p : 0 < Ev N y0 := lt_of_le_of_ne hy0' (noz_right hN hk1 hk hy0).symm
  have hpos2 := pos_on_of (continuous_Ev N) hy0 hy0p (fun y hy => noz_right hN hk1 hk hy)
  have h1 := Dv_strict_of N hspec.1.1 hpos
  have h2 := Dv_strict_of N hspec.1.2 hpos2
  have hg0 : Dv N (gr N k) = 0 := by unfold gr; exact Dv_grid hN hk1 hk
  rw [hg0] at h1
  rw [Dv_gr_succ hN hk1 hk] at h2
  linarith

lemma Ev_Q {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ N - 1) :
    (∀ y ∈ Set.Ioo (gr N k) (rr N k), 0 < Ev N y) ∧
      (∀ y ∈ Set.Ioo (rr N k) (gr N (k + 1)), Ev N y < 0) := by
  induction k, hk1 using Nat.le_induction with
  | base =>
    exact Ev_step hN le_rfl hk (gr_pos hN le_rfl)
      (fun y hy => Ev_P0 hN y ⟨hy.1.le, hy.2⟩)
  | succ k hk1 ih =>
    have ih := ih (by omega)
    exact Ev_step hN (by omega) hk (rr_spec hN hk1 (by omega)).1.2 ih.2

/-- **Main sign lemma**: `M(x) ≥ x - 1/2` on `[0,1]`. -/
theorem Dv_nonneg {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ Dv N x := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rcases lt_or_ge x (gr N 1) with h1 | h1
  · have := Dv_anti_of N h1.le (fun y hy => (Ev_P0 hN y ⟨hx.1.trans hy.1.le, hy.2⟩).le)
    have h0 : Dv N (gr N 1) = 0 := by unfold gr; exact Dv_grid hN le_rfl (by omega)
    linarith
  rcases eq_or_lt_of_le hx.2 with h2 | h2
  · rw [h2, Dv_one hN]
  set k := ⌊x * N⌋₊ with hk
  have hk1 : 1 ≤ k := by
    rw [hk]; apply Nat.le_floor
    have : (1 : ℝ) / N ≤ x := by unfold gr at h1; simpa using h1
    rw [div_le_iff₀ hNR] at this; simpa using this
  have hkN : k ≤ N - 1 := by
    have : k < N := by
      rw [hk]; apply Nat.floor_lt (mul_nonneg hx.1 hNR.le) |>.2
      nlinarith
    omega
  have hgk : gr N k ≤ x := by
    unfold gr; rw [div_le_iff₀ hNR]; exact Nat.floor_le (mul_nonneg hx.1 hNR.le)
  have hgk1 : x < gr N (k + 1) := by
    unfold gr; rw [lt_div_iff₀ hNR]; push_cast; exact Nat.lt_floor_add_one _
  have hQ := Ev_Q hN hk1 hkN
  rcases le_or_gt x (rr N k) with h3 | h3
  · have := Dv_mono_of N hgk (fun y hy => (hQ.1 y ⟨hy.1, hy.2.trans_le h3⟩).le)
    have h0 : Dv N (gr N k) = 0 := by unfold gr; exact Dv_grid hN hk1 hkN
    linarith
  · have := Dv_anti_of N hgk1.le (fun y hy => (hQ.2 y ⟨h3.trans hy.1, hy.2⟩).le)
    rw [Dv_gr_succ hN hk1 hkN] at this
    exact this

end Sign4


/-! ### Assembling Vaaler's lemma -/

noncomputable def psiStar (N : ℕ) (x : ℝ) : ℝ := ∑ h ∈ Ico 1 N, al N h * Real.sin (2 * Real.pi * h * x)
noncomputable def Kh (N : ℕ) (x : ℝ) : ℝ := 1 / (2 * N) + ∑ h ∈ Ico 1 N, be N h * Real.cos (2 * Real.pi * h * x)

lemma Mf_eq {N : ℕ} (hN : 0 < N) (x : ℝ) : Mf N x = psiStar N x + Kh N x := by
  unfold Mf trig psiStar Kh
  rw [Ico_N hN, sum_add_distrib]; ring

lemma psiStar_add_int (N : ℕ) (x : ℝ) (m : ℤ) : psiStar N (x + m) = psiStar N x := by
  unfold psiStar
  refine sum_congr rfl fun h _ => ?_
  rw [show 2 * Real.pi * h * (x + m) = 2 * Real.pi * h * x + ((h * m : ℤ) : ℝ) * (2 * Real.pi) by
    push_cast; ring, Real.sin_add_int_mul_two_pi]

lemma Kh_add_int (N : ℕ) (x : ℝ) (m : ℤ) : Kh N (x + m) = Kh N x := by
  unfold Kh; congr 1
  refine sum_congr rfl fun h _ => ?_
  rw [show 2 * Real.pi * h * (x + m) = 2 * Real.pi * h * x + ((h * m : ℤ) : ℝ) * (2 * Real.pi) by
    push_cast; ring, Real.cos_add_int_mul_two_pi]

lemma psiStar_neg (N : ℕ) (x : ℝ) : psiStar N (-x) = -psiStar N x := by
  unfold psiStar; rw [← sum_neg_distrib]
  refine sum_congr rfl fun h _ => ?_
  rw [show 2 * Real.pi * h * -x = -(2 * Real.pi * h * x) by ring, Real.sin_neg]; ring

lemma Kh_neg (N : ℕ) (x : ℝ) : Kh N (-x) = Kh N x := by
  unfold Kh; congr 1
  refine sum_congr rfl fun h _ => ?_
  rw [show 2 * Real.pi * h * -x = -(2 * Real.pi * h * x) by ring, Real.cos_neg]

/-- The real form of Vaaler's inequality: `|ψ(x) - ψ*(x)| ≤ K(x)/(2N)`. -/
theorem vaaler_real {N : ℕ} (hN : 2 ≤ N) (x : ℝ) :
    |(x - ⌊x⌋ - 1 / 2) - psiStar N x| ≤ Kh N x := by
  set y := Int.fract x with hy
  have hxy : x = y + ⌊x⌋ := by rw [hy, Int.fract]; ring
  have hy0 : 0 ≤ y := Int.fract_nonneg x
  have hy1 : y < 1 := Int.fract_lt_one x
  have e1 : x - ⌊x⌋ - 1 / 2 = y - 1 / 2 := by rw [hy, Int.fract]
  have e2 : psiStar N x = psiStar N y := by rw [hxy, psiStar_add_int]
  have e3 : Kh N x = Kh N y := by rw [hxy, Kh_add_int]
  rw [e1, e2, e3]
  have hup : y - 1 / 2 ≤ psiStar N y + Kh N y := by
    have := Dv_nonneg hN ⟨hy0, hy1.le⟩
    unfold Dv at this; rw [Mf_eq (by omega)] at this; linarith
  rcases eq_or_lt_of_le hy0 with h0 | h0
  · rw [← h0]
    have hm := Mf_zero (N := N) (by omega)
    rw [Mf_eq (by omega)] at hm
    have hp0 : psiStar N 0 = 0 := by unfold psiStar; simp
    rw [hp0] at hm ⊢
    rw [abs_le]; constructor <;> linarith
  · have hlow : psiStar N y - Kh N y ≤ y - 1 / 2 := by
      have := Dv_nonneg hN (x := 1 - y) ⟨by linarith, by linarith⟩
      unfold Dv at this
      rw [Mf_eq (by omega), show 1 - y = -y + ((1 : ℤ) : ℝ) by push_cast; ring,
        psiStar_add_int, Kh_add_int, psiStar_neg, Kh_neg] at this
      linarith
    rw [abs_le]; constructor <;> linarith

/-- `π u cot(π u) ≤ 1` for `0 < u < 1`. -/
lemma pi_mul_cot_le {u : ℝ} (h0 : 0 < u) (h1 : u < 1) : Real.pi * u * Real.cot (Real.pi * u) ≤ 1 := by
  have hpu : 0 < Real.pi * u := by positivity
  rcases lt_or_ge u (1 / 2) with h | h
  · have hlt : Real.pi * u < Real.pi / 2 := by nlinarith [Real.pi_pos]
    have htan := Real.lt_tan hpu hlt
    rw [← Real.tan_inv_eq_cot]
    have htp : 0 < Real.tan (Real.pi * u) := hpu.trans htan
    rw [mul_inv_le_iff₀ htp]; linarith
  · have hc : Real.cot (Real.pi * u) ≤ 0 := by
      rw [Real.cot_eq_cos_div_sin]
      apply div_nonpos_of_nonpos_of_nonneg
      · apply Real.cos_nonpos_of_pi_div_two_le_of_le <;> nlinarith [Real.pi_pos]
      · exact Real.sin_nonneg_of_nonneg_of_le_pi hpu.le (by nlinarith [Real.pi_pos])
    nlinarith

lemma abs_al_le {N h : ℕ} (hh1 : 1 ≤ h) (hhN : h < N) :
    |al N h| ≤ 1 / (Real.pi * h) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  have hhNR : (h : ℝ) < N := by exact_mod_cast hhN
  set t : ℝ := h / N with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t < 1 := by rw [ht, div_lt_one hNR]; exact hhNR
  have hpi := Real.pi_pos
  have key : al N h = -(Real.pi * t * (1 - t) * Real.cot (Real.pi * t) + t) / (Real.pi * h) := by
    rw [al, ht]
    have : Real.pi * h / N = Real.pi * (h / N) := by ring
    rw [this]; field_simp
  have hup := pi_mul_cot_le ht0 ht1
  have hlow := pi_mul_cot_le (u := 1 - t) (by linarith) (by linarith)
  have hcot : Real.cot (Real.pi * (1 - t)) = -Real.cot (Real.pi * t) := by
    rw [show Real.pi * (1 - t) = Real.pi - Real.pi * t by ring, Real.cot_eq_cos_div_sin,
      Real.cot_eq_cos_div_sin, Real.cos_pi_sub, Real.sin_pi_sub, neg_div]
  rw [hcot] at hlow
  have hφ1 : Real.pi * t * (1 - t) * Real.cot (Real.pi * t) + t ≤ 1 := by nlinarith
  have hφ0 : 0 ≤ Real.pi * t * (1 - t) * Real.cot (Real.pi * t) + t := by nlinarith
  rw [key, abs_div, abs_neg, abs_of_nonneg hφ0, abs_of_pos (by positivity)]
  exact div_le_div_of_nonneg_right hφ1 (by positivity)

/-- Coefficients of Vaaler's polynomial. -/
noncomputable def acoef (N : ℕ) (ℓ : ℤ) : ℂ := -(I / 2) * (al N ℓ.natAbs : ℂ) * (ℓ.sign : ℂ)

lemma sum_filter_split (H : ℕ) (f : ℤ → ℂ) :
    ∑ ℓ ∈ (Icc (-(H : ℤ)) H).filter (fun ℓ => 1 ≤ |ℓ|), f ℓ =
      ∑ h ∈ Ico 1 (H + 1), (f h + f (-(h : ℤ))) := by
  rw [sum_add_distrib]
  have hdisj : Disjoint ((Ico 1 (H + 1)).image (fun h : ℕ => (h : ℤ)))
      ((Ico 1 (H + 1)).image (fun h : ℕ => -(h : ℤ))) := by
    rw [disjoint_left]
    intro a ha hb
    simp only [mem_image, mem_Ico] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, hxy⟩ := hb
    omega
  have hset : (Icc (-(H : ℤ)) H).filter (fun ℓ => 1 ≤ |ℓ|) =
      (Ico 1 (H + 1)).image (fun h : ℕ => (h : ℤ)) ∪ (Ico 1 (H + 1)).image (fun h : ℕ => -(h : ℤ)) := by
    ext ℓ
    simp only [mem_filter, mem_Icc, mem_union, mem_image, mem_Ico, le_abs']
    constructor
    · rintro ⟨⟨h1, h2⟩, h3 | h3⟩
      · right; exact ⟨(-ℓ).toNat, by omega, by omega⟩
      · left; exact ⟨ℓ.toNat, by omega, by omega⟩
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · exact ⟨⟨by omega, by omega⟩, Or.inr (by omega)⟩
      · exact ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩
  rw [hset, sum_union hdisj, sum_image (by intro a _ b _ h; simpa using h),
    sum_image (by intro a _ b _ h; simpa using h)]

lemma exp_int_eq (ℓ : ℤ) (x : ℝ) : Complex.exp (2 * Real.pi * I * ℓ * x) =
    (Real.cos (2 * Real.pi * ℓ * x) : ℂ) + (Real.sin (2 * Real.pi * ℓ * x) : ℂ) * I := by
  rw [show (2 * Real.pi * I * ℓ * x : ℂ) = ((2 * Real.pi * ℓ * x : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma vaaler_sum_eq {N : ℕ} (hN : 1 ≤ N) (x : ℝ) :
    ∑ ℓ ∈ (Icc (-((N - 1 : ℕ) : ℤ)) (N - 1 : ℕ)).filter (fun ℓ => 1 ≤ |ℓ|),
      acoef N ℓ * Complex.exp (2 * Real.pi * I * ℓ * x) = (psiStar N x : ℂ) := by
  rw [sum_filter_split, Nat.sub_add_cancel hN]
  unfold psiStar
  rw [Complex.ofReal_sum]
  refine sum_congr rfl fun h hh => ?_
  simp only [mem_Ico] at hh
  have hs1 : ((h : ℤ)).sign = 1 := Int.sign_eq_one_of_pos (by omega)
  have hs2 : (-(h : ℤ)).sign = -1 := by rw [Int.sign_neg, hs1]
  have hn1 : ((h : ℤ)).natAbs = h := Int.natAbs_natCast h
  have hn2 : (-(h : ℤ)).natAbs = h := by rw [Int.natAbs_neg, hn1]
  unfold acoef
  rw [hs1, hs2, hn1, hn2, exp_int_eq, exp_int_eq]
  simp only [Int.cast_natCast, Int.cast_neg, Int.cast_one]
  rw [show 2 * Real.pi * -(h : ℝ) * x = -(2 * Real.pi * h * x) by ring, Real.cos_neg, Real.sin_neg,
    Complex.ofReal_neg, Complex.ofReal_mul]
  linear_combination (-(al N h : ℂ) * (Real.sin (2 * Real.pi * h * x) : ℂ)) * I_sq

lemma fejer_eq {N : ℕ} (hN : 1 ≤ N) (x : ℝ) :
    1 / (2 * ((N - 1 : ℕ) : ℝ) + 2) * (∑ ℓ ∈ Icc (-((N - 1 : ℕ) : ℤ)) (N - 1 : ℕ),
      ((1 - |(ℓ : ℝ)| / ((N - 1 : ℕ) + 1) : ℝ) : ℂ) * Complex.exp (2 * Real.pi * I * ℓ * x)).re =
    Kh N x := by
  have hNR : ((N - 1 : ℕ) : ℝ) + 1 = N := by rw [Nat.cast_sub hN]; push_cast; ring
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [← sum_filter_add_sum_filter_not _ (fun ℓ : ℤ => 1 ≤ |ℓ|), sum_filter_split,
    Nat.sub_add_cancel hN]
  have hnot : (Icc (-((N - 1 : ℕ) : ℤ)) (N - 1 : ℕ)).filter (fun ℓ : ℤ => ¬ 1 ≤ |ℓ|) = {0} := by
    ext ℓ
    simp only [mem_filter, mem_Icc, mem_singleton, le_abs', not_or, not_le]
    constructor
    · rintro ⟨_, h1, h2⟩; omega
    · rintro rfl; exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  rw [hnot, sum_singleton]
  simp only [Complex.add_re, Complex.re_sum, exp_int_eq, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
    zero_mul, sub_zero, add_zero, mul_one]
  unfold Kh
  rw [hNR]
  simp only [Int.cast_zero, abs_zero, zero_div, sub_zero, mul_zero, zero_mul, Real.cos_zero,
    Int.cast_natCast, Int.cast_neg, abs_neg, Nat.abs_cast, neg_mul, mul_neg, Real.cos_neg, mul_one]
  rw [show 2 * ((N - 1 : ℕ) : ℝ) + 2 = 2 * N by rw [← hNR]; ring, mul_add, mul_sum, mul_one, add_comm]
  congr 1
  refine sum_congr rfl fun h _ => ?_
  unfold be; field_simp; ring

/-- **Vaaler's lemma** (Vaaler 1985, Thm 18; Graham–Kolesnik Thm A.6). -/
theorem vaaler_lemma : ∀ H : ℕ, 1 ≤ H → ∃ a : ℤ → ℂ,
    (∀ ℓ : ℤ, 1 ≤ |ℓ| → |ℓ| ≤ H → ‖a ℓ‖ ≤ 1 / (2 * Real.pi * |(ℓ : ℝ)|)) ∧
    ∀ x : ℝ, ‖((x - ⌊x⌋ - 1 / 2 : ℝ) : ℂ) - ∑ ℓ ∈ (Icc (-(H : ℤ)) H).filter (fun ℓ => 1 ≤ |ℓ|),
        a ℓ * Complex.exp (2 * Real.pi * I * ℓ * x)‖ ≤
      1 / (2 * H + 2) * (∑ ℓ ∈ Icc (-(H : ℤ)) H,
        ((1 - |(ℓ : ℝ)| / (H + 1) : ℝ) : ℂ) * Complex.exp (2 * Real.pi * I * ℓ * x)).re := by
  intro H hH
  refine ⟨acoef (H + 1), ?_, ?_⟩
  · intro ℓ h1 h2
    rw [Int.abs_eq_natAbs] at h1 h2
    have hn1 : 1 ≤ ℓ.natAbs := by omega
    have hn2 : ℓ.natAbs < H + 1 := by omega
    have habs : |(ℓ : ℝ)| = (ℓ.natAbs : ℝ) := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp
    have hsign : ‖(ℓ.sign : ℂ)‖ = 1 := by
      rcases Int.sign_trichotomy ℓ with h | h | h <;>
        first
        | (rw [Int.sign_eq_zero_iff_zero] at h; subst h; simp at hn1)
        | (rw [h]; simp)
    unfold acoef
    rw [norm_mul, norm_mul, hsign, mul_one, norm_neg, norm_div, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, habs]
    have := abs_al_le (N := H + 1) hn1 hn2
    have hpi := Real.pi_pos
    have hpos : (0 : ℝ) < ℓ.natAbs := by exact_mod_cast hn1
    calc 1 / ‖(2 : ℂ)‖ * |al (H + 1) ℓ.natAbs| ≤ 1 / 2 * (1 / (Real.pi * ℓ.natAbs)) := by
          rw [show ‖(2 : ℂ)‖ = 2 by simp]; gcongr
      _ = _ := by field_simp
  · intro x
    have hs := vaaler_sum_eq (N := H + 1) (by omega) x
    have hf := fejer_eq (N := H + 1) (by omega) x
    simp only [Nat.add_sub_cancel] at hs hf
    rw [hs, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    push_cast at hf ⊢
    rw [hf]
    exact vaaler_real (by omega) x

end Vaaler
#print axioms Vaaler.vaaler_lemma
#print axioms Vaaler.vaaler_real
