import ThetaSum.Bridge
import ThetaSum.SquareWave
import ThetaSum.Weights
import ThetaSum.Kloost

/-
**Lemma 6.6** (the heads over a block), in the form used here.

For a block of odd moduli `k ∈ [a, b)` with `a ≥ 2N`, the heads
  `∑_k ∑_{n ≤ N odd} cot(π n/(2k))/k² · g(n w_k / p)`,  `w_k = (2k)^{-1} mod p`,
are bounded through the square wave (Vaaler), Abel summation over `k` with the decreasing
weights `cot(π n/(2k))/k²`, and a bound `M_b` for the incomplete Kloosterman sums
`∑_{k ∈ [a,x), k odd} e(c (2k)^{-1}/p)`.
-/

open Finset

namespace ThetaSum

lemma psiP_natCast (p : ℕ) (hp : 0 < p) (m : ℕ) :
    psiP p (m : ZMod p) = Complex.exp (((2 * Real.pi * (m / p) : ℝ) : ℂ) * Complex.I) := by
  haveI : NeZero p := ⟨by omega⟩
  unfold psiP
  rw [ZMod.val_natCast]
  have hdec : (m : ℝ) = p * (m / p : ℕ) + (m % p : ℕ) := by exact_mod_cast (Nat.div_add_mod m p).symm
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have e : (((2 * Real.pi * (m / p) : ℝ) : ℂ) * Complex.I) =
      2 * Real.pi * Complex.I * (((m % p : ℕ) : ℝ) / p) + ((m / p : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [hdec]; push_cast; field_simp; ring
  rw [e, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

lemma psiP_im (p : ℕ) (hp : 0 < p) (m : ℕ) :
    (psiP p (m : ZMod p)).im = Real.sin (2 * Real.pi * (m / p)) := by
  rw [psiP_natCast p hp, Complex.exp_ofReal_mul_I_im]

lemma psiP_re (p : ℕ) (hp : 0 < p) (m : ℕ) :
    (psiP p (m : ZMod p)).re = Real.cos (2 * Real.pi * (m / p)) := by
  rw [psiP_natCast p hp, Complex.exp_ofReal_mul_I_re]

/-- The Kloosterman phase `h n (2k)^{-1}` written with `w_k = wInv p k`. -/
lemma phase_eq (p : ℕ) (hp : p.Prime) (h n k : ℕ) :
    ((h * n : ℕ) : ZMod p) * ((2 * k : ℕ) : ZMod p)⁻¹ = ((h * n * wInv p k : ℕ) : ZMod p) := by
  haveI := Fact.mk hp
  unfold wInv
  push_cast
  rw [ZMod.natCast_zmod_val]

/-- The weights `cot(π n/(2k))/k²` are nonnegative and at most `2/(π n k)`. -/
lemma weight_bounds (n k : ℕ) (hn : 1 ≤ n) (hk : 2 * n ≤ k) :
    0 ≤ Real.cot (Real.pi * n / (2 * k)) / (k : ℝ) ^ 2 ∧
      Real.cot (Real.pi * n / (2 * k)) / (k : ℝ) ^ 2 ≤ 2 / (Real.pi * n * k) := by
  have hpi := Real.pi_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hx0 : 0 < Real.pi * n / (2 * k) := by positivity
  have hx2 : Real.pi * n / (2 * k) < Real.pi / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    have : (2 * n : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hcos : 0 < Real.cos (Real.pi * n / (2 * k)) := Real.cos_pos_of_mem_Ioo ⟨by linarith, hx2⟩
  have hsin : 0 < Real.sin (Real.pi * n / (2 * k)) :=
    Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith)
  have hc0 : 0 ≤ Real.cot (Real.pi * n / (2 * k)) := by
    rw [Real.cot_eq_cos_div_sin]; positivity
  have hc1 : Real.cot (Real.pi * n / (2 * k)) ≤ 1 / (Real.pi * n / (2 * k)) := by
    have ht : Real.pi * n / (2 * k) < Real.tan (Real.pi * n / (2 * k)) := Real.lt_tan hx0 hx2
    rw [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos] at *
    rw [lt_div_iff₀ hcos] at ht
    rw [div_le_div_iff₀ hsin hx0]; linarith
  refine ⟨by positivity, ?_⟩
  calc Real.cot (Real.pi * n / (2 * k)) / (k : ℝ) ^ 2 ≤ (1 / (Real.pi * n / (2 * k))) / (k : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hc1 (by positivity)
    _ = 2 / (Real.pi * n * k) := by field_simp

/-- The phase `y = n w / p` is not in `½ℤ` (for `p` odd, `p ∤ n`, `p ∤ w`). -/
lemma phase_nonint (p n w : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hn1 : 1 ≤ n) (hnp : n < p)
    (hw : ¬ p ∣ w) :
    (∀ m : ℤ, (n : ℝ) * w / p ≠ m) ∧ (∀ m : ℤ, (n : ℝ) * w / p + 1 / 2 ≠ m) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpn : ¬ p ∣ n * w := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
    · have := Nat.le_of_dvd (by omega) h1; omega
    · exact hw h1
  constructor
  · intro m hm
    have : ((n * w : ℕ) : ℤ) = p * m := by
      have : ((n * w : ℕ) : ℝ) = p * m := by rw [← hm]; push_cast; field_simp
      exact_mod_cast this
    exact hpn (by exact_mod_cast (Dvd.intro m this.symm : (p : ℤ) ∣ (n * w : ℕ)))
  · intro m hm
    have h2 : ((2 * (n * w) + p : ℕ) : ℤ) = 2 * p * m := by
      have : ((2 * (n * w) + p : ℕ) : ℝ) = 2 * p * m := by
        have e : (m : ℝ) = n * w / p + 1 / 2 := hm.symm
        rw [e]; push_cast; field_simp
      exact_mod_cast this
    have hodd : Odd p := hp.odd_of_ne_two hp2
    obtain ⟨t, ht⟩ := hodd
    have : (2 : ℤ) ∣ ((2 * (n * w) + p : ℕ) : ℤ) := ⟨p * m, by rw [h2]; ring⟩
    push_cast at this
    omega

/-- The weight `cot(π n/(2k))/k²`. -/
noncomputable def wt (n k : ℕ) : ℝ := Real.cot (Real.pi * n / (2 * k)) / (k : ℝ) ^ 2

/-- The heads of `Φ_k`, written with `w_k = (2k)^{-1} mod p`. -/
noncomputable def headTerm (p N k : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 N).filter Odd, wt n k * gsq (n * (wInv p k : ℝ) / p)

/-- Abel + Kloosterman bound for one `n` and one frequency `c`. -/
lemma kl_weighted (p : ℕ) (c : ZMod p) (hc : c ≠ 0) (n a b : ℕ) (hn : 1 ≤ n) (hna : 2 * n ≤ a)
    (hab : a ≤ b) (Mb : ℝ)
    (hMb : ∀ c : ZMod p, c ≠ 0 → ∀ x, a ≤ x → x ≤ b →
      ‖∑ k ∈ (Ico a x).filter Odd, psiP p (c * ((2 * k : ℕ) : ZMod p)⁻¹)‖ ≤ Mb) :
    ‖∑ k ∈ (Ico a b).filter Odd, (wt n k : ℂ) * psiP p (c * ((2 * k : ℕ) : ZMod p)⁻¹)‖ ≤
      wt n a * Mb := by
  classical
  set z : ℕ → ℂ := fun k => if Odd k then psiP p (c * ((2 * k : ℕ) : ZMod p)⁻¹) else 0
  have e : ∑ k ∈ (Ico a b).filter Odd, (wt n k : ℂ) * psiP p (c * ((2 * k : ℕ) : ZMod p)⁻¹) =
      ∑ k ∈ Ico a b, (wt n k : ℂ) * z k := by
    rw [sum_filter]; apply sum_congr rfl; intro k _; simp only [z]; split_ifs <;> simp
  rw [e]
  apply abel_antitone (wt n) z a b hab Mb
  · intro k hk _; exact weight_antitone n k (k + 1) hn (by omega) (by omega)
  · exact (weight_bounds n b hn (by omega)).1
  · intro x hx1 hx2
    have e2 : ∑ i ∈ Ico a x, z i = ∑ k ∈ (Ico a x).filter Odd, psiP p (c * ((2 * k : ℕ) : ZMod p)⁻¹) := by
      rw [sum_filter]
    rw [e2]; exact hMb c hc x hx1 hx2

lemma sum3_comm (X Y Z : Finset ℕ) (f : ℕ → ℕ → ℕ → ℝ) :
    ∑ x ∈ X, ∑ y ∈ Y, ∑ z ∈ Z, f x y z = ∑ z ∈ Z, ∑ x ∈ X, ∑ y ∈ Y, f x y z := by
  have h1 : ∑ x ∈ X, ∑ y ∈ Y, ∑ z ∈ Z, f x y z = ∑ x ∈ X, ∑ z ∈ Z, ∑ y ∈ Y, f x y z :=
    sum_congr rfl (fun x _ => sum_comm)
  rw [h1, sum_comm]

/-- **Heads over a block** (Lemma 6.6). -/
theorem block_heads (hV : HV) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (N H a b : ℕ) (hH : 1 ≤ H)
    (hN : 1 ≤ N) (hNa : 2 * N ≤ a) (hab : a ≤ b) (hbp : b ≤ p) (hHp : H < p) (hNp : N < p)
    (Mb : ℝ) (hMb0 : 0 ≤ Mb)
    (hMb : ∀ c : ZMod p, c ≠ 0 → ∀ x, a ≤ x → x ≤ b →
      ‖∑ k ∈ (Ico a x).filter Odd, psiP p (c * ((2 * k : ℕ) : ZMod p)⁻¹)‖ ≤ Mb) :
    |∑ k ∈ (Ico a b).filter Odd, headTerm p N k| ≤
      2 / (H + 1) * ∑ k ∈ (Ico a b).filter Odd, ∑ n ∈ (Icc 1 N).filter Odd, wt n k +
        (∑ h ∈ Icc 1 H, 4 / (Real.pi * h) + 4) * (∑ n ∈ (Icc 1 N).filter Odd, wt n a) * Mb := by
  classical
  haveI := Fact.mk hp
  obtain ⟨bb, dd, hbb, hdd, hsw⟩ := square_wave hV H hH
  have hp0 : 0 < p := hp.pos
  set A := (Ico a b).filter Odd
  set Nn := (Icc 1 N).filter Odd
  set y : ℕ → ℕ → ℝ := fun k n => n * (wInv p k : ℝ) / p
  -- basic facts on the indices
  have hkA : ∀ k ∈ A, a ≤ k ∧ k < b ∧ Odd k := by
    intro k hk; simp only [A, mem_filter, mem_Ico] at hk; exact ⟨hk.1.1, hk.1.2, hk.2⟩
  have hnN : ∀ n ∈ Nn, 1 ≤ n ∧ n ≤ N := by
    intro n hn; simp only [Nn, mem_filter, mem_Icc] at hn; exact hn.1
  have hwt0 : ∀ k ∈ A, ∀ n ∈ Nn, 0 ≤ wt n k := by
    intro k hk n hn
    exact (weight_bounds n k (hnN n hn).1 (by have := hkA k hk; have := hnN n hn; omega)).1
  have hw : ∀ k ∈ A, ¬ p ∣ wInv p k := by
    intro k hk hdvd
    have hk' := hkA k hk
    have h2k : ¬ p ∣ 2 * k := by
      intro h
      rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
      · have := Nat.le_of_dvd (by norm_num) h1
        have := hp.two_le; omega
      · have := Nat.le_of_dvd (by omega) h1; omega
    have hs := wInv_spec p k hp h2k
    obtain ⟨c, hc⟩ := hdvd
    have : (p : ℤ) ∣ 1 := by
      have e : (1 : ℤ) = 2 * k * wInv p k - (2 * k * wInv p k - 1) := by ring
      rw [e]; refine dvd_sub ?_ hs
      rw [hc]; push_cast; exact ⟨2 * k * c, by ring⟩
    have := Int.eq_one_of_dvd_one (by positivity) this
    have : p = 1 := by exact_mod_cast this
    exact hp.one_lt.ne' this
  -- square-wave approximation at every point
  have happ : ∀ k ∈ A, ∀ n ∈ Nn,
      |gsq (y k n) - ∑ h ∈ Icc 1 H, bb h * Real.sin (2 * Real.pi * h * y k n)| ≤
        2 / (H + 1) * (1 + ∑ h ∈ Icc 1 H, dd h * Real.cos (2 * Real.pi * h * y k n)) := by
    intro k hk n hn
    have hni := phase_nonint p n (wInv p k) hp hp2 (hnN n hn).1 (by have := hnN n hn; omega) (hw k hk)
    exact hsw (y k n) hni.1 hni.2
  -- the Kloosterman form of the sine and cosine sums
  have hphase : ∀ h n k : ℕ, 2 * Real.pi * h * y k n = 2 * Real.pi * (((h * n * wInv p k : ℕ) : ℝ) / p) := by
    intro h n k; simp only [y]; push_cast; ring
  have hcne : ∀ h ∈ Icc 1 H, ∀ n ∈ Nn, ((h * n : ℕ) : ZMod p) ≠ 0 := by
    intro h hh n hn
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    simp only [mem_Icc] at hh
    rcases (Nat.Prime.dvd_mul hp).mp hd with h1 | h1
    · have := Nat.le_of_dvd (by omega) h1; omega
    · have := Nat.le_of_dvd (by have := hnN n hn; omega) h1; have := hnN n hn; omega
  have hSh : ∀ h ∈ Icc 1 H, ∀ n ∈ Nn,
      |∑ k ∈ A, wt n k * Real.sin (2 * Real.pi * h * y k n)| ≤ wt n a * Mb ∧
      |∑ k ∈ A, wt n k * Real.cos (2 * Real.pi * h * y k n)| ≤ wt n a * Mb := by
    intro h hh n hn
    have hK := kl_weighted p ((h * n : ℕ) : ZMod p) (hcne h hh n hn) n a b (hnN n hn).1
      (by have := hnN n hn; omega) hab Mb hMb
    have hterm : ∀ k : ℕ, psiP p (((h * n : ℕ) : ZMod p) * ((2 * k : ℕ) : ZMod p)⁻¹) =
        psiP p ((h * n * wInv p k : ℕ) : ZMod p) := by
      intro k; rw [phase_eq p hp h n k]
    set Z := ∑ k ∈ A, (wt n k : ℂ) * psiP p (((h * n : ℕ) : ZMod p) * ((2 * k : ℕ) : ZMod p)⁻¹)
    have him : Z.im = ∑ k ∈ A, wt n k * Real.sin (2 * Real.pi * h * y k n) := by
      simp only [Z, Complex.im_sum, Complex.im_ofReal_mul, hterm, psiP_im p hp0, hphase]
    have hre : Z.re = ∑ k ∈ A, wt n k * Real.cos (2 * Real.pi * h * y k n) := by
      simp only [Z, Complex.re_sum, Complex.re_ofReal_mul, hterm, psiP_re p hp0, hphase]
    exact ⟨him ▸ (Complex.abs_im_le_norm Z).trans hK, hre ▸ (Complex.abs_re_le_norm Z).trans hK⟩
  set Wa := ∑ n ∈ Nn, wt n a
  have hWa0 : 0 ≤ Wa := by
    apply sum_nonneg; intro n hn
    exact (weight_bounds n a (hnN n hn).1 (by have := hnN n hn; omega)).1
  -- double sums over `(k, n)` for each frequency
  have hS2 : ∀ h ∈ Icc 1 H,
      |∑ k ∈ A, ∑ n ∈ Nn, wt n k * Real.sin (2 * Real.pi * h * y k n)| ≤ Wa * Mb ∧
      |∑ k ∈ A, ∑ n ∈ Nn, wt n k * Real.cos (2 * Real.pi * h * y k n)| ≤ Wa * Mb := by
    intro h hh
    rw [sum_comm, sum_comm (s := A) (t := Nn)]
    constructor
    · refine (abs_sum_le_sum_abs _ _).trans ?_
      rw [show Wa * Mb = ∑ n ∈ Nn, wt n a * Mb by rw [sum_mul]]
      exact sum_le_sum fun n hn => (hSh h hh n hn).1
    · refine (abs_sum_le_sum_abs _ _).trans ?_
      rw [show Wa * Mb = ∑ n ∈ Nn, wt n a * Mb by rw [sum_mul]]
      exact sum_le_sum fun n hn => (hSh h hh n hn).2
  -- split `g = (∑ b sin) + (g - ∑ b sin)`
  have hsplit : ∑ k ∈ A, headTerm p N k =
      ∑ h ∈ Icc 1 H, bb h * ∑ k ∈ A, ∑ n ∈ Nn, wt n k * Real.sin (2 * Real.pi * h * y k n) +
        ∑ k ∈ A, ∑ n ∈ Nn, wt n k *
          (gsq (y k n) - ∑ h ∈ Icc 1 H, bb h * Real.sin (2 * Real.pi * h * y k n)) := by
    have hT : ∑ h ∈ Icc 1 H, bb h * ∑ k ∈ A, ∑ n ∈ Nn, wt n k * Real.sin (2 * Real.pi * h * y k n) =
        ∑ k ∈ A, ∑ n ∈ Nn, ∑ h ∈ Icc 1 H, wt n k * (bb h * Real.sin (2 * Real.pi * h * y k n)) := by
      rw [sum3_comm A Nn (Icc 1 H) (fun k n h => wt n k * (bb h * Real.sin (2 * Real.pi * h * y k n)))]
      apply sum_congr rfl; intro h _
      rw [mul_sum]; apply sum_congr rfl; intro k _
      rw [mul_sum]; apply sum_congr rfl; intro n _
      ring
    rw [hT, ← sum_add_distrib]
    unfold headTerm
    apply sum_congr rfl; intro k _
    rw [← sum_add_distrib]
    apply sum_congr rfl; intro n _
    rw [← mul_sum]
    show wt n k * gsq (y k n) = _
    ring
  rw [hsplit]
  -- first part
  have hfirst : |∑ h ∈ Icc 1 H, bb h * ∑ k ∈ A, ∑ n ∈ Nn, wt n k * Real.sin (2 * Real.pi * h * y k n)| ≤
      (∑ h ∈ Icc 1 H, 4 / (Real.pi * h)) * (Wa * Mb) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [sum_mul]
    apply sum_le_sum; intro h hh
    rw [abs_mul]
    have hh' := hh; simp only [mem_Icc] at hh'
    exact mul_le_mul (hbb h hh'.1 hh'.2) (hS2 h hh).1 (abs_nonneg _) (by positivity)
  -- second part
  have hsecond : |∑ k ∈ A, ∑ n ∈ Nn, wt n k *
        (gsq (y k n) - ∑ h ∈ Icc 1 H, bb h * Real.sin (2 * Real.pi * h * y k n))| ≤
      2 / (H + 1) * ∑ k ∈ A, ∑ n ∈ Nn, wt n k + 4 * (Wa * Mb) := by
    have hH0 : (0 : ℝ) < H + 1 := by positivity
    calc _ ≤ ∑ k ∈ A, ∑ n ∈ Nn, wt n k * (2 / (H + 1) *
            (1 + ∑ h ∈ Icc 1 H, dd h * Real.cos (2 * Real.pi * h * y k n))) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
          rw [abs_mul, abs_of_nonneg (hwt0 k hk n hn)]
          exact mul_le_mul_of_nonneg_left (happ k hk n hn) (hwt0 k hk n hn)
      _ = 2 / (H + 1) * ∑ k ∈ A, ∑ n ∈ Nn, wt n k +
            2 / (H + 1) * ∑ h ∈ Icc 1 H, dd h *
              ∑ k ∈ A, ∑ n ∈ Nn, wt n k * Real.cos (2 * Real.pi * h * y k n) := by
          have hC : ∑ h ∈ Icc 1 H, dd h * ∑ k ∈ A, ∑ n ∈ Nn, wt n k * Real.cos (2 * Real.pi * h * y k n) =
              ∑ k ∈ A, ∑ n ∈ Nn, ∑ h ∈ Icc 1 H, wt n k * (dd h * Real.cos (2 * Real.pi * h * y k n)) := by
            rw [sum3_comm A Nn (Icc 1 H) (fun k n h => wt n k * (dd h * Real.cos (2 * Real.pi * h * y k n)))]
            apply sum_congr rfl; intro h _
            rw [mul_sum]; apply sum_congr rfl; intro k _
            rw [mul_sum]; apply sum_congr rfl; intro n _
            ring
          rw [hC, mul_sum, mul_sum, ← sum_add_distrib]
          apply sum_congr rfl; intro k _
          rw [mul_sum, mul_sum, ← sum_add_distrib]
          apply sum_congr rfl; intro n _
          rw [← mul_sum]
          ring
      _ ≤ 2 / (H + 1) * ∑ k ∈ A, ∑ n ∈ Nn, wt n k + 4 * (Wa * Mb) := by
          apply add_le_add le_rfl
          have hc : ∑ h ∈ Icc 1 H, dd h * ∑ k ∈ A, ∑ n ∈ Nn, wt n k * Real.cos (2 * Real.pi * h * y k n) ≤
              ∑ h ∈ Icc 1 H, 2 * (Wa * Mb) := by
            apply sum_le_sum; intro h hh
            have hh' := hh; simp only [mem_Icc] at hh'
            have hd := hdd h hh'.2
            have hc := (hS2 h hh).2
            calc dd h * ∑ k ∈ A, ∑ n ∈ Nn, wt n k * Real.cos (2 * Real.pi * h * y k n)
                ≤ dd h * |∑ k ∈ A, ∑ n ∈ Nn, wt n k * Real.cos (2 * Real.pi * h * y k n)| :=
                  mul_le_mul_of_nonneg_left (le_abs_self _) hd.1
              _ ≤ 2 * (Wa * Mb) := mul_le_mul hd.2 hc (abs_nonneg _) (by norm_num)
          rw [sum_const, Nat.card_Icc, nsmul_eq_mul] at hc
          have hHle : 2 / ((H : ℝ) + 1) * ((H + 1 - 1 : ℕ) * (2 * (Wa * Mb))) ≤ 4 * (Wa * Mb) := by
            have : ((H + 1 - 1 : ℕ) : ℝ) = H := by norm_num
            rw [this]
            have hWM : 0 ≤ Wa * Mb := mul_nonneg hWa0 hMb0
            rw [div_mul_eq_mul_div, div_le_iff₀ hH0]
            nlinarith
          calc 2 / ((H : ℝ) + 1) * ∑ h ∈ Icc 1 H, dd h * ∑ k ∈ A, ∑ n ∈ Nn, wt n k * Real.cos (2 * Real.pi * h * y k n)
              ≤ 2 / ((H : ℝ) + 1) * ((H + 1 - 1 : ℕ) * (2 * (Wa * Mb))) :=
                mul_le_mul_of_nonneg_left hc (by positivity)
            _ ≤ _ := hHle
  calc _ ≤ |∑ h ∈ Icc 1 H, bb h * ∑ k ∈ A, ∑ n ∈ Nn, wt n k * Real.sin (2 * Real.pi * h * y k n)| +
        |∑ k ∈ A, ∑ n ∈ Nn, wt n k *
          (gsq (y k n) - ∑ h ∈ Icc 1 H, bb h * Real.sin (2 * Real.pi * h * y k n))| := abs_add_le _ _
    _ ≤ (∑ h ∈ Icc 1 H, 4 / (Real.pi * h)) * (Wa * Mb) +
        (2 / (H + 1) * ∑ k ∈ A, ∑ n ∈ Nn, wt n k + 4 * (Wa * Mb)) := add_le_add hfirst hsecond
    _ = _ := by ring

end ThetaSum

#print axioms ThetaSum.block_heads
