-- Copied from the companion project (lean-upper/Upper/Main.lean). Only the import and the namespace
-- were changed (`Arxiv.«2501.03234»` → `ThetaSum.Upper`), so that `S` is `ThetaSum.S`.
import ThetaSum.Hypotheses

/-!
# Upper bound for the arithmetic sum `S(p)` (Conjecture 3.3, upper half)

Proof following Appendix A of Berndt–Bhat–Meyer–Xie–Zaharescu (arXiv:2501.03234):
finite Fourier expansion of `(-1)^⌊n/p⌋` over the `2p`-th roots of unity, geometric-sum
bounds via Jordan's inequality, and a harmonic-sum count.
-/

namespace ThetaSum.Upper
open Complex Finset

lemma neg_one_pow_reflect {p h j : ℕ} (hp : p.Prime) (hh : h ∈ Ico 1 p) (hj : j ∈ Ico 1 p) :
    (-1 : ℤ) ^ (j + 1 + h * j / p) = (-1) ^ ((p - h) * j / p) := by
  simp only [mem_Ico] at hh hj
  have hpos : 0 < p := hp.pos
  have hnd : ¬ p ∣ h * j := by
    intro hd
    rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
    · exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)
    · exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)
  set q := h * j / p with hq
  set s := h * j % p with hs
  have hs0 : 0 < s := Nat.pos_of_ne_zero (fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0))
  have hsp : s < p := Nat.mod_lt _ hpos
  have hdiv : p * q + s = h * j := Nat.div_add_mod _ _
  have hqj : q < j := by
    by_contra hc
    push Not at hc
    have : p * j ≤ p * q := Nat.mul_le_mul_left _ hc
    have : h * j < p * j := Nat.mul_lt_mul_of_pos_right hh.2 (by omega)
    omega
  clear_value q s
  obtain ⟨t, rfl⟩ : ∃ t, j = q + 1 + t := ⟨j - q - 1, by omega⟩
  have e : (p - h) * (q + 1 + t) + h * (q + 1 + t) = p * (q + 1 + t) := by
    rw [← add_mul, Nat.sub_add_cancel hh.2.le]
  have e2 : p * (q + 1 + t) = p * q + p + p * t := by ring
  have key : (p - h) * (q + 1 + t) / p = t := by
    apply Nat.div_eq_of_lt_le
    · rw [mul_comm t p]; omega
    · rw [add_mul, one_mul, mul_comm t p]; omega
  rw [key, show q + 1 + t + 1 + q = t + 2 * (q + 1) by ring, pow_add, pow_mul]
  simp

theorem S_eq_double_sum {p : ℕ} (hp : p.Prime) :
    S p = ∑ a ∈ Ico 1 p, ∑ b ∈ Ico 1 p, (-1 : ℤ) ^ (a * b / p) := by
  have h1 : S p = ∑ h ∈ Ico 1 p, ∑ j ∈ Ico 1 p, (-1 : ℤ) ^ ((p - h) * j / p) := by
    unfold S S'
    refine sum_congr rfl fun h hh => sum_congr rfl fun j hj => ?_
    rw [← Nat.cast_mul, Nat.floor_div_eq_div]
    exact neg_one_pow_reflect hp hh hj
  rw [h1]
  have := sum_Ico_reflect (fun a => ∑ j ∈ Ico 1 p, (-1 : ℤ) ^ (a * j / p)) 1 (n := p) (m := p)
    (by omega)
  rw [this]
  rw [show p + 1 - p = 1 by omega, show p + 1 - 1 = p by omega]

/-- `ζ = exp(2πi/(2p)) = exp(πi/p)`, a primitive `2p`-th root of unity. -/
noncomputable def zeta (p : ℕ) : ℂ := Complex.exp (2 * Real.pi * I / ((2 * p : ℕ) : ℂ))

variable {p : ℕ}

lemma zeta_prim (hp : 0 < p) : IsPrimitiveRoot (zeta p) (2 * p) :=
  Complex.isPrimitiveRoot_exp _ (by omega)

lemma zeta_pow_p (hp : 0 < p) : zeta p ^ p = -1 :=
  ((zeta_prim hp).pow (by omega) (by ring : 2 * p = p * 2)).eq_neg_one_of_two_right

lemma norm_zeta (hp : 0 < p) : ‖zeta p‖ = 1 := (zeta_prim hp).norm'_eq_one (by omega)

lemma sum_A (hp : 0 < p) (k : ℕ) :
    ∑ l ∈ range p, zeta p ^ ((2 * l + 1) * k) = if p ∣ k then (p : ℂ) * (-1) ^ (k / p) else 0 := by
  have hpr := zeta_prim hp
  have e : ∀ l, zeta p ^ ((2 * l + 1) * k) = zeta p ^ k * ((zeta p ^ 2) ^ k) ^ l := by
    intro l; rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
  simp_rw [e, ← mul_sum]
  split_ifs with hk
  · obtain ⟨c, rfl⟩ := hk
    have h2 : (zeta p ^ 2) ^ (p * c) = 1 := by
      rw [← pow_mul, show 2 * (p * c) = (2 * p) * c by ring, pow_mul, hpr.pow_eq_one, one_pow]
    simp [h2, pow_mul, zeta_pow_p hp, Nat.mul_div_cancel_left c hp, mul_comm]
  · have hne : (zeta p ^ 2) ^ k ≠ 1 := by
      rw [← pow_mul, Ne, hpr.pow_eq_one_iff_dvd]
      intro h; exact hk (Nat.dvd_of_mul_dvd_mul_left two_pos h)
    have h1 : ((zeta p ^ 2) ^ k) ^ p = 1 := by
      rw [← pow_mul, ← pow_mul, show 2 * (k * p) = (2 * p) * k by ring, pow_mul, hpr.pow_eq_one,
        one_pow]
    rw [geom_sum_eq hne, h1, sub_self, zero_div, mul_zero]

/-- Exact finite Fourier expansion of `(-1)^⌊n/p⌋`. -/
lemma expansion (hp : 0 < p) (n : ℕ) :
    (p : ℂ) * (-1) ^ (n / p) = - ∑ l ∈ range p,
      (∑ m ∈ Ico 1 (p + 1), (zeta p ^ (2 * l + 1)) ^ m) * (zeta p ^ (2 * l + 1)) ^ n := by
  have e : ∀ l, (∑ m ∈ Ico 1 (p + 1), (zeta p ^ (2 * l + 1)) ^ m) * (zeta p ^ (2 * l + 1)) ^ n
      = ∑ m ∈ Ico 1 (p + 1), zeta p ^ ((2 * l + 1) * (n + m)) := by
    intro l; rw [sum_mul]; refine sum_congr rfl fun m _ => ?_
    rw [← pow_add, ← pow_mul, add_comm m n]
  simp_rw [e]
  rw [sum_comm]
  simp_rw [sum_A hp]
  have hdm := Nat.div_add_mod n p
  have hml := Nat.mod_lt n hp
  rw [sum_eq_single (p - n % p)]
  · have hd : n + (p - n % p) = p * (n / p + 1) := by rw [mul_add, mul_one]; omega
    rw [ite_eq_left ⟨_, hd⟩, hd, Nat.mul_div_cancel_left _ hp, pow_succ]
    ring
  · intro m hm hne
    rw [ite_eq_right]
    intro hd
    apply hne
    simp only [mem_Ico] at hm
    have h2 : p ∣ n % p + m := by
      have : n + m = p * (n / p) + (n % p + m) := by omega
      rw [this] at hd
      exact (Nat.dvd_add_right (dvd_mul_right p _)).1 hd
    obtain ⟨k, hk⟩ := h2
    have hk2 : k < 2 := by
      by_contra hc
      have : p * 2 ≤ p * k := Nat.mul_le_mul_left _ (by omega)
      omega
    interval_cases k <;> omega
  · intro h; exfalso; apply h; simp only [mem_Ico]; omega

/-- Jordan's inequality in the form we need. -/
lemma jordan (hp : 0 < p) {x : ℕ} (hx : x ≤ p) :
    (x : ℝ) / p ≤ Real.sin (Real.pi * x / (2 * p)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hxR : (x : ℝ) ≤ p := by exact_mod_cast hx
  have h0 : 0 ≤ Real.pi * x / (2 * p) := by positivity
  have h1 : Real.pi * x / (2 * p) ≤ Real.pi / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_pos]
  have := Real.mul_le_sin h0 h1
  calc (x : ℝ) / p = 2 / Real.pi * (Real.pi * x / (2 * p)) := by
        field_simp
    _ ≤ _ := this

/-- Distance function `1 / min(q, 2p - q)`. -/
noncomputable def Fq (p q : ℕ) : ℝ := 1 / ((min q (2 * p - q) : ℕ) : ℝ)

lemma Fq_nonneg (p q : ℕ) : 0 ≤ Fq p q := by unfold Fq; positivity

lemma norm_zeta_pow_sub_one (hp : 0 < p) (t : ℕ) (ht : ¬ 2 * p ∣ t) :
    2 * ((min (t % (2 * p)) (2 * p - t % (2 * p)) : ℕ) : ℝ) / p ≤ ‖zeta p ^ t - 1‖ := by
  have hpr := zeta_prim hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  set q := t % (2 * p) with hq
  have hqlt : q < 2 * p := Nat.mod_lt _ (by omega)
  have hq0 : q ≠ 0 := fun h => ht (Nat.dvd_of_mod_eq_zero h)
  have e1 : zeta p ^ t = zeta p ^ q := by
    conv_lhs => rw [← Nat.mod_add_div t (2 * p)]
    rw [pow_add, pow_mul, hpr.pow_eq_one, one_pow, mul_one]
  have e2 : zeta p ^ q = Complex.exp (I * ((Real.pi * q / p : ℝ) : ℂ)) := by
    rw [zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [e1, e2, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul]
  rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have key : ((min q (2 * p - q) : ℕ) : ℝ) / p ≤ |Real.sin (Real.pi * q / p / 2)| := by
    rcases le_or_gt q p with h | h
    · rw [min_eq_left (by omega)]
      have := jordan hp h
      rw [show Real.pi * q / p / 2 = Real.pi * q / (2 * p) by ring]
      exact this.trans (le_abs_self _)
    · rw [min_eq_right (by omega)]
      have := jordan hp (x := 2 * p - q) (by omega)
      have e3 : Real.pi * q / p / 2 = Real.pi - Real.pi * ((2 * p - q : ℕ) : ℝ) / (2 * p) := by
        rw [Nat.cast_sub hqlt.le]; push_cast; field_simp; ring
      rw [e3, Real.sin_pi_sub]
      exact this.trans (le_abs_self _)
  calc 2 * ((min q (2 * p - q) : ℕ) : ℝ) / p = 2 * (((min q (2 * p - q) : ℕ) : ℝ) / p) := by ring
    _ ≤ _ := by gcongr

lemma geom_bound (hp : 0 < p) (t : ℕ) (ht : ¬ 2 * p ∣ t) {m n : ℕ} (hmn : m ≤ n) :
    ‖∑ i ∈ Ico m n, (zeta p ^ t) ^ i‖ ≤ p * Fq p (t % (2 * p)) := by
  have hpr := zeta_prim hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hx1 : zeta p ^ t ≠ 1 := by rw [Ne, hpr.pow_eq_one_iff_dvd]; exact ht
  have hxn : ‖zeta p ^ t‖ = 1 := by rw [norm_pow, norm_zeta hp, one_pow]
  have hlow := norm_zeta_pow_sub_one hp t ht
  set d : ℕ := min (t % (2 * p)) (2 * p - t % (2 * p)) with hd
  have hqlt : t % (2 * p) < 2 * p := Nat.mod_lt _ (by omega)
  have hq0 : t % (2 * p) ≠ 0 := fun h => ht (Nat.dvd_of_mod_eq_zero h)
  have hd0 : 0 < d := by rw [hd]; omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  rw [geom_sum_Ico hx1 hmn, norm_div]
  have hnum : ‖(zeta p ^ t) ^ n - (zeta p ^ t) ^ m‖ ≤ 2 := by
    calc _ ≤ ‖(zeta p ^ t) ^ n‖ + ‖(zeta p ^ t) ^ m‖ := norm_sub_le _ _
      _ = 2 := by simp [norm_pow, norm_zeta hp]; norm_num
  have hden : 0 < ‖zeta p ^ t - 1‖ := lt_of_lt_of_le (by positivity) hlow
  rw [div_le_iff₀ hden]
  unfold Fq
  rw [← hd]
  calc _ ≤ (2 : ℝ) := hnum
    _ = p * (1 / d) * (2 * d / p) := by field_simp
    _ ≤ _ := by gcongr

lemma norm_geom_le_card (hp : 0 < p) (t m n : ℕ) :
    ‖∑ i ∈ Ico m n, (zeta p ^ t) ^ i‖ ≤ ((n - m : ℕ) : ℝ) := by
  calc _ ≤ ∑ i ∈ Ico m n, ‖(zeta p ^ t) ^ i‖ := norm_sum_le _ _
    _ = ((Ico m n).card : ℝ) := by simp [norm_pow, norm_zeta hp]
    _ = _ := by rw [Nat.card_Ico]

lemma harmonic_cast (p : ℕ) : ((harmonic p : ℚ) : ℝ) = ∑ q ∈ range (p + 1), 1 / (q : ℝ) := by
  rw [sum_range_succ']
  simp [harmonic]

lemma sum_Fq_le (p : ℕ) : ∑ q ∈ range (2 * p + 1), Fq p q ≤ 2 * (harmonic p : ℝ) := by
  let h : ℕ → ℝ := fun q => if q ≤ p then 1 / (q : ℝ) else 0
  have hb : ∀ q ∈ range (2 * p + 1), Fq p q ≤ h q + h (2 * p - q) := by
    intro q hq
    simp only [mem_range] at hq
    unfold Fq
    rcases le_or_gt q p with hqp | hqp
    · rw [min_eq_left (by omega)]
      simp only [h, ite_eq_left hqp]
      have : 0 ≤ (if 2 * p - q ≤ p then 1 / ((2 * p - q : ℕ) : ℝ) else 0) := by
        split_ifs <;> positivity
      linarith
    · rw [min_eq_right (by omega)]
      simp only [h, ite_eq_left (show 2 * p - q ≤ p by omega), ite_eq_right (show ¬ q ≤ p by omega)]
      simp
  have hr : ∑ q ∈ range (2 * p + 1), h (2 * p - q) = ∑ q ∈ range (2 * p + 1), h q := by
    rw [← sum_range_reflect h (2 * p + 1)]
    refine sum_congr rfl fun q _ => ?_
    congr 1
  have hs : ∑ q ∈ range (2 * p + 1), h q = harmonic p := by
    rw [harmonic_cast, ← sum_filter]
    congr 1
    ext q; simp only [mem_filter, mem_range]; omega
  calc _ ≤ ∑ q ∈ range (2 * p + 1), (h q + h (2 * p - q)) := sum_le_sum hb
    _ = _ := by rw [sum_add_distrib, hr, hs]; ring

lemma sum_inj_le {p : ℕ} (hp : 0 < p) (s : Finset ℕ) (g : ℕ → ℕ)
    (hinj : Set.InjOn (fun x => g x % (2 * p)) s) :
    ∑ x ∈ s, Fq p (g x % (2 * p)) ≤ 2 * (harmonic p : ℝ) := by
  rw [← sum_image (f := Fq p) (g := fun x => g x % (2 * p)) (fun x hx y hy hxy => hinj hx hy hxy)]
  refine le_trans ?_ (sum_Fq_le p)
  apply sum_le_sum_of_subset_of_nonneg
  · intro q hq
    simp only [mem_image] at hq
    obtain ⟨x, _, rfl⟩ := hq
    simp only [mem_range]
    have := Nat.mod_lt (g x) (show 0 < 2 * p by omega)
    omega
  · intro q _ _; exact Fq_nonneg p q

lemma one_le_harmonic {p : ℕ} (hp : 0 < p) : (1 : ℝ) ≤ harmonic p := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  induction n with
  | zero => simp
  | succ n ih =>
    rw [harmonic_succ]; push_cast
    have := ih (by omega)
    have : (0 : ℝ) ≤ ((n + 1 + 1 : ℕ) : ℝ)⁻¹ := by positivity
    push_cast at this ⊢
    linarith


/-- The key estimate: `p |S(p)| ≤ 4 p² H_p² + p²`. -/
theorem main_bound {p : ℕ} (hp : p.Prime) :
    (p : ℝ) * |(S p : ℝ)| ≤ 4 * (p : ℝ) ^ 2 * (harmonic p : ℝ) ^ 2 + (p : ℝ) ^ 2 := by
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  set H : ℝ := (harmonic p : ℝ) with hH
  have hH1 : 1 ≤ H := one_le_harmonic hp0
  set c : ℕ → ℂ := fun l => ∑ m ∈ Ico 1 (p + 1), (zeta p ^ (2 * l + 1)) ^ m with hc
  set J : ℕ → ℕ → ℂ := fun l a => ∑ b ∈ Ico 1 p, ((zeta p ^ (2 * l + 1)) ^ a) ^ b with hJ
  have hS : (p : ℂ) * (S p : ℂ) = - ∑ l ∈ range p, c l * ∑ a ∈ Ico 1 p, J l a := by
    rw [S_eq_double_sum hp]
    push_cast
    rw [mul_sum]
    simp_rw [mul_sum, expansion hp0, sum_neg_distrib]
    congr 1
    calc _ = ∑ a ∈ Ico 1 p, ∑ l ∈ range p, ∑ b ∈ Ico 1 p,
          c l * ((zeta p ^ (2 * l + 1)) ^ a) ^ b := by
          refine sum_congr rfl fun a _ => ?_
          rw [sum_comm]
          refine sum_congr rfl fun l _ => sum_congr rfl fun b _ => ?_
          simp only [hc, pow_mul]
      _ = _ := by
          rw [sum_comm]
          refine sum_congr rfl fun l _ => ?_
          simp only [hJ, mul_sum]
  have hnorm : (p : ℝ) * |(S p : ℝ)| = ‖(p : ℂ) * (S p : ℂ)‖ := by
    rw [norm_mul, Complex.norm_natCast, Complex.norm_intCast]
  rw [hnorm, hS, norm_neg]
  -- per-`l` bound
  have hl : ∀ l ∈ range p, ‖c l * ∑ a ∈ Ico 1 p, J l a‖ ≤
      p * Fq p ((2 * l + 1) % (2 * p)) * (2 * p * H) +
        (if 2 * l + 1 = p then (p : ℝ) ^ 2 else 0) := by
    intro l hl
    simp only [mem_range] at hl
    have hodd : ¬ 2 * p ∣ 2 * l + 1 := by
      intro h; have := (dvd_mul_right 2 p).trans h; omega
    have hcl : ‖c l‖ ≤ p * Fq p ((2 * l + 1) % (2 * p)) :=
      geom_bound hp0 (2 * l + 1) hodd (by omega)
    have hF0 : 0 ≤ (p : ℝ) * Fq p ((2 * l + 1) % (2 * p)) := by
      have := Fq_nonneg p ((2 * l + 1) % (2 * p)); positivity
    rw [norm_mul]
    by_cases hr : 2 * l + 1 = p
    · rw [ite_eq_left hr]
      have hmod : (2 * l + 1) % (2 * p) = p := by rw [hr]; exact Nat.mod_eq_of_lt (by omega)
      have hc1 : ‖c l‖ ≤ 1 := by
        refine hcl.trans (le_of_eq ?_)
        rw [hmod]; unfold Fq
        rw [show min p (2 * p - p) = p by omega]
        field_simp
      have hJ1 : ‖∑ a ∈ Ico 1 p, J l a‖ ≤ (p : ℝ) ^ 2 := by
        calc _ ≤ ∑ a ∈ Ico 1 p, ‖J l a‖ := norm_sum_le _ _
          _ ≤ ∑ a ∈ Ico 1 p, (p : ℝ) := by
            refine sum_le_sum fun a _ => ?_
            have : J l a = ∑ b ∈ Ico 1 p, (zeta p ^ ((2 * l + 1) * a)) ^ b := by
              simp only [hJ, pow_mul]
            rw [this]
            refine (norm_geom_le_card hp0 _ _ _).trans ?_
            exact_mod_cast Nat.sub_le p 1
          _ ≤ (p : ℝ) ^ 2 := by
            rw [sum_const, Nat.card_Ico, nsmul_eq_mul, sq]
            gcongr
            exact_mod_cast Nat.sub_le p 1
      have h2 : ‖c l‖ * ‖∑ a ∈ Ico 1 p, J l a‖ ≤ 1 * (p : ℝ) ^ 2 := by
        gcongr
      have h3 : 0 ≤ (p : ℝ) * Fq p ((2 * l + 1) % (2 * p)) * (2 * p * H) := by positivity
      linarith
    · rw [ite_eq_right hr, add_zero]
      have hcop : Nat.Coprime (2 * p) (2 * l + 1) := by
        refine Nat.coprime_mul_iff_left.2 ⟨?_, ?_⟩
        · exact Nat.coprime_two_left.2 (odd_two_mul_add_one l)
        · rw [Nat.Prime.coprime_iff_not_dvd hp]
          rintro ⟨k, hk⟩
          have hk2 : k < 2 := by
            by_contra hc'
            have : p * 2 ≤ p * k := Nat.mul_le_mul_left _ (by omega)
            omega
          interval_cases k <;> omega
      have hJb : ∀ a ∈ Ico 1 p, ‖J l a‖ ≤ p * Fq p ((2 * l + 1) * a % (2 * p)) := by
        intro a ha
        simp only [mem_Ico] at ha
        have : J l a = ∑ b ∈ Ico 1 p, (zeta p ^ ((2 * l + 1) * a)) ^ b := by
          simp only [hJ, pow_mul]
        rw [this]
        refine geom_bound hp0 _ ?_ (by omega)
        intro hd
        have hd' : p ∣ (2 * l + 1) * a := (dvd_mul_left p 2).trans hd
        rcases (Nat.Prime.dvd_mul hp).1 hd' with h | h
        · exact (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.Coprime.coprime_mul_left hcop) h
        · exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
      have hsum : ∑ a ∈ Ico 1 p, Fq p ((2 * l + 1) * a % (2 * p)) ≤ 2 * H := by
        apply sum_inj_le hp0
        intro a ha b hb hab
        simp only [coe_Ico, Set.mem_Ico] at ha hb
        have hm : a ≡ b [MOD 2 * p] := Nat.ModEq.cancel_left_of_coprime hcop hab
        unfold Nat.ModEq at hm
        rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hm
      have hJ2 : ‖∑ a ∈ Ico 1 p, J l a‖ ≤ p * (2 * H) := by
        calc _ ≤ ∑ a ∈ Ico 1 p, ‖J l a‖ := norm_sum_le _ _
          _ ≤ ∑ a ∈ Ico 1 p, (p : ℝ) * Fq p ((2 * l + 1) * a % (2 * p)) := sum_le_sum hJb
          _ = p * ∑ a ∈ Ico 1 p, Fq p ((2 * l + 1) * a % (2 * p)) := by rw [mul_sum]
          _ ≤ p * (2 * H) := by gcongr
      calc ‖c l‖ * ‖∑ a ∈ Ico 1 p, J l a‖
          ≤ (p * Fq p ((2 * l + 1) % (2 * p))) * (p * (2 * H)) := by gcongr
        _ = _ := by ring
  have hsumF : ∑ l ∈ range p, Fq p ((2 * l + 1) % (2 * p)) ≤ 2 * H := by
    apply sum_inj_le hp0
    intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    simp only at hab
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hab
    omega
  have hite : ∑ l ∈ range p, (if 2 * l + 1 = p then (p : ℝ) ^ 2 else 0) ≤ (p : ℝ) ^ 2 := by
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
    have : ((range p).filter (fun l => 2 * l + 1 = p)).card ≤ 1 := by
      apply Finset.card_le_one.2
      intro a ha b hb
      simp only [mem_filter] at ha hb
      omega
    have : (((range p).filter (fun l => 2 * l + 1 = p)).card : ℝ) ≤ 1 := by exact_mod_cast this
    nlinarith [sq_nonneg (p : ℝ)]
  calc _ ≤ ∑ l ∈ range p, ‖c l * ∑ a ∈ Ico 1 p, J l a‖ := norm_sum_le _ _
    _ ≤ ∑ l ∈ range p, (p * Fq p ((2 * l + 1) % (2 * p)) * (2 * p * H) +
        (if 2 * l + 1 = p then (p : ℝ) ^ 2 else 0)) := sum_le_sum hl
    _ = 2 * (p : ℝ) ^ 2 * H * ∑ l ∈ range p, Fq p ((2 * l + 1) % (2 * p)) +
        ∑ l ∈ range p, (if 2 * l + 1 = p then (p : ℝ) ^ 2 else 0) := by
      rw [sum_add_distrib, mul_sum]
      congr 1
      refine sum_congr rfl fun l _ => ?_
      ring
    _ ≤ 2 * (p : ℝ) ^ 2 * H * (2 * H) + (p : ℝ) ^ 2 := by gcongr
    _ = _ := by ring

/-- Bound valid for every prime (including `p = 2`). -/
theorem S_abs_le' {p : ℕ} (hp : p.Prime) :
    |(S p : ℝ)| ≤ 5 * p * (harmonic p : ℝ) ^ 2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hH1 : (1 : ℝ) ≤ harmonic p := one_le_harmonic hp.pos
  have h := main_bound hp
  have h2 : |(S p : ℝ)| ≤ 4 * p * (harmonic p : ℝ) ^ 2 + p := by
    refine le_of_mul_le_mul_left ?_ hpR
    calc _ ≤ _ := h
      _ = _ := by ring
  have h3 : (p : ℝ) ≤ p * (harmonic p : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ (harmonic p : ℝ) ^ 2 := one_le_pow₀ hH1
    nlinarith
  linarith

/-- **Upper bound** (Appendix A of arXiv:2501.03234): for an odd prime `p`,
`|S(p)| ≤ 5 p H_p²`. -/
theorem S_abs_le {p : ℕ} (hp : p.Prime) (_hp2 : p ≠ 2) :
    |(S p : ℝ)| ≤ 5 * p * (harmonic p : ℝ) ^ 2 :=
  S_abs_le' hp

theorem S_abs_le_log {p : ℕ} (hp : p.Prime) :
    |(S p : ℝ)| ≤ 5 * p * (1 + Real.log p) ^ 2 := by
  refine (S_abs_le' hp).trans ?_
  have h0 : (0 : ℝ) ≤ harmonic p := by
    have := one_le_harmonic hp.pos; linarith
  have h1 : (harmonic p : ℝ) ≤ 1 + Real.log p := harmonic_le_one_add_log p
  have : (harmonic p : ℝ) ^ 2 ≤ (1 + Real.log p) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have hpR : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  gcongr

/-- **Conjecture 3.3 (upper half)** of arXiv:2501.03234. -/
theorem conjecture_3_3_upper :
    ∀ C₂ > (0 : ℝ), ∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in Filter.atTop,
      k.Prime → (S k : ℝ) < C₂ * (k : ℝ) ^ (1 + ε) := by
  intro C hC ε hε
  set δ : ℝ := ε / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  set K : ℝ := (1 + 1 / δ) ^ 2 with hK
  have hT : Filter.Tendsto (fun k : ℕ => (k : ℝ) ^ (ε / 2)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hT.eventually_gt_atTop (5 * K / C), Filter.eventually_ge_atTop 1]
    with k hk hk1 hprime
  have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have kpos : (0 : ℝ) < k := by linarith
  have hlog : Real.log k ≤ (k : ℝ) ^ δ / δ := Real.log_le_rpow_div kpos.le hδ0
  have hkδ : 1 ≤ (k : ℝ) ^ δ := Real.one_le_rpow hk1R hδ0.le
  have hl0 : 0 ≤ 1 + Real.log k := by have := Real.log_nonneg hk1R; linarith
  have hb : 1 + Real.log k ≤ (1 + 1 / δ) * (k : ℝ) ^ δ := by
    have : (k : ℝ) ^ δ / δ = 1 / δ * (k : ℝ) ^ δ := by ring
    nlinarith
  have hsq : (1 + Real.log k) ^ 2 ≤ K * (k : ℝ) ^ (ε / 2) := by
    have e : (k : ℝ) ^ (ε / 2) = (k : ℝ) ^ δ * (k : ℝ) ^ δ := by
      rw [← Real.rpow_add kpos]; congr 1; rw [hδ]; ring
    rw [e, hK]
    nlinarith [pow_le_pow_left₀ hl0 hb 2]
  have hK5 : 5 * K < C * (k : ℝ) ^ (ε / 2) := by
    rw [div_lt_iff₀ hC] at hk; linarith
  have hpos : 0 < (k : ℝ) ^ (ε / 2) := Real.rpow_pos_of_pos kpos _
  have e2 : (k : ℝ) ^ (1 + ε) = k * ((k : ℝ) ^ (ε / 2) * (k : ℝ) ^ (ε / 2)) := by
    rw [← Real.rpow_add kpos, Real.rpow_add kpos, Real.rpow_one]; congr 2; ring
  calc (S k : ℝ) ≤ |(S k : ℝ)| := le_abs_self _
    _ ≤ 5 * k * (1 + Real.log k) ^ 2 := S_abs_le_log hprime
    _ ≤ 5 * k * (K * (k : ℝ) ^ (ε / 2)) := by gcongr
    _ = k * (5 * K) * (k : ℝ) ^ (ε / 2) := by ring
    _ < k * (C * (k : ℝ) ^ (ε / 2)) * (k : ℝ) ^ (ε / 2) := by gcongr
    _ = C * (k : ℝ) ^ (1 + ε) := by rw [e2]; ring

end ThetaSum.Upper
