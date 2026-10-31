import Upper.Main

/-!
# Section 3 of `theta_sum_v3.pdf`: the dual (cotangent) formula and Theorem A

* `T_dual`        — Lemma 3.1 (dual formula for `T(a)`),
* `S_eq_sum_T`    — Lemma 2.1(b) (`S(p) = Σ_{a odd} T(a)`),
* `S_dual`        — formula (3.1),
* `Cp_sign_form`, `Cp_abs_le` — Lemma 3.2 (sign form, `|C_p(k)| ≤ C_p(1)`),
* `Cp_one_le`     — Lemma 3.3,
* `theorem_A`, `S_abs_le_cot` — Theorem A with the elementary constant `2` in place of `K₀`.
-/
namespace Arxiv.«2501.03234»
open Complex Finset

/-- `T(a) = Σ_{b=1}^{p-1} (-1)^⌊ab/p⌋`. -/
def T (p a : ℕ) : ℤ := ∑ b ∈ Ico 1 p, (-1 : ℤ) ^ (a * b / p)

/-- Half-range cotangent sum `C_m(k) = Σ_{0<a<m, a odd} cot(π k a / 2m)`. -/
noncomputable def Cp (m k : ℕ) : ℝ :=
  ∑ a ∈ (range m).filter Odd, Real.cot (Real.pi * k * a / (2 * m))

/-- `σ(m) = (-1)^⌊m/p⌋`. -/
def sigma (p m : ℕ) : ℤ := (-1) ^ (m / p)

/-- Lemma 2.1(b): `T(a) = 0` for even `a`. -/
lemma T_even {p a : ℕ} (hp : p.Prime) (ha : a ∈ Ico 1 p) (hev : Even a) : T p a = 0 := by
  have h1 : T p a = ∑ b ∈ Ico 1 p, (-1 : ℤ) ^ ((p - b) * a / p) := by
    unfold T
    have := sum_Ico_reflect (fun b => (-1 : ℤ) ^ (a * b / p)) 1 (n := p) (m := p) (by omega)
    rw [show p + 1 - p = 1 by omega, show p + 1 - 1 = p by omega] at this
    rw [← this]
    refine sum_congr rfl fun b _ => ?_
    rw [mul_comm]
  have h2 : ∑ b ∈ Ico 1 p, (-1 : ℤ) ^ ((p - b) * a / p) = - T p a := by
    unfold T
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun b hb => ?_
    rw [← neg_one_pow_reflect hp hb ha]
    obtain ⟨c, rfl⟩ := hev
    rw [show c + c + 1 + b * (c + c) / p = (b * (c + c) / p + 1) + 2 * c by ring, pow_add,
      pow_mul, pow_succ, mul_comm (c + c) b]
    simp
  omega

lemma S_eq_sum_T {p : ℕ} (hp : p.Prime) : S p = ∑ a ∈ (range p).filter Odd, T p a := by
  rw [S_eq_double_sum hp]
  change ∑ a ∈ Ico 1 p, T p a = _
  rw [← sum_filter_add_sum_filter_not (Ico 1 p) Odd]
  rw [sum_eq_zero (s := (Ico 1 p).filter (fun a => ¬ Odd a)), add_zero]
  · congr 1
    ext a; simp only [mem_filter, mem_Ico, mem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1.2, h2⟩
    · rintro ⟨h1, h2⟩; refine ⟨⟨?_, h1⟩, h2⟩; rcases h2 with ⟨c, rfl⟩; omega
  · intro a ha
    simp only [mem_filter, Nat.not_odd_iff_even] at ha
    exact T_even hp ha.1 ha.2

/-- Odd numbers below `2h+1` are `2x+1`, `x < h`. -/
lemma sum_odd_range {M : Type*} [AddCommMonoid M] (h : ℕ) (f : ℕ → M) :
    ∑ k ∈ (range (2 * h + 1)).filter Odd, f k = ∑ x ∈ range h, f (2 * x + 1) := by
  symm
  rw [← sum_image (s := range h) (g := fun x => 2 * x + 1) (by intro x _ y _ hxy; simp at hxy; omega)]
  congr 1
  ext k; simp only [mem_image, mem_range, mem_filter]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨by omega, ⟨x, rfl⟩⟩
  · rintro ⟨hk, ⟨x, rfl⟩⟩; exact ⟨x, by omega, rfl⟩

lemma cot_add_nat_mul_pi (x : ℝ) (n : ℕ) : Real.cot (x + n * Real.pi) = Real.cot x := by
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cos_add_nat_mul_pi,
    Real.sin_add_nat_mul_pi, mul_div_mul_left _ _ (pow_ne_zero _ (by norm_num))]

lemma cot_nat_mul_pi_sub (x : ℝ) (n : ℕ) : Real.cot (n * Real.pi - x) = - Real.cot x := by
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cos_nat_mul_pi_sub,
    Real.sin_nat_mul_pi_sub, div_neg, mul_div_mul_left _ _ (pow_ne_zero _ (by norm_num))]

lemma cot_formula (t : ℝ) (h : Complex.exp (2 * t * I) ≠ 1) :
    (Complex.exp (2 * t * I) + 1) / (Complex.exp (2 * t * I) - 1) = -I * (Real.cot t : ℂ) := by
  set c : ℝ := Real.cos t with hc
  set s : ℝ := Real.sin t with hs
  have e : Complex.exp (2 * t * I) = ((c : ℂ) + (s : ℂ) * I) ^ 2 := by
    rw [show (2 * t * I : ℂ) = ((2 : ℕ) : ℂ) * (t * I) by push_cast; ring, Complex.exp_nat_mul,
      Complex.exp_mul_I, hc, hs, Complex.ofReal_cos, Complex.ofReal_sin]
  have hcs : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by
    have := Real.cos_sq_add_sin_sq t
    exact_mod_cast this
  have e1 : ((c : ℂ) + (s : ℂ) * I) ^ 2 + 1 = 2 * c * ((c : ℂ) + (s : ℂ) * I) := by
    linear_combination (-1 : ℂ) * hcs + (s : ℂ) ^ 2 * I_sq
  have e2 : ((c : ℂ) + (s : ℂ) * I) ^ 2 - 1 = 2 * s * I * ((c : ℂ) + (s : ℂ) * I) := by
    linear_combination hcs - (s : ℂ) ^ 2 * I_sq
  rw [e] at h ⊢
  have hu : ((c : ℂ) + (s : ℂ) * I) ≠ 0 := by
    intro h0
    have : (1 : ℂ) = 0 := by
      linear_combination -hcs + ((c : ℂ) - s * I) * h0 + (s : ℂ) ^ 2 * I_sq
    exact one_ne_zero this
  have hs0 : (s : ℂ) ≠ 0 := by
    intro h0; apply h; rw [← sub_eq_zero, e2, h0]; ring
  rw [e1, e2, mul_div_mul_right _ _ hu, Real.cot_eq_cos_div_sin, ← hc, ← hs]
  push_cast
  field_simp
  linear_combination (c : ℂ) * I_sq

lemma zeta_pow_eq_exp {p : ℕ} (hp : 0 < p) (n : ℕ) :
    zeta p ^ n = Complex.exp (2 * ((Real.pi * n / (2 * p) : ℝ) : ℂ) * I) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold zeta
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- One Fourier mode: `-(c_l · Σ_b w_l^{ab}) = cot α cot β + i cot β`. -/
lemma mode_eq {p : ℕ} (hp : 0 < p) {r a : ℕ} (hr : Odd r) (ha : Odd a) :
    -((∑ m ∈ Ico 1 (p + 1), (zeta p ^ r) ^ m) * ∑ b ∈ Ico 1 p, ((zeta p ^ r) ^ a) ^ b) =
      ((Real.cot (Real.pi * r / (2 * p)) * Real.cot (Real.pi * r * a / (2 * p)) : ℝ) : ℂ) +
        I * (Real.cot (Real.pi * r * a / (2 * p)) : ℂ) := by
  have hpr := zeta_prim hp
  set w := zeta p ^ r with hw
  set x := w ^ a with hx
  have hwp : w ^ p = -1 := by rw [hw, ← pow_mul, mul_comm, pow_mul, zeta_pow_p hp, hr.neg_one_pow]
  have hxp : x ^ p = -1 := by rw [hx, ← pow_mul, mul_comm, pow_mul, hwp, ha.neg_one_pow]
  have hw1 : w ≠ 1 := by
    rw [hw, Ne, hpr.pow_eq_one_iff_dvd]
    intro h; have := (dvd_mul_right 2 p).trans h; rw [← even_iff_two_dvd] at this
    exact (Nat.not_even_iff_odd.2 hr) this
  have hx1 : x ≠ 1 := by
    rw [hx, hw, ← pow_mul, Ne, hpr.pow_eq_one_iff_dvd]
    intro h; have := (dvd_mul_right 2 p).trans h; rw [← even_iff_two_dvd] at this
    exact (Nat.not_even_iff_odd.2 (hr.mul ha)) this
  have hw1' : w - 1 ≠ 0 := sub_ne_zero.2 hw1
  have hx1' : x - 1 ≠ 0 := sub_ne_zero.2 hx1
  have hc : ∑ m ∈ Ico 1 (p + 1), w ^ m = -(1 + (w + 1) / (w - 1)) := by
    rw [geom_sum_Ico hw1 (by omega), pow_succ, hwp]
    field_simp
    ring
  have hJ : ∑ b ∈ Ico 1 p, x ^ b = -((x + 1) / (x - 1)) := by
    rw [geom_sum_Ico hx1 (by omega), hxp]
    field_simp
    ring
  have hwe : w = Complex.exp (2 * ((Real.pi * r / (2 * p) : ℝ) : ℂ) * I) := zeta_pow_eq_exp hp r
  have hxe : x = Complex.exp (2 * ((Real.pi * r * a / (2 * p) : ℝ) : ℂ) * I) := by
    rw [hx, hw, ← pow_mul, zeta_pow_eq_exp hp]; push_cast; ring_nf
  have hA : (w + 1) / (w - 1) = -I * (Real.cot (Real.pi * r / (2 * p)) : ℂ) := by
    rw [hwe]; exact cot_formula _ (hwe ▸ hw1)
  have hB : (x + 1) / (x - 1) = -I * (Real.cot (Real.pi * r * a / (2 * p)) : ℂ) := by
    rw [hxe]; exact cot_formula _ (hxe ▸ hx1)
  rw [hc, hJ, hA, hB, Complex.ofReal_mul]
  linear_combination (-(Real.cot (Real.pi * r / (2 * p)) : ℂ) *
    (Real.cot (Real.pi * r * a / (2 * p)) : ℂ)) * I_sq

lemma T_real {p a : ℕ} (hp : 0 < p) (ha : Odd a) :
    (p : ℝ) * (T p a : ℝ) = ∑ l ∈ range p,
      Real.cot (Real.pi * ((2 * l + 1 : ℕ) : ℝ) / (2 * p)) *
        Real.cot (Real.pi * ((2 * l + 1 : ℕ) : ℝ) * a / (2 * p)) := by
  have hC : (p : ℂ) * (T p a : ℂ) = ∑ l ∈ range p,
      (((Real.cot (Real.pi * ((2 * l + 1 : ℕ) : ℝ) / (2 * p)) *
        Real.cot (Real.pi * ((2 * l + 1 : ℕ) : ℝ) * a / (2 * p)) : ℝ) : ℂ) +
        I * (Real.cot (Real.pi * ((2 * l + 1 : ℕ) : ℝ) * a / (2 * p)) : ℂ)) := by
    have e1 : (p : ℂ) * (T p a : ℂ) = - ∑ l ∈ range p,
        (∑ m ∈ Ico 1 (p + 1), (zeta p ^ (2 * l + 1)) ^ m) *
          ∑ b ∈ Ico 1 p, ((zeta p ^ (2 * l + 1)) ^ a) ^ b := by
      unfold T
      push_cast
      rw [mul_sum]
      simp_rw [expansion hp, mul_sum, ← pow_mul]
      rw [sum_neg_distrib, sum_comm]
      simp only [mul_assoc]
    rw [e1, ← sum_neg_distrib]
    refine sum_congr rfl fun l _ => ?_
    exact mode_eq hp (odd_two_mul_add_one l) ha
  have e2 : (p : ℂ) * (T p a : ℂ) = (((p : ℝ) * (T p a : ℝ) : ℝ) : ℂ) := by push_cast; ring
  rw [e2] at hC
  have := congrArg Complex.re hC
  simpa only [Complex.re_sum, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, one_mul] using this

/-- Folding `r ↦ 2p - r`. -/
lemma fold_sum (p h : ℕ) (hpe : p = 2 * h + 1) (f : ℕ → ℝ)
    (hsym : ∀ r ≤ 2 * p, f (2 * p - r) = f r) (hmid : f p = 0) :
    ∑ l ∈ range p, f (2 * l + 1) = 2 * ∑ k ∈ (range p).filter Odd, f k := by
  subst hpe
  rw [sum_odd_range, show 2 * h + 1 = h + (h + 1) by ring, sum_range_add, sum_range_succ']
  have : ∑ k ∈ range h, f (2 * (h + (k + 1)) + 1) = ∑ x ∈ range h, f (2 * x + 1) := by
    rw [← sum_range_reflect]
    refine sum_congr rfl fun x hx => ?_
    simp only [mem_range] at hx
    rw [show 2 * (h + (h - 1 - x + 1)) + 1 = 2 * (2 * h + 1) - (2 * x + 1) by omega]
    exact hsym _ (by omega)
  rw [this, show 2 * (h + 0) + 1 = 2 * h + 1 by ring, hmid]
  ring

/-- **Lemma 3.1** (dual formula): for odd `p` and odd `a`,
`T(a) = (2/p) Σ_{0<k<p, k odd} cot(πk/2p) cot(πka/2p)`. -/
theorem T_dual {p a : ℕ} (hp : Odd p) (ha : Odd a) :
    (T p a : ℝ) = 2 / p * ∑ k ∈ (range p).filter Odd,
      Real.cot (Real.pi * k / (2 * p)) * Real.cot (Real.pi * k * a / (2 * p)) := by
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have h1 := T_real hp0 ha
  obtain ⟨h, hh⟩ := hp
  have key := fold_sum p h hh (fun k : ℕ => Real.cot (Real.pi * k / (2 * p)) *
      Real.cot (Real.pi * k * a / (2 * p))) ?_ ?_
  · rw [key] at h1
    field_simp
    linarith
  · intro r hr
    rw [Nat.cast_sub hr]
    push_cast
    have e1 : Real.pi * (2 * p - r) / (2 * p) = ((1 : ℕ) : ℝ) * Real.pi - Real.pi * r / (2 * p) := by
      rw [Nat.cast_one, one_mul]; field_simp
    have e2 : Real.pi * (2 * p - r) * a / (2 * p) =
        (a : ℝ) * Real.pi - Real.pi * r * a / (2 * p) := by
      field_simp
    rw [e1, e2, cot_nat_mul_pi_sub, cot_nat_mul_pi_sub]
    ring
  · show Real.cot (Real.pi * p / (2 * p)) * Real.cot (Real.pi * p * a / (2 * p)) = 0
    rw [show Real.pi * p / (2 * p) = Real.pi / 2 by field_simp, Real.cot_eq_cos_div_sin,
      Real.cos_pi_div_two, zero_div, zero_mul]

/-- **(3.1)**: `S(p) = (2/p) Σ_{0<k<p, k odd} cot(πk/2p) C_p(k)` for odd primes `p`. -/
theorem S_dual {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (S p : ℝ) = 2 / p * ∑ k ∈ (range p).filter Odd, Real.cot (Real.pi * k / (2 * p)) * Cp p k := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  rw [S_eq_sum_T hp]
  push_cast
  rw [sum_congr rfl fun a ha => T_dual hodd (mem_filter.1 ha).2, ← mul_sum, sum_comm]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [Cp, mul_sum]

lemma sigma_eq {p : ℕ} (hp : 0 < p) (m : ℕ) :
    sigma p m = if m % (2 * p) < p then 1 else -1 := by
  have e : m / p = 2 * (m / (2 * p)) + (m % (2 * p)) / p := by
    conv_lhs => rw [← Nat.mod_add_div m (2 * p)]
    rw [show m % (2 * p) + 2 * p * (m / (2 * p)) = m % (2 * p) + p * (2 * (m / (2 * p))) by ring,
      Nat.add_mul_div_left _ _ hp]
    ring
  have hlt : m % (2 * p) < 2 * p := Nat.mod_lt _ (by omega)
  unfold sigma
  rw [e, pow_add, pow_mul]
  split_ifs with h
  · rw [Nat.div_eq_of_lt h]; simp
  · have h1 : m % (2 * p) / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [h1]; simp

/-- If `(x + a) ≡ 0 (mod n)` with `0 < a < n`, then `x mod n = n - a`. -/
lemma mod_eq_sub_of_add {x a n : ℕ} (h : (x + a) % n = 0) (ha0 : 0 < a) (han : a < n) :
    x % n = n - a := by
  have hn : 0 < n := by omega
  rw [Nat.add_mod, Nat.mod_eq_of_lt han] at h
  set y := x % n + a with hy
  have hxlt : x % n < n := Nat.mod_lt _ hn
  have hy1 : y / n = 1 := by
    apply Nat.div_eq_of_lt_le
    · by_contra hc
      push Not at hc
      rw [Nat.mod_eq_of_lt (by omega)] at h
      omega
    · omega
  have := Nat.div_add_mod y n
  rw [hy1, h] at this
  omega

lemma cot_pos_of_lt {p n : ℕ} (hn0 : 0 < n) (hnp : n < p) :
    0 < Real.cot (Real.pi * n / (2 * p)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnpR : (n : ℝ) < p := by exact_mod_cast hnp
  have h0 : 0 < Real.pi * n / (2 * p) := by positivity
  have h1 : Real.pi * n / (2 * p) < Real.pi / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_pos]
  rw [Real.cot_eq_cos_div_sin]
  apply div_pos
  · exact Real.cos_pos_of_mem_Ioo ⟨by linarith, h1⟩
  · exact Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)

/-- **Lemma 3.2** (sign form): for odd `k` with `p ∤ k` and `k * k̄ ≡ 1 (mod 2p)`,
`C_p(k) = Σ_{0<n<p, n odd} σ(n k̄) cot(πn/2p)`. -/
theorem Cp_sign_form {p k kbar : ℕ} (hp : p.Prime) (hk : Odd k) (hpk : ¬ p ∣ k)
    (hkbar : k * kbar ≡ 1 [MOD 2 * p]) :
    Cp p k = ∑ n ∈ (range p).filter Odd, (sigma p (n * kbar) : ℝ) * Real.cot (Real.pi * n / (2 * p)) := by
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have h2p : 0 < 2 * p := by omega
  have hcop : Nat.Coprime (2 * p) k := by
    refine Nat.coprime_mul_iff_left.2 ⟨Nat.coprime_two_left.2 hk, ?_⟩
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hpk
  -- the map `a ↦ n(a)`
  let φ : ℕ → ℕ := fun a => if k * a % (2 * p) < p then k * a % (2 * p) else 2 * p - k * a % (2 * p)
  -- basic facts for `a` odd in `(0,p)`
  have hu : ∀ a ∈ (range p).filter Odd, Odd (k * a % (2 * p)) ∧ k * a % (2 * p) ≠ p ∧
      k * a % (2 * p) < 2 * p := by
    intro a ha
    simp only [mem_filter, mem_range] at ha
    have hka : Odd (k * a) := hk.mul ha.2
    refine ⟨?_, ?_, Nat.mod_lt _ h2p⟩
    · rw [Nat.odd_iff, Nat.mod_mod_of_dvd _ (dvd_mul_right 2 p), ← Nat.odd_iff]; exact hka
    · intro he
      have hd : p ∣ k * a := by
        have := Nat.div_add_mod (k * a) (2 * p)
        rw [he] at this
        exact ⟨2 * (k * a / (2 * p)) + 1, by linarith [this]⟩
      rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
      · exact hpk h
      · have : 0 < a := ha.2.pos
        exact absurd (Nat.le_of_dvd this h) (by omega)
  have hmaps : ∀ a ∈ (range p).filter Odd, φ a ∈ (range p).filter Odd := by
    intro a ha
    obtain ⟨hodd, hne, hlt⟩ := hu a ha
    simp only [mem_filter, mem_range, φ]
    rw [Nat.odd_iff] at hodd
    split_ifs with h
    · exact ⟨h, Nat.odd_iff.2 hodd⟩
    · refine ⟨by omega, Nat.odd_iff.2 (by omega)⟩
  -- the cotangent identity
  have hcot : ∀ a ∈ (range p).filter Odd, Real.cot (Real.pi * k * a / (2 * p)) =
      (sigma p (k * a) : ℝ) * Real.cot (Real.pi * (φ a) / (2 * p)) := by
    intro a ha
    obtain ⟨hodd, hne, hlt⟩ := hu a ha
    set u := k * a % (2 * p) with hu'
    set q := k * a / (2 * p) with hq
    have hdiv : ((k : ℝ) * a) = 2 * p * q + u := by
      have := Nat.div_add_mod (k * a) (2 * p); exact_mod_cast this.symm
    have e1 : Real.pi * k * a / (2 * p) = Real.pi * u / (2 * p) + q * Real.pi := by
      rw [mul_assoc, hdiv]; field_simp; ring
    rw [e1, cot_add_nat_mul_pi, sigma_eq hp0, ← hu']
    simp only [φ, ← hu']
    split_ifs with h
    · simp
    · have e2 : Real.pi * u / (2 * p) = ((1 : ℕ) : ℝ) * Real.pi - Real.pi * ((2 * p - u : ℕ) : ℝ) / (2 * p) := by
        rw [Nat.cast_sub hlt.le]; push_cast; field_simp; ring
      rw [e2, cot_nat_mul_pi_sub]
      simp
  -- the sign identity
  have hsig : ∀ a ∈ (range p).filter Odd, sigma p (φ a * kbar) = sigma p (k * a) := by
    intro a ha
    obtain ⟨hodd, hne, hlt⟩ := hu a ha
    have ha' := ha
    simp only [mem_filter, mem_range] at ha'
    have ha0 : 0 < a := ha'.2.pos
    have hm : k * a % (2 * p) * kbar ≡ a [MOD 2 * p] := by
      calc k * a % (2 * p) * kbar ≡ k * a * kbar [MOD 2 * p] := (Nat.mod_modEq _ _).mul_right _
        _ = a * (k * kbar) := by ring
        _ ≡ a * 1 [MOD 2 * p] := hkbar.mul_left _
        _ = a := mul_one a
    rw [sigma_eq hp0, sigma_eq hp0]
    simp only [φ]
    split_ifs with h1 h2 h2
    · rfl
    · exfalso; apply h2
      rw [hm]; rw [Nat.mod_eq_of_lt (by omega)]; omega
    · exfalso
      have : (2 * p - k * a % (2 * p)) * kbar % (2 * p) = 2 * p - a := by
        apply mod_eq_sub_of_add _ ha0 (by omega)
        have e : (2 * p - k * a % (2 * p)) * kbar + k * a % (2 * p) * kbar = 2 * p * kbar := by
          rw [← add_mul, Nat.sub_add_cancel hlt.le]
        have : (2 * p - k * a % (2 * p)) * kbar + a ≡ 0 [MOD 2 * p] := by
          calc (2 * p - k * a % (2 * p)) * kbar + a
              ≡ (2 * p - k * a % (2 * p)) * kbar + k * a % (2 * p) * kbar [MOD 2 * p] :=
                (hm.symm).add_left _
            _ = 2 * p * kbar := e
            _ ≡ 0 [MOD 2 * p] := Nat.modEq_zero_iff_dvd.2 (dvd_mul_right _ _)
        exact this
      omega
    · rfl
  -- injectivity
  have hinj : Set.InjOn φ ((range p).filter Odd : Set ℕ) := by
    intro a ha b hb hab
    have ha' := ha; have hb' := hb
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at ha' hb'
    obtain ⟨_, _, hlta⟩ := hu a (by simpa using ha)
    obtain ⟨_, _, hltb⟩ := hu b (by simpa using hb)
    have hgcd : Nat.gcd (2 * p) k = 1 := hcop
    simp only [φ] at hab
    have same : k * a % (2 * p) = k * b % (2 * p) → a = b := by
      intro he
      have := Nat.ModEq.cancel_left_of_coprime hgcd he
      unfold Nat.ModEq at this
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    have opp : k * a % (2 * p) + k * b % (2 * p) = 2 * p → False := by
      intro he
      have h1 : k * (a + b) ≡ k * 0 [MOD 2 * p] := by
        unfold Nat.ModEq
        rw [mul_add, Nat.add_mod, he, mul_zero, Nat.zero_mod, Nat.mod_self]
      have := Nat.ModEq.cancel_left_of_coprime hgcd h1
      unfold Nat.ModEq at this
      rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega)] at this
      have := ha'.2.pos
      omega
    split_ifs at hab with h1 h2 h2
    · exact same hab
    · exact (opp (by omega)).elim
    · exact (opp (by omega)).elim
    · exact same (by omega)
  have hsurj : Set.SurjOn φ ((range p).filter Odd : Set ℕ) ((range p).filter Odd : Set ℕ) :=
    Finset.surjOn_of_injOn_of_card_le φ (fun a ha => hmaps a ha) hinj le_rfl
  unfold Cp
  symm
  rw [show ((range p).filter Odd).sum (fun n => (sigma p (n * kbar) : ℝ) *
      Real.cot (Real.pi * n / (2 * p))) = ∑ a ∈ (range p).filter Odd,
      (sigma p (φ a * kbar) : ℝ) * Real.cot (Real.pi * (φ a) / (2 * p)) from
    (sum_nbij φ hmaps hinj hsurj (fun a _ => rfl)).symm]
  refine sum_congr rfl fun a ha => ?_
  rw [hcot a ha, hsig a ha]

lemma Cp_one_eq (p : ℕ) :
    Cp p 1 = ∑ n ∈ (range p).filter Odd, Real.cot (Real.pi * n / (2 * p)) := by
  unfold Cp; simp only [Nat.cast_one, mul_one]

/-- `|C_p(k)| ≤ C_p(1)` for odd `k` with `p ∤ k` (end of Lemma 3.2). -/
theorem Cp_abs_le {p k : ℕ} (hp : p.Prime) (hk : Odd k) (hpk : ¬ p ∣ k) :
    |Cp p k| ≤ Cp p 1 := by
  have hcop : Nat.Coprime k (2 * p) := by
    refine (Nat.coprime_mul_iff_left.2 ⟨Nat.coprime_two_left.2 hk, ?_⟩).symm
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hpk
  obtain ⟨kbar, -, hkbar⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by have := hp.two_le; omega)
  have hkbar' : k * kbar ≡ 1 [MOD 2 * p] := by
    unfold Nat.ModEq; rw [hkbar, Nat.mod_eq_of_lt (by have := hp.two_le; omega)]
  rw [Cp_sign_form hp hk hpk hkbar', Cp_one_eq]
  refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun n hn => ?_))
  simp only [mem_filter, mem_range] at hn
  rw [abs_mul, abs_of_pos (cot_pos_of_lt hn.2.pos hn.1)]
  have : |(sigma p (n * kbar) : ℝ)| = 1 := by unfold sigma; push_cast; simp
  rw [this, one_mul]

lemma odd_harmonic_le (h : ℕ) (hh : 1 ≤ h) :
    ∑ x ∈ range h, 1 / (2 * (x : ℝ) + 1) ≤ 1 + Real.log (2 * h - 1) / 2 := by
  induction h, hh using Nat.le_induction with
  | base => norm_num
  | succ h hh ih =>
    rw [sum_range_succ]
    have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
    have hpos : (0 : ℝ) < 2 * h - 1 := by linarith
    have key := Real.one_sub_inv_le_log_of_pos (x := (2 * h + 1) / (2 * h - 1)) (by positivity)
    rw [inv_div, Real.log_div (by positivity) hpos.ne'] at key
    have e : 1 / (2 * (h : ℝ) + 1) = (1 - (2 * h - 1) / (2 * h + 1)) / 2 := by
      field_simp; ring
    push_cast
    rw [show 2 * ((h : ℝ) + 1) - 1 = 2 * h + 1 by ring, e]
    linarith

/-- `cot y ≤ 1/y` on `(0, π/2)`. -/
lemma cot_le_inv {y : ℝ} (h0 : 0 < y) (h1 : y < Real.pi / 2) : Real.cot y ≤ 1 / y := by
  rw [← Real.tan_inv_eq_cot, one_div]
  exact inv_anti₀ h0 (Real.lt_tan h0 h1).le

/-- **Lemma 3.3**: `C_m(1) ≤ (m/π)(log m + 2)` for odd `m` (in particular for odd `m ≥ 3`). -/
theorem Cp_one_le {m : ℕ} (hm : Odd m) :
    Cp m 1 ≤ m / Real.pi * (Real.log m + 2) := by
  obtain ⟨h, rfl⟩ := hm
  have hmR : (0 : ℝ) < ((2 * h + 1 : ℕ) : ℝ) := by positivity
  have hlog : 0 ≤ Real.log ((2 * h + 1 : ℕ) : ℝ) := Real.log_nonneg (by push_cast; linarith [(h.cast_nonneg : (0:ℝ) ≤ h)])
  rw [Cp_one_eq, sum_odd_range]
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · simp only [range_zero, sum_empty]; positivity
  have hterm : ∀ x ∈ range h, Real.cot (Real.pi * ((2 * x + 1 : ℕ) : ℝ) / (2 * ((2 * h + 1 : ℕ) : ℝ))) ≤
      2 * ((2 * h + 1 : ℕ) : ℝ) / Real.pi * (1 / (2 * (x : ℝ) + 1)) := by
    intro x hx
    simp only [mem_range] at hx
    have hxR : (x : ℝ) < h := by exact_mod_cast hx
    refine (cot_le_inv (by positivity) ?_).trans (le_of_eq ?_)
    · push_cast
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [Real.pi_pos]
    · push_cast; field_simp
  calc _ ≤ ∑ x ∈ range h, 2 * ((2 * h + 1 : ℕ) : ℝ) / Real.pi * (1 / (2 * (x : ℝ) + 1)) :=
        sum_le_sum hterm
    _ = 2 * ((2 * h + 1 : ℕ) : ℝ) / Real.pi * ∑ x ∈ range h, 1 / (2 * (x : ℝ) + 1) := by
        rw [mul_sum]
    _ ≤ 2 * ((2 * h + 1 : ℕ) : ℝ) / Real.pi * (1 + Real.log ((2 * h + 1 : ℕ) : ℝ) / 2) := by
        gcongr
        refine (odd_harmonic_le h hh).trans ?_
        have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
        gcongr
        · linarith
        · push_cast; linarith
    _ = _ := by field_simp; ring

lemma Cp_one_nonneg (p : ℕ) : 0 ≤ Cp p 1 := by
  rw [Cp_one_eq]
  refine sum_nonneg fun n hn => ?_
  simp only [mem_filter, mem_range] at hn
  exact (cot_pos_of_lt hn.2.pos hn.1).le

/-- **Theorem A** (with the elementary constant `2` of Lemma 3.3 in place of `K₀`):
for every odd prime `p`, `|S(p)| ≤ (2/p) C_p(1)² ≤ (2/π²) p (log p + 2)²`. -/
theorem theorem_A {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    |(S p : ℝ)| ≤ 2 / p * Cp p 1 ^ 2 ∧
      2 / p * Cp p 1 ^ 2 ≤ 2 / Real.pi ^ 2 * p * (Real.log p + 2) ^ 2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  constructor
  · rw [S_dual hp hp2, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / p), sq]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc _ ≤ ∑ k ∈ (range p).filter Odd, |Real.cot (Real.pi * k / (2 * p)) * Cp p k| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ (range p).filter Odd, Real.cot (Real.pi * k / (2 * p)) * Cp p 1 := by
          refine sum_le_sum fun k hk => ?_
          simp only [mem_filter, mem_range] at hk
          have hc := cot_pos_of_lt hk.2.pos hk.1
          rw [abs_mul, abs_of_pos hc]
          gcongr
          refine Cp_abs_le hp hk.2 ?_
          intro hd; exact absurd (Nat.le_of_dvd hk.2.pos hd) (by omega)
      _ = Cp p 1 * Cp p 1 := by rw [← sum_mul, ← Cp_one_eq]
  · have h1 := Cp_one_le (hp.odd_of_ne_two hp2)
    have h0 := Cp_one_nonneg p
    have h2 : Cp p 1 ^ 2 ≤ (p / Real.pi * (Real.log p + 2)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    calc 2 / p * Cp p 1 ^ 2 ≤ 2 / p * (p / Real.pi * (Real.log p + 2)) ^ 2 := by gcongr
      _ = _ := by field_simp

/-- Theorem A, combined form. -/
theorem S_abs_le_cot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    |(S p : ℝ)| ≤ 2 / Real.pi ^ 2 * p * (Real.log p + 2) ^ 2 :=
  (theorem_A hp hp2).1.trans (theorem_A hp hp2).2

#print axioms S_eq_sum_T
#print axioms T_dual
#print axioms S_dual
#print axioms Cp_sign_form
#print axioms Cp_abs_le
#print axioms Cp_one_le
#print axioms theorem_A
#print axioms S_abs_le_cot

end Arxiv.«2501.03234»
