import Upper.Cot

/-!
# Elementary lemmas on the tangent sums `F_k(n)` and `G_d(n)` (`theta_sum_v3.pdf`, §4 and §9)

* `Cp_eq_Fsum`, `Fsum_one_eq_Cp` — Lemma 4.4 (first part) and Corollary 4.3(a) (elementary part),
* `Fsum_abs_le` — Corollary 4.3(b) (elementary part): `|F_k(r)| ≤ F_k(1)`,
* `Fsum_eq_sum_Gsum` — Lemma 9.1,
* `tan_sum_shift` — `Σ_{i<m} tan(x + iπ/m) = m tan(mx)` for odd `m`,
* `Gsum_avg` — Lemma 9.2(a).
-/
namespace Arxiv.«2501.03234»
open Finset

/-- `F_k(n) = Σ_{t=1}^{(k-1)/2} tan(π n t / k)`. -/
noncomputable def Fsum (k : ℕ) (n : ℤ) : ℝ :=
  ∑ t ∈ Icc 1 ((k - 1) / 2), Real.tan (Real.pi * n * t / k)

lemma sum_Icc_one (h : ℕ) (f : ℕ → ℝ) : ∑ t ∈ Icc 1 h, f t = ∑ x ∈ range h, f (x + 1) := by
  induction h with
  | zero => simp
  | succ h ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

lemma cot_pi_div_two_sub (x : ℝ) : Real.cot (Real.pi / 2 - x) = Real.tan x := by
  rw [Real.cot_eq_cos_div_sin, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub,
    Real.tan_eq_sin_div_cos]

/-- **Lemma 4.4** (first part, elementary): `C_m(k) = F_m(k)` for odd `m` and odd `k`
(coprimality is not needed). -/
theorem Cp_eq_Fsum {m k : ℕ} (hm : Odd m) (hk : Odd k) : Cp m k = Fsum m k := by
  obtain ⟨h, rfl⟩ := hm
  obtain ⟨c, rfl⟩ := hk
  unfold Cp Fsum
  rw [sum_odd_range, show (2 * h + 1 - 1) / 2 = h by omega, sum_Icc_one, ← sum_range_reflect]
  refine sum_congr rfl fun x hx => ?_
  simp only [mem_range] at hx
  obtain ⟨y, rfl⟩ : ∃ y, h = x + 1 + y := ⟨h - 1 - x, by omega⟩
  rw [show x + 1 + y - 1 - x = y by omega]
  have e : Real.pi * ((2 * c + 1 : ℕ) : ℝ) * ((2 * y + 1 : ℕ) : ℝ) /
      (2 * ((2 * (x + 1 + y) + 1 : ℕ) : ℝ)) = (c : ℝ) * Real.pi + (Real.pi / 2 -
        Real.pi * (((2 * c + 1 : ℕ) : ℤ) : ℝ) * ((x + 1 : ℕ) : ℝ) / ((2 * (x + 1 + y) + 1 : ℕ) : ℝ)) := by
    push_cast
    field_simp
    ring
  rw [e, add_comm, cot_add_nat_mul_pi, cot_pi_div_two_sub]

/-- **Corollary 4.3(a)** (elementary part): `F_m(1) = C_m(1)` for odd `m`. -/
theorem Fsum_one_eq_Cp {m : ℕ} (hm : Odd m) : Fsum m 1 = Cp m 1 := by
  rw [Cp_eq_Fsum hm odd_one]; rfl

lemma tan_pos_of_two_mul_lt {k t : ℕ} (ht : 1 ≤ t) (hk : 2 * t < k) :
    0 < Real.tan (Real.pi * t / k) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hkt : 2 * (t : ℝ) < k := by exact_mod_cast hk
  apply Real.tan_pos_of_pos_of_lt_pi_div_two (by positivity)
  rw [div_lt_div_iff₀ hkR (by norm_num)]
  nlinarith [Real.pi_pos]

lemma Fsum_one_eq (k : ℕ) : Fsum k 1 = ∑ t ∈ Icc 1 ((k - 1) / 2), Real.tan (Real.pi * t / k) := by
  unfold Fsum; simp only [Int.cast_one, mul_one]

lemma Fsum_one_nonneg {k : ℕ} (hk : Odd k) : 0 ≤ Fsum k 1 := by
  rw [Fsum_one_eq]
  refine sum_nonneg fun t ht => ?_
  simp only [mem_Icc] at ht
  obtain ⟨h, rfl⟩ := hk
  exact (tan_pos_of_two_mul_lt ht.1 (by omega)).le

/-- `F_k(r)` only depends on `r mod k`. -/
lemma Fsum_emod {k : ℕ} (hk : 0 < k) (r : ℤ) : Fsum k r = Fsum k (r % k) := by
  unfold Fsum
  refine sum_congr rfl fun t _ => ?_
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have e : (r : ℝ) = (r % k : ℤ) + k * (r / k : ℤ) := by
    have := Int.mul_ediv_add_emod r k
    exact_mod_cast (by linarith : r = r % k + k * (r / k))
  rw [e, show Real.pi * (((r % k : ℤ) : ℝ) + k * ((r / k : ℤ) : ℝ)) * t / k =
    Real.pi * ((r % k : ℤ) : ℝ) * t / k + ((r / k * t : ℤ) : ℝ) * Real.pi by push_cast; field_simp,
    Real.tan_add_int_mul_pi]

/-- Coprime case of Corollary 4.3(b). -/
lemma Fsum_abs_le_coprime {k r : ℕ} (hk : Odd k) (hcop : Nat.Coprime r k) :
    |Fsum k r| ≤ Fsum k 1 := by
  obtain ⟨h, hh⟩ := hk
  have hk0 : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hhk : (k - 1) / 2 = h := by omega
  let φ : ℕ → ℕ := fun t => if r * t % k ≤ h then r * t % k else k - r * t % k
  have hu0 : ∀ t ∈ Icc 1 h, r * t % k ≠ 0 := by
    intro t ht h0
    simp only [mem_Icc] at ht
    have : k ∣ t := (Nat.Coprime.dvd_of_dvd_mul_left hcop.symm (Nat.dvd_of_mod_eq_zero h0))
    exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  have hlt : ∀ t, r * t % k < k := fun t => Nat.mod_lt _ hk0
  have hmaps : ∀ t ∈ Icc 1 h, φ t ∈ Icc 1 h := by
    intro t ht
    have := hu0 t ht; have := hlt t
    simp only [mem_Icc, φ]
    split_ifs <;> omega
  have habs : ∀ t ∈ Icc 1 h, |Real.tan (Real.pi * ((r : ℤ) : ℝ) * t / k)| =
      Real.tan (Real.pi * (φ t) / k) := by
    intro t ht
    have := hu0 t ht; have := hlt t
    have hdiv : ((r : ℝ) * t) = k * ((r * t / k : ℕ) : ℝ) + ((r * t % k : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod (r * t) k).symm
    rw [Int.cast_natCast, mul_assoc, hdiv, show Real.pi * (k * ((r * t / k : ℕ) : ℝ) +
      ((r * t % k : ℕ) : ℝ)) / k = Real.pi * ((r * t % k : ℕ) : ℝ) / k +
        ((r * t / k : ℕ) : ℝ) * Real.pi by field_simp; ring, Real.tan_add_nat_mul_pi]
    simp only [φ]
    split_ifs with h1
    · exact abs_of_pos (tan_pos_of_two_mul_lt (by omega) (by omega))
    · rw [show Real.pi * ((r * t % k : ℕ) : ℝ) / k =
          ((1 : ℕ) : ℝ) * Real.pi - Real.pi * ((k - r * t % k : ℕ) : ℝ) / k by
        rw [Nat.cast_sub (hlt t).le]; field_simp; ring, Real.tan_nat_mul_pi_sub, abs_neg]
      exact abs_of_pos (tan_pos_of_two_mul_lt (by omega) (by omega))
  have hinj : Set.InjOn φ (Icc 1 h : Set ℕ) := by
    intro a ha b hb hab
    simp only [coe_Icc, Set.mem_Icc] at ha hb
    have ha0 := hu0 a (by simpa using ha); have hb0 := hu0 b (by simpa using hb)
    have := hlt a; have := hlt b
    have hgcd : Nat.gcd k r = 1 := hcop.symm
    have same : r * a % k = r * b % k → a = b := by
      intro he
      have := Nat.ModEq.cancel_left_of_coprime hgcd he
      unfold Nat.ModEq at this
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    have opp : r * a % k + r * b % k = k → False := by
      intro he
      have h1 : r * (a + b) ≡ r * 0 [MOD k] := by
        unfold Nat.ModEq
        rw [mul_add, Nat.add_mod, he, mul_zero, Nat.zero_mod, Nat.mod_self]
      have := Nat.ModEq.cancel_left_of_coprime hgcd h1
      unfold Nat.ModEq at this
      rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega)] at this
      omega
    simp only [φ] at hab
    split_ifs at hab with h1 h2 h2
    · exact same hab
    · exact (opp (by omega)).elim
    · exact (opp (by omega)).elim
    · exact same (by omega)
  rw [Fsum_one_eq, hhk]
  unfold Fsum
  rw [hhk]
  calc _ ≤ ∑ t ∈ Icc 1 h, |Real.tan (Real.pi * ((r : ℤ) : ℝ) * t / k)| := abs_sum_le_sum_abs _ _
    _ = ∑ t ∈ Icc 1 h, Real.tan (Real.pi * (φ t) / k) := sum_congr rfl habs
    _ = ∑ x ∈ (Icc 1 h).image φ, Real.tan (Real.pi * x / k) := (sum_image (f := fun x : ℕ => Real.tan (Real.pi * x / k)) hinj).symm
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro x hx
        simp only [mem_image] at hx
        obtain ⟨t, ht, rfl⟩ := hx
        exact hmaps t ht
      · intro x hx _
        simp only [mem_Icc] at hx
        exact (tan_pos_of_two_mul_lt hx.1 (by omega)).le

lemma sum_rot (φ : ℕ → ℝ) (L : ℕ) (hper : ∀ t, φ (t + L) = φ t) (c : ℕ) :
    ∑ x ∈ range L, φ (c + x) = ∑ x ∈ range L, φ x := by
  induction c with
  | zero => simp
  | succ c ih =>
    have h1 := sum_range_succ (fun x => φ (c + x)) L
    have h2 := sum_range_succ' (fun x => φ (c + x)) L
    simp only [add_zero] at h1 h2
    rw [hper] at h1
    have : ∑ x ∈ range L, φ (c + 1 + x) = ∑ x ∈ range L, φ (c + (x + 1)) :=
      sum_congr rfl fun x _ => by rw [add_assoc, add_comm 1 x]
    rw [this, ← ih]
    linarith

lemma sum_blocks (φ : ℕ → ℝ) (L : ℕ) (hper : ∀ t, φ (t + L) = φ t)
    (hzero : ∑ x ∈ range L, φ x = 0) (c j : ℕ) : ∑ x ∈ range (L * j), φ (c + x) = 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [mul_add, mul_one, sum_range_add, ih, zero_add]
    have := sum_rot φ L hper (c + L * j)
    simp only [add_assoc] at this
    rw [this, hzero]

lemma tan_sum_period_zero (k r : ℕ) (hk : 0 < k) :
    ∑ x ∈ range k, Real.tan (Real.pi * r * x / k) = 0 := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  set ψ : ℕ → ℝ := fun x => Real.tan (Real.pi * r * x / k) with hψ
  have hper : ∀ t, ψ (t + k) = ψ t := by
    intro t; simp only [hψ]; push_cast
    rw [show Real.pi * r * (t + k) / k = Real.pi * r * t / k + (r : ℝ) * Real.pi by field_simp,
      Real.tan_add_nat_mul_pi]
  have h1 := sum_rot ψ k hper 1
  have h2 : ∑ x ∈ range k, ψ (1 + x) = - ∑ x ∈ range k, ψ x := by
    rw [← sum_range_reflect, ← sum_neg_distrib]
    refine sum_congr rfl fun x hx => ?_
    simp only [mem_range] at hx
    simp only [hψ]
    rw [show 1 + (k - 1 - x) = k - x by omega, Nat.cast_sub hx.le,
      show Real.pi * r * ((k : ℝ) - x) / k = (r : ℝ) * Real.pi - Real.pi * r * x / k by
        field_simp, Real.tan_nat_mul_pi_sub]
  change ∑ x ∈ range k, ψ x = 0
  linarith

/-- Reduction `F_{gk'}(g r') = F_{k'}(r')` for odd `g`, `k'`. -/
lemma Fsum_reduce {g k' r' : ℕ} (hg : Odd g) (hk' : Odd k') :
    Fsum (g * k') ((g * r' : ℕ) : ℤ) = Fsum k' (r' : ℤ) := by
  obtain ⟨a, rfl⟩ := hg
  obtain ⟨b, rfl⟩ := hk'
  have hgR : ((2 * a + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hkR : ((2 * b + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hdiv : ((2 * a + 1) * (2 * b + 1) - 1) / 2 = b + (2 * b + 1) * a := by
    rw [show (2 * a + 1) * (2 * b + 1) = 2 * (b + (2 * b + 1) * a) + 1 by ring]
    omega
  unfold Fsum
  rw [hdiv, show (2 * b + 1 - 1) / 2 = b by omega, sum_Icc_one, sum_Icc_one, sum_range_add]
  set ψ : ℕ → ℝ := fun y => Real.tan (Real.pi * r' * (y : ℝ) / ((2 * b + 1 : ℕ) : ℝ)) with hψ
  have e : ∀ y : ℕ, Real.tan (Real.pi * ((((2 * a + 1) * r' : ℕ) : ℤ) : ℝ) * (y : ℝ) /
      (((2 * a + 1) * (2 * b + 1) : ℕ) : ℝ)) = ψ y := by
    intro y; simp only [hψ]; congr 1; push_cast; field_simp
  have hper : ∀ t, ψ (t + (2 * b + 1)) = ψ t := by
    intro t
    simp only [hψ]
    push_cast
    rw [show Real.pi * r' * ((t : ℝ) + (2 * b + 1)) / (2 * b + 1) =
      Real.pi * r' * t / (2 * b + 1) + (r' : ℝ) * Real.pi by field_simp, Real.tan_add_nat_mul_pi]
  have hz := sum_blocks ψ (2 * b + 1) hper (tan_sum_period_zero _ _ (by omega)) (b + 1) a
  calc _ = ∑ x ∈ range b, ψ (x + 1) + ∑ x ∈ range ((2 * b + 1) * a), ψ (b + 1 + x) := by
        congr 1
        · exact sum_congr rfl fun x _ => e _
        · refine sum_congr rfl fun x _ => ?_
          rw [e]; congr 1; ring
    _ = ∑ x ∈ range b, ψ (x + 1) := by rw [hz, add_zero]
    _ = _ := by
        refine sum_congr rfl fun x _ => ?_
        simp only [hψ, Int.cast_natCast]

/-- `F_{k'}(1) ≤ F_{g k'}(1)` for odd `g`, `k'`. -/
lemma Fsum_one_mono {g k' : ℕ} (hg : Odd g) (hk' : Odd k') : Fsum k' 1 ≤ Fsum (g * k') 1 := by
  obtain ⟨a, rfl⟩ := hg
  obtain ⟨b, rfl⟩ := hk'
  have hgR : ((2 * a + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hdiv : ((2 * a + 1) * (2 * b + 1) - 1) / 2 = b + (2 * b + 1) * a := by
    rw [show (2 * a + 1) * (2 * b + 1) = 2 * (b + (2 * b + 1) * a) + 1 by ring]
    omega
  rw [Fsum_one_eq, Fsum_one_eq, hdiv, show (2 * b + 1 - 1) / 2 = b by omega]
  have hinj : Set.InjOn (fun s => (2 * a + 1) * s) (Icc 1 b : Set ℕ) := by
    intro x _ y _ hxy
    simp only at hxy
    exact Nat.eq_of_mul_eq_mul_left (by omega) hxy
  calc ∑ t ∈ Icc 1 b, Real.tan (Real.pi * t / ((2 * b + 1 : ℕ) : ℝ))
      = ∑ t ∈ Icc 1 b, Real.tan (Real.pi * (((2 * a + 1) * t : ℕ) : ℝ) /
          (((2 * a + 1) * (2 * b + 1) : ℕ) : ℝ)) := by
        refine sum_congr rfl fun t _ => ?_
        congr 1; push_cast; field_simp
    _ = ∑ t ∈ (Icc 1 b).image (fun s => (2 * a + 1) * s),
          Real.tan (Real.pi * t / (((2 * a + 1) * (2 * b + 1) : ℕ) : ℝ)) :=
        (sum_image (f := fun t : ℕ => Real.tan (Real.pi * t /
          (((2 * a + 1) * (2 * b + 1) : ℕ) : ℝ))) hinj).symm
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro x hx
        simp only [mem_image, mem_Icc] at hx ⊢
        obtain ⟨t, ht, rfl⟩ := hx
        constructor
        · nlinarith
        · nlinarith
      · intro x hx _
        simp only [mem_Icc] at hx
        refine (tan_pos_of_two_mul_lt hx.1 ?_).le
        have : (2 * a + 1) * (2 * b + 1) = 2 * (b + (2 * b + 1) * a) + 1 := by ring
        omega

/-- **Corollary 4.3(b)** (elementary part): `|F_k(r)| ≤ F_k(1)` for odd `k` and every integer `r`. -/
theorem Fsum_abs_le {k : ℕ} (hk : Odd k) (r : ℤ) : |Fsum k r| ≤ Fsum k 1 := by
  have hk0 : 0 < k := hk.pos
  have hkZ : (k : ℤ) ≠ 0 := by exact_mod_cast hk0.ne'
  set r0 : ℕ := (r % k).toNat with hr0
  have hr0' : ((r0 : ℕ) : ℤ) = r % k := Int.toNat_of_nonneg (Int.emod_nonneg r hkZ)
  rw [Fsum_emod hk0, ← hr0']
  set g := Nat.gcd r0 k with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ hk0
  have hkg : k = g * (k / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right r0 k)).symm
  have hrg : r0 = g * (r0 / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left r0 k)).symm
  have hcop : Nat.Coprime (r0 / g) (k / g) := Nat.coprime_div_gcd_div_gcd hg0
  have hodd : Odd g ∧ Odd (k / g) := by
    rw [← Nat.odd_mul, ← hkg]; exact hk
  rw [hrg, hkg, Fsum_reduce hodd.1 hodd.2]
  exact (Fsum_abs_le_coprime hodd.2 hcop).trans (Fsum_one_mono hodd.1 hodd.2)

/-- Index set `{1 ≤ j < d/2, (j,d) = 1}`. -/
def Jset (d : ℕ) : Finset ℕ := (range d).filter (fun j => 1 ≤ j ∧ 2 * j < d ∧ Nat.Coprime j d)

/-- `G_d(n) = Σ_{1≤j<d/2, (j,d)=1} tan(π j n / d)`. -/
noncomputable def Gsum (d : ℕ) (n : ℤ) : ℝ := ∑ j ∈ Jset d, Real.tan (Real.pi * n * j / d)

/-- `|G_d(n)| ≤ G_d(1)` for odd `d` and `n` coprime to `d` (companion paper, Lemma "Gmax",
Sharp tails). Same folding argument as `Fsum_abs_le_coprime`. -/
theorem Gsum_abs_le {d n : ℕ} (hd : Odd d) (hcop : Nat.Coprime n d) :
    |Gsum d n| ≤ Gsum d 1 := by
  obtain ⟨h, hh⟩ := hd
  have hk0 : 0 < d := by omega
  have hkR : (0 : ℝ) < d := by exact_mod_cast hk0
  have hJ : ∀ t, t ∈ Jset d ↔ 1 ≤ t ∧ t ≤ h ∧ Nat.Coprime t d := by
    intro t
    simp only [Jset, mem_filter, mem_range]
    constructor
    · rintro ⟨_, h1, h2, h3⟩; exact ⟨h1, by omega, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h1, by omega, h3⟩
  let φ : ℕ → ℕ := fun t => if n * t % d ≤ h then n * t % d else d - n * t % d
  have hu0 : ∀ t ∈ Jset d, n * t % d ≠ 0 := by
    intro t ht h0
    rw [hJ] at ht
    have : d ∣ t := (Nat.Coprime.dvd_of_dvd_mul_left hcop.symm (Nat.dvd_of_mod_eq_zero h0))
    exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  have hlt : ∀ t, n * t % d < d := fun t => Nat.mod_lt _ hk0
  have hmaps : ∀ t ∈ Jset d, φ t ∈ Jset d := by
    intro t ht
    have := hu0 t ht; have := hlt t
    have hc : Nat.Coprime (n * t % d) d := by
      unfold Nat.Coprime
      rw [← Nat.gcd_rec]
      exact Nat.Coprime.mul_right hcop.symm ((hJ t).1 ht).2.2.symm
    rw [hJ]
    simp only [φ]
    split_ifs
    · exact ⟨by omega, by omega, hc⟩
    · exact ⟨by omega, by omega, (Nat.coprime_self_sub_left (hlt t).le).2 hc⟩
  have habs : ∀ t ∈ Jset d, |Real.tan (Real.pi * ((n : ℤ) : ℝ) * t / d)| =
      Real.tan (Real.pi * (φ t) / d) := by
    intro t ht
    have := hu0 t ht; have := hlt t
    have hdiv : ((n : ℝ) * t) = d * ((n * t / d : ℕ) : ℝ) + ((n * t % d : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod (n * t) d).symm
    rw [Int.cast_natCast, mul_assoc, hdiv, show Real.pi * (d * ((n * t / d : ℕ) : ℝ) +
      ((n * t % d : ℕ) : ℝ)) / d = Real.pi * ((n * t % d : ℕ) : ℝ) / d +
        ((n * t / d : ℕ) : ℝ) * Real.pi by field_simp; ring, Real.tan_add_nat_mul_pi]
    simp only [φ]
    split_ifs with h1
    · exact abs_of_pos (tan_pos_of_two_mul_lt (by omega) (by omega))
    · rw [show Real.pi * ((n * t % d : ℕ) : ℝ) / d =
          ((1 : ℕ) : ℝ) * Real.pi - Real.pi * ((d - n * t % d : ℕ) : ℝ) / d by
        rw [Nat.cast_sub (hlt t).le]; field_simp; ring, Real.tan_nat_mul_pi_sub, abs_neg]
      exact abs_of_pos (tan_pos_of_two_mul_lt (by omega) (by omega))
  have hinj : Set.InjOn φ (Jset d : Set ℕ) := by
    intro a ha b hb hab
    have ha' := (hJ a).1 ha; have hb' := (hJ b).1 hb
    have ha0 := hu0 a ha; have hb0 := hu0 b hb
    have := hlt a; have := hlt b
    have hgcd : Nat.gcd d n = 1 := hcop.symm
    have same : n * a % d = n * b % d → a = b := by
      intro he
      have := Nat.ModEq.cancel_left_of_coprime hgcd he
      unfold Nat.ModEq at this
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    have opp : n * a % d + n * b % d = d → False := by
      intro he
      have h1 : n * (a + b) ≡ n * 0 [MOD d] := by
        unfold Nat.ModEq
        rw [mul_add, Nat.add_mod, he, mul_zero, Nat.zero_mod, Nat.mod_self]
      have := Nat.ModEq.cancel_left_of_coprime hgcd h1
      unfold Nat.ModEq at this
      rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega)] at this
      omega
    simp only [φ] at hab
    split_ifs at hab with h1 h2 h2
    · exact same hab
    · exact (opp (by omega)).elim
    · exact (opp (by omega)).elim
    · exact same (by omega)
  have hG1 : Gsum d 1 = ∑ j ∈ Jset d, Real.tan (Real.pi * j / d) := by
    unfold Gsum; simp only [Int.cast_one, mul_one]
  rw [hG1]
  unfold Gsum
  calc _ ≤ ∑ t ∈ Jset d, |Real.tan (Real.pi * ((n : ℤ) : ℝ) * t / d)| := abs_sum_le_sum_abs _ _
    _ = ∑ t ∈ Jset d, Real.tan (Real.pi * (φ t) / d) := sum_congr rfl habs
    _ = ∑ x ∈ (Jset d).image φ, Real.tan (Real.pi * x / d) :=
        (sum_image (f := fun x : ℕ => Real.tan (Real.pi * x / d)) hinj).symm
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro x hx
        simp only [mem_image] at hx
        obtain ⟨t, ht, rfl⟩ := hx
        exact hmaps t ht
      · intro x hx _
        have hx' := (hJ x).1 hx
        exact (tan_pos_of_two_mul_lt hx'.1 (by omega)).le

/-- **Lemma 9.1**: `F_k(n) = Σ_{d | k, d ≥ 3} G_d(n)` for odd `k`. -/
theorem Fsum_eq_sum_Gsum {k : ℕ} (hk : Odd k) (n : ℤ) :
    Fsum k n = ∑ d ∈ k.divisors.filter (fun d => 3 ≤ d), Gsum d n := by
  have hk0 : 0 < k := hk.pos
  unfold Gsum
  rw [sum_sigma']
  unfold Fsum
  symm
  refine sum_nbij' (fun x => x.2 * (k / x.1)) (fun t => ⟨k / Nat.gcd t k, t / Nat.gcd t k⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨d, j⟩ hx
    simp only [mem_sigma, Nat.mem_divisors, Jset, mem_filter, mem_range] at hx
    obtain ⟨⟨⟨hdk, -⟩, hd3⟩, hj, hj1, hj2, -⟩ := hx
    obtain ⟨e, rfl⟩ := hdk
    have he : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; simp at hk0)
    simp only [mem_Icc]
    rw [Nat.mul_div_cancel_left _ (by omega)]
    have : 2 * (j * e) < d * e := by rw [← mul_assoc]; exact Nat.mul_lt_mul_of_pos_right hj2 he
    constructor
    · exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) he.ne')
    · omega
  · intro t ht
    simp only [mem_Icc] at ht
    have hg0 : 0 < Nat.gcd t k := Nat.gcd_pos_of_pos_right _ hk0
    have hgt := Nat.gcd_dvd_left t k
    have hgk := Nat.gcd_dvd_right t k
    have hkg : k = Nat.gcd t k * (k / Nat.gcd t k) := (Nat.mul_div_cancel' hgk).symm
    have htg : t = Nat.gcd t k * (t / Nat.gcd t k) := (Nat.mul_div_cancel' hgt).symm
    have hdodd : Odd (k / Nat.gcd t k) := (Nat.odd_mul.1 (hkg ▸ hk)).2
    have h2 : 2 * (t / Nat.gcd t k) < k / Nat.gcd t k := by
      apply Nat.lt_of_mul_lt_mul_left (a := Nat.gcd t k)
      rw [← hkg, mul_left_comm, ← htg]; omega
    have hd1 : k / Nat.gcd t k ≠ 1 := by
      intro h1
      rw [h1, mul_one] at hkg
      have : k ∣ t := hkg ▸ hgt
      exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
    have hj1 : 1 ≤ t / Nat.gcd t k := Nat.div_pos (Nat.le_of_dvd (by omega) hgt) hg0
    simp only [mem_sigma, Nat.mem_divisors, Jset, mem_filter, mem_range]
    refine ⟨⟨⟨Nat.div_dvd_of_dvd hgk, hk0.ne'⟩, ?_⟩, by omega, hj1, h2,
      Nat.coprime_div_gcd_div_gcd hg0⟩
    obtain ⟨c, hc⟩ := hdodd
    omega
  · rintro ⟨d, j⟩ hx
    simp only [mem_sigma, Nat.mem_divisors, Jset, mem_filter, mem_range] at hx
    obtain ⟨⟨⟨hdk, -⟩, hd3⟩, hj, hj1, hj2, hcop⟩ := hx
    obtain ⟨e, rfl⟩ := hdk
    have he : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; simp at hk0)
    simp only
    rw [Nat.mul_div_cancel_left _ (by omega)]
    have hg : Nat.gcd (j * e) (d * e) = e := by
      rw [Nat.gcd_mul_right, Nat.Coprime.gcd_eq_one hcop, one_mul]
    rw [hg, Nat.mul_div_cancel _ he, Nat.mul_div_cancel _ he]
  · intro t ht
    simp only
    have hgt := Nat.gcd_dvd_left t k
    have hgk := Nat.gcd_dvd_right t k
    rw [Nat.div_div_self hgk hk0.ne', Nat.div_mul_cancel hgt]
  · rintro ⟨d, j⟩ hx
    simp only [mem_sigma, mem_filter, Nat.mem_divisors] at hx
    obtain ⟨⟨⟨hdk, -⟩, hd3⟩, -⟩ := hx
    obtain ⟨e, rfl⟩ := hdk
    have he : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; simp at hk0)
    simp only
    rw [Nat.mul_div_cancel_left _ (by omega)]
    congr 1
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    have heR : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    push_cast
    field_simp

open Complex in
lemma tan_formula (t : ℝ) (hc : Real.cos t ≠ 0) :
    Complex.exp (2 * t * I) + 1 ≠ 0 ∧
      (Real.tan t : ℂ) = -I * ((Complex.exp (2 * t * I) - 1) / (Complex.exp (2 * t * I) + 1)) := by
  set c : ℝ := Real.cos t with hcd
  set s : ℝ := Real.sin t with hsd
  have e : Complex.exp (2 * t * I) = ((c : ℂ) + (s : ℂ) * I) ^ 2 := by
    rw [show (2 * t * I : ℂ) = ((2 : ℕ) : ℂ) * (t * I) by push_cast; ring, Complex.exp_nat_mul,
      Complex.exp_mul_I, hcd, hsd, Complex.ofReal_cos, Complex.ofReal_sin]
  have hcs : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by
    have := Real.cos_sq_add_sin_sq t
    exact_mod_cast this
  have e1 : ((c : ℂ) + (s : ℂ) * I) ^ 2 + 1 = 2 * c * ((c : ℂ) + (s : ℂ) * I) := by
    linear_combination (-1 : ℂ) * hcs + (s : ℂ) ^ 2 * I_sq
  have e2 : ((c : ℂ) + (s : ℂ) * I) ^ 2 - 1 = 2 * s * I * ((c : ℂ) + (s : ℂ) * I) := by
    linear_combination hcs - (s : ℂ) ^ 2 * I_sq
  have hu : ((c : ℂ) + (s : ℂ) * I) ≠ 0 := by
    intro h0
    have : (1 : ℂ) = 0 := by
      linear_combination -hcs + ((c : ℂ) - s * I) * h0 + (s : ℂ) ^ 2 * I_sq
    exact one_ne_zero this
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  rw [e, e1, e2]
  refine ⟨mul_ne_zero (mul_ne_zero two_ne_zero hc') hu, ?_⟩
  rw [mul_div_mul_right _ _ hu, Real.tan_eq_sin_div_cos, ← hcd, ← hsd]
  push_cast
  field_simp
  linear_combination (s : ℂ) * I_sq

/-- `Σ_{i<m} 1/(1 - y ω^i) = m/(1 - y^m)` for a primitive `m`-th root of unity `ω`. -/
lemma sum_inv_one_sub {m : ℕ} (hm : 0 < m) {ω y : ℂ} (hω : IsPrimitiveRoot ω m)
    (hy : ∀ i < m, 1 - y * ω ^ i ≠ 0) (hym : 1 - y ^ m ≠ 0) :
    ∑ i ∈ range m, 1 / (1 - y * ω ^ i) = m / (1 - y ^ m) := by
  have h1 : ∀ i ∈ range m, 1 / (1 - y * ω ^ i) =
      (∑ l ∈ range m, y ^ l * (ω ^ l) ^ i) / (1 - y ^ m) := by
    intro i hi
    simp only [mem_range] at hi
    rw [div_eq_div_iff (hy i hi) hym, one_mul]
    have := geom_sum_mul_neg (y * ω ^ i) m
    rw [mul_pow, ← pow_mul, mul_comm i m, pow_mul, hω.pow_eq_one, one_pow, mul_one] at this
    rw [← this]
    congr 1
    refine sum_congr rfl fun l _ => ?_
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm i l]
  rw [sum_congr rfl h1, ← sum_div, sum_comm]
  congr 1
  rw [sum_eq_single 0]
  · simp
  · intro l hl hl0
    simp only [mem_range] at hl
    rw [← mul_sum]
    have hne : ω ^ l ≠ 1 := by
      rw [Ne, hω.pow_eq_one_iff_dvd]
      intro hd; exact hl0 (Nat.eq_zero_of_dvd_of_lt hd hl)
    rw [geom_sum_eq hne, ← pow_mul, mul_comm l m, pow_mul, hω.pow_eq_one, one_pow, sub_self,
      zero_div, mul_zero]
  · intro h; simp at h; omega

/-- `Σ_{i<m} tan(x + iπ/m) = m tan(mx)` for odd `m`, away from the poles. -/
theorem tan_sum_shift {m : ℕ} (hm : Odd m) (x : ℝ)
    (hcos : ∀ i < m, Real.cos (x + i * Real.pi / m) ≠ 0) (hcosm : Real.cos (m * x) ≠ 0) :
    ∑ i ∈ range m, Real.tan (x + i * Real.pi / m) = m * Real.tan (m * x) := by
  have hm0 : 0 < m := hm.pos
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / m) with hωd
  have hω : IsPrimitiveRoot ω m := Complex.isPrimitiveRoot_exp m hm0.ne'
  set z : ℂ := Complex.exp (2 * x * Complex.I) with hz
  have hu : ∀ i : ℕ, Complex.exp (2 * ((x + i * Real.pi / m : ℝ) : ℂ) * Complex.I) = z * ω ^ i := by
    intro i
    rw [hz, hωd, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
  have hzm : Complex.exp (2 * ((m * x : ℝ) : ℂ) * Complex.I) = z ^ m := by
    rw [hz, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast]
  have hterm : ∀ i ∈ range m, (Real.tan (x + i * Real.pi / m) : ℂ) =
      -Complex.I * (1 - 2 * (1 / (1 - (-z) * ω ^ i))) := by
    intro i hi
    simp only [mem_range] at hi
    obtain ⟨hne, heq⟩ := tan_formula _ (hcos i hi)
    rw [hu] at hne heq
    rw [heq]
    congr 1
    rw [neg_mul, sub_neg_eq_add, add_comm 1]
    field_simp
    ring
  have hne : ∀ i < m, 1 - (-z) * ω ^ i ≠ 0 := by
    intro i hi
    have := (tan_formula _ (hcos i hi)).1
    rw [hu] at this
    rw [neg_mul, sub_neg_eq_add, add_comm]; exact this
  obtain ⟨hnem, heqm⟩ := tan_formula _ hcosm
  rw [hzm] at hnem heqm
  have hm' : 1 - (-z) ^ m ≠ 0 := by rw [hm.neg_pow, sub_neg_eq_add, add_comm]; exact hnem
  have hsum := sum_inv_one_sub hm0 hω hne hm'
  rw [sum_congr rfl hterm, ← mul_sum, sum_sub_distrib, ← mul_sum, hsum, hm.neg_pow, heqm]
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  rw [sub_neg_eq_add, add_comm 1 (z ^ m)]
  field_simp
  ring

lemma cos_pi_int_div_odd_ne {d : ℕ} (hd : Odd d) (N : ℤ) : Real.cos (Real.pi * N / d) ≠ 0 := by
  intro h
  rw [Real.cos_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.pos.ne'
  have h2 : (2 : ℝ) * N = (2 * k + 1) * d := by
    field_simp at hk
    nlinarith [Real.pi_pos]
  have hZ : 2 * N = (2 * k + 1) * (d : ℤ) := by exact_mod_cast h2
  have hodd : Odd ((2 * k + 1) * (d : ℤ)) := (odd_two_mul_add_one k).mul (by exact_mod_cast hd)
  rw [← hZ] at hodd
  exact (Int.not_even_iff_odd.2 hodd) ⟨N, by ring⟩

/-- **Lemma 9.2(a)**: for odd `d`, `g ∣ d`, `m = d/g` and `s ∈ ℤ`,
`(1/m) Σ_{i<m} G_d(s + g i) = Σ_{1≤j<d/2, (j,d)=1} tan(π j s / g)`. -/
theorem Gsum_avg {d g : ℕ} (hd : Odd d) (hg : g ∣ d) (s : ℤ) :
    1 / ((d / g : ℕ) : ℝ) * ∑ i ∈ range (d / g), Gsum d (s + g * i) =
      ∑ j ∈ Jset d, Real.tan (Real.pi * s * j / g) := by
  obtain ⟨m, rfl⟩ := hg
  have hodd := Nat.odd_mul.1 hd
  have hg0 : 0 < g := hodd.1.pos
  have hm0 : 0 < m := hodd.2.pos
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg0.ne'
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm0.ne'
  rw [Nat.mul_div_cancel_left _ hg0]
  unfold Gsum
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  simp only [Jset, mem_filter, mem_range] at hj
  have hjm : Nat.Coprime j m := Nat.Coprime.coprime_dvd_right (dvd_mul_left m g) hj.2.2.2
  set y : ℝ := Real.pi * s * j / ((g * m : ℕ) : ℝ) with hy
  have hterm : ∀ i ∈ range m, Real.tan (Real.pi * ((s + g * i : ℤ) : ℝ) * j / ((g * m : ℕ) : ℝ)) =
      Real.tan (y + ((i * j % m : ℕ) : ℝ) * Real.pi / m) := by
    intro i _
    have hdiv : ((i * j : ℕ) : ℝ) = ((i * j % m : ℕ) : ℝ) + m * ((i * j / m : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mod_add_div (i * j) m).symm
    rw [show Real.pi * ((s + g * i : ℤ) : ℝ) * j / ((g * m : ℕ) : ℝ) =
      y + ((i * j : ℕ) : ℝ) * Real.pi / m by rw [hy]; push_cast; field_simp,
      hdiv, show (((i * j % m : ℕ) : ℝ) + m * ((i * j / m : ℕ) : ℝ)) * Real.pi / m =
        ((i * j % m : ℕ) : ℝ) * Real.pi / m + ((i * j / m : ℕ) : ℝ) * Real.pi by field_simp,
      ← add_assoc, Real.tan_add_nat_mul_pi]
  rw [sum_congr rfl hterm]
  have hinj : Set.InjOn (fun i => i * j % m) (range m : Set ℕ) := by
    intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    have h1 : j * a ≡ j * b [MOD m] := by
      unfold Nat.ModEq; simpa [mul_comm] using hab
    have := Nat.ModEq.cancel_left_of_coprime (Nat.Coprime.symm hjm) h1
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  have hmaps : Set.MapsTo (fun i => i * j % m) (range m : Set ℕ) (range m : Set ℕ) := by
    intro a _
    simp only [coe_range, Set.mem_Iio]
    exact Nat.mod_lt _ hm0
  have hsurj := Finset.surjOn_of_injOn_of_card_le _ hmaps hinj le_rfl
  have hperm : ∑ x ∈ range m, Real.tan (y + ((x * j % m : ℕ) : ℝ) * Real.pi / m) =
      ∑ i ∈ range m, Real.tan (y + (i : ℝ) * Real.pi / m) :=
    sum_nbij (fun i : ℕ => (i * j % m : ℕ)) (fun a ha => hmaps ha) hinj hsurj (fun a _ => rfl)
  rw [hperm]
  rw [tan_sum_shift hodd.2 y]
  · rw [show (m : ℝ) * y = Real.pi * s * j / g by rw [hy]; push_cast; field_simp]
    field_simp
  · intro i _
    rw [show y + i * Real.pi / m = Real.pi * ((s * j + g * i : ℤ) : ℝ) / ((g * m : ℕ) : ℝ) by
      rw [hy]; push_cast; field_simp]
    exact cos_pi_int_div_odd_ne hd _
  · rw [show (m : ℝ) * y = Real.pi * ((s * j : ℤ) : ℝ) / g by rw [hy]; push_cast; field_simp]
    exact cos_pi_int_div_odd_ne hodd.1 _

#print axioms Cp_eq_Fsum
#print axioms Fsum_one_eq_Cp
#print axioms Fsum_abs_le
#print axioms Fsum_eq_sum_Gsum
#print axioms tan_sum_shift
#print axioms Gsum_avg
#print axioms Gsum_abs_le

end Arxiv.«2501.03234»
