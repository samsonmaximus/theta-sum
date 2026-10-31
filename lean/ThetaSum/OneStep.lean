import Mathlib

/-
Lemma 7.2 ("One step") of "An asymptotic formula for the theta-function sum S(p)" (v3),
the recursive step in the proof of Theorem D, together with
* the first assertion of Lemma 7.2 (each nonempty `A_s` is an admissible progression of
  length at most `2R/s`): `sub_progression`, `admissible_of_mem_S`;
* the fact (F1): `card_filter_dvd_le`;
* the Euler-product form of the Mertens constant `M(y)`: `sum_inv_smooth_le_euler_prod`.

Main theorem: `ThetaSum.one_step` (with a hypothesis `hM` standing for `M(y)`) and
`ThetaSum.one_step_euler` (with `M(y) = ∏_{ℓ ≤ y} (1 - 1/ℓ)⁻¹`).

The paper's sum over `j ≥ 0` is replaced by the sum over `j < J` for any `J` with
`X ≤ 2^J T'R`; since every divisor is at most `X`, the terms with `j ≥ J` are counted
in no class, and the finite sum is at most the paper's infinite one (all terms are `≥ 0`).
-/

open Finset

namespace ThetaSum

def smL (b d : ℕ) : List ℕ := d.primeFactorsList.filter (fun p => p ≤ b)
def rmL (b d : ℕ) : List ℕ := d.primeFactorsList.filter (fun p => ¬ p ≤ b)

lemma sm_mul_rm (b d : ℕ) (hd : d ≠ 0) : (smL b d).prod * (rmL b d).prod = d := by
  have h := Multiset.prod_filter_mul_prod_filter_not
    (s := (d.primeFactorsList : Multiset ℕ)) (fun p => p ≤ b)
  simp only [Multiset.filter_coe, Multiset.prod_coe] at h
  rw [Nat.prod_primeFactorsList hd] at h
  simpa [smL, rmL] using h

lemma rmL_sublist (b : ℕ) {d n : ℕ} (h : d ∣ n) (hn : n ≠ 0) : List.Sublist (rmL b d) (rmL b n) :=
  (Nat.primeFactorsList_sublist_of_dvd h hn).filter _

lemma prime_of_mem_smL {b d p : ℕ} (h : p ∈ smL b d) : p.Prime ∧ p ≤ b := by
  simp only [smL, List.mem_filter, decide_eq_true_eq] at h
  exact ⟨Nat.prime_of_mem_primeFactorsList h.1, h.2⟩

lemma prime_of_mem_rmL {b d p : ℕ} (h : p ∈ rmL b d) : p.Prime ∧ b < p := by
  simp only [rmL, List.mem_filter, decide_eq_true_eq, not_le] at h
  exact ⟨Nat.prime_of_mem_primeFactorsList h.1, h.2⟩

/-- `(b+1)^(number of b-rough prime factors) ≤ d`. -/
lemma pow_length_rmL_le (b d : ℕ) (hd : d ≠ 0) : (b + 1) ^ (rmL b d).length ≤ d := by
  have h1 : (b + 1) ^ (rmL b d).length ≤ (rmL b d).prod :=
    List.pow_length_le_prod _ _ (fun x hx => (prime_of_mem_rmL hx).2)
  have h2 : (rmL b d).prod ≤ d := by
    have := sm_mul_rm b d hd
    apply Nat.le_of_dvd (Nat.pos_of_ne_zero hd)
    exact ⟨(smL b d).prod, by rw [mul_comm]; exact this.symm⟩
  exact h1.trans h2


/-- `n` is `y`-smooth: every prime factor is at most `y`. -/
def IsSmooth (y : ℝ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, (p : ℝ) ≤ y

lemma length_rmL_le {y Z : ℝ} (hy : 2 ≤ y) {d : ℕ} (hd : d ≠ 0) (hdZ : (d : ℝ) ≤ Z) :
    (rmL ⌊y⌋₊ d).length ≤ ⌊Real.log Z / Real.log y⌋₊ := by
  set c := (rmL ⌊y⌋₊ d).length
  have hy0 : 0 < y := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have h1 : y ^ c ≤ (d : ℝ) := by
    have h := pow_length_rmL_le ⌊y⌋₊ d hd
    have h' : ((⌊y⌋₊ + 1 : ℕ) : ℝ) ^ c ≤ (d : ℝ) := by exact_mod_cast h
    refine le_trans ?_ h'
    apply pow_le_pow_left₀ hy0.le
    push_cast
    exact (Nat.lt_floor_add_one y).le
  have h2 : (c : ℝ) * Real.log y ≤ Real.log Z := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (h1.trans hdZ)
  apply Nat.le_floor
  rw [le_div_iff₀ hlogy]
  exact h2

lemma isSmooth_prod {y : ℝ} (l : List ℕ) (hl : ∀ x ∈ l, 0 < x ∧ (x : ℝ) ≤ y) :
    IsSmooth y l.prod := by
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ l.prod := Nat.dvd_of_mem_primeFactors hp
  obtain ⟨x, hx, hpx⟩ := (Prime.dvd_prod_iff hpp.prime).mp hpd
  have := Nat.le_of_dvd (hl x hx).1 hpx
  exact le_trans (by exact_mod_cast this) (hl x hx).2

lemma smL_bound {y : ℝ} (hy : 0 ≤ y) {d x : ℕ} (hx : x ∈ smL ⌊y⌋₊ d) : 0 < x ∧ (x : ℝ) ≤ y := by
  obtain ⟨hp, hle⟩ := prime_of_mem_smL hx
  exact ⟨hp.pos, (Nat.le_floor_iff hy).mp hle⟩

/-- First partial product exceeding `B`. -/
lemma prefix_exists (l : List ℕ) {y B : ℝ} (hB : 1 ≤ B) (hl : ∀ x ∈ l, 0 < x ∧ (x : ℝ) ≤ y)
    (h : B < (l.prod : ℝ)) :
    ∃ k, B < ((l.take k).prod : ℝ) ∧ ((l.take k).prod : ℝ) ≤ B * y := by
  classical
  have hex : ∃ k, B < ((l.take k).prod : ℝ) := ⟨l.length, by simpa using h⟩
  have hk : B < ((l.take (Nat.find hex)).prod : ℝ) := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h0; rw [h0] at hk; simp at hk; linarith
  obtain ⟨k', hk'⟩ : ∃ k', Nat.find hex = k' + 1 := Nat.exists_eq_succ_of_ne_zero hk0
  have hmin : ¬ B < ((l.take k').prod : ℝ) := Nat.find_min hex (by omega)
  refine ⟨k' + 1, hk' ▸ hk, ?_⟩
  have hlt : k' < l.length := by
    by_contra hc
    rw [List.take_of_length_le (not_lt.mp hc)] at hmin
    exact hmin h
  rw [List.prod_take_succ _ _ hlt, Nat.cast_mul]
  have hy : 0 ≤ ((l.take k').prod : ℝ) := by positivity
  exact mul_le_mul (not_lt.mp hmin) (hl _ (List.getElem_mem _)).2 (by positivity) (by linarith)


lemma isCoprime_of_dvd_term {q : ℕ} {a t : ℤ} {e : ℤ} (hcop : IsCoprime a (q : ℤ))
    (he : e ∣ a + q * t) : IsCoprime e q :=
  IsCoprime.of_isCoprime_of_dvd_left (hcop.add_mul_left_left t) he

lemma dvd_sub_of_dvd_terms {q : ℕ} {a t t' : ℤ} {e : ℤ} (hcop : IsCoprime a (q : ℤ))
    (he : e ∣ a + q * t) (he' : e ∣ a + q * t') : e ∣ t - t' := by
  have hc := isCoprime_of_dvd_term hcop he
  have : e ∣ (q : ℤ) * (t - t') := by
    have := dvd_sub he he'
    rwa [show a + q * t - (a + q * t') = (q : ℤ) * (t - t') by ring] at this
  exact hc.dvd_of_dvd_mul_left this

/-- (F1): the `t` in an interval of length `len` with `e ∣ a + q t` number at most `len/e + 1`. -/
lemma card_filter_dvd_le {q : ℕ} {a t0 : ℤ} {len e : ℕ} (hcop : IsCoprime a (q : ℤ)) (he : 0 < e) :
    (((Ico t0 (t0 + len)).filter (fun t => (e : ℤ) ∣ a + q * t)).card : ℝ) ≤ len / e + 1 := by
  set F := (Ico t0 (t0 + len)).filter (fun t => (e : ℤ) ∣ a + q * t)
  rcases F.eq_empty_or_nonempty with hF | ⟨t1, ht1⟩
  · rw [hF]; simp only [card_empty, Nat.cast_zero]; positivity
  have he' : (0 : ℤ) < e := by exact_mod_cast he
  set m : ℤ := ((len : ℤ) - 1) / e
  have hmaps : Set.MapsTo (fun t => (t - t0) / (e : ℤ)) F (Icc 0 m) := by
    intro t ht
    simp only [F, coe_filter, mem_Ico, Set.mem_ofPred_eq] at ht
    simp only [coe_Icc, Set.mem_Icc]
    exact ⟨Int.ediv_nonneg (by omega) he'.le, Int.ediv_le_ediv he' (by omega)⟩
  have hinj : Set.InjOn (fun t => (t - t0) / (e : ℤ)) F := by
    intro t ht t' ht' heq
    simp only [F, coe_filter, mem_Ico, Set.mem_ofPred_eq] at ht ht'
    have hd : (e : ℤ) ∣ t - t' := dvd_sub_of_dvd_terms hcop ht.2 ht'.2
    have hmod : (t - t0) % e = (t' - t0) % e := by
      apply Int.modEq_iff_dvd.mpr
      rw [show t' - t0 - (t - t0) = -(t - t') by ring]
      exact (dvd_neg).mpr hd
    have h1 := Int.mul_ediv_add_emod (t - t0) e
    have h2 := Int.mul_ediv_add_emod (t' - t0) e
    simp only at heq
    rw [heq, hmod] at h1
    linarith
  have hcard := card_le_card_of_injOn _ hmaps hinj
  rw [Int.card_Icc] at hcard
  have hm0 : 0 ≤ m := by
    simp only [F, mem_filter, mem_Ico] at ht1
    exact Int.ediv_nonneg (by omega) he'.le
  have hc : (F.card : ℤ) ≤ m + 1 := by
    have := Int.toNat_of_nonneg (show 0 ≤ m + 1 - 0 by omega)
    omega
  have hme : m * e ≤ (len : ℤ) - 1 := Int.ediv_mul_le _ (by omega)
  have key : ((F.card : ℤ) - 1) * e ≤ len := by nlinarith
  have key' : ((F.card : ℝ) - 1) * e ≤ len := by exact_mod_cast key
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  rw [div_add_one heR.ne', le_div_iff₀ heR]
  nlinarith


/-- `N_y = ⌊log X / log y⌋`: an upper bound for the number of prime factors `> y` of an
integer of size at most `X`. -/
noncomputable def Ny (X y : ℝ) : ℕ := ⌊Real.log X / Real.log y⌋₊

/-- `G_y(Z) = ∑_{0 ≤ i ≤ log Z / log y} binom(N_y, i)`. -/
noncomputable def G (X y Z : ℝ) : ℝ :=
  ∑ i ∈ range (⌊Real.log Z / Real.log y⌋₊ + 1), ((Ny X y).choose i : ℝ)

lemma sm_pos (b d : ℕ) : 0 < (smL b d).prod :=
  List.prod_pos (fun _ hx => (prime_of_mem_smL hx).1.pos)

lemma sm_dvd (b d : ℕ) (hd : d ≠ 0) : (smL b d).prod ∣ d :=
  ⟨(rmL b d).prod, (sm_mul_rm b d hd).symm⟩

open Classical in
/-- Case `e ≤ R` counting: for a fixed nonzero `n ≤ X`, the divisors `d ≤ Z` of `n` whose
`y`-smooth part `e` is at most `R` number at most `#{e ≤ R smooth, e ∣ n} · G_y(Z)`. -/
lemma card_case1_le {X y R Z : ℝ} (hy : 2 ≤ y) {n : ℕ} (hn : n ≠ 0) (hnX : (n : ℝ) ≤ X) :
    ((n.divisors.filter (fun d => ((smL ⌊y⌋₊ d).prod : ℝ) ≤ R ∧ (d : ℝ) ≤ Z)).card : ℝ) ≤
      ((((Icc 1 ⌊R⌋₊).filter (fun e => IsSmooth y e ∧ e ∣ n)).card : ℕ) : ℝ) * G X y Z := by
  classical
  set b := ⌊y⌋₊
  set m := ⌊Real.log Z / Real.log y⌋₊
  set E' := (Icc 1 ⌊R⌋₊).filter (fun e => IsSmooth y e ∧ e ∣ n)
  set U : Finset (Multiset ℕ) :=
    (range (m + 1)).biUnion (fun i => (Multiset.powersetCard i (rmL b n : Multiset ℕ)).toFinset)
  set D := n.divisors.filter (fun d => ((smL b d).prod : ℝ) ≤ R ∧ (d : ℝ) ≤ Z)
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hmaps : Set.MapsTo (fun d => ((smL b d).prod, (rmL b d : Multiset ℕ))) D
      ↑(E' ×ˢ U) := by
    intro d hd
    simp only [D, coe_filter, Nat.mem_divisors, Set.mem_ofPred_eq] at hd
    obtain ⟨⟨hdn, -⟩, hsR, hdZ⟩ := hd
    have hd0 : d ≠ 0 := by rintro rfl; exact hn (Nat.eq_zero_of_zero_dvd hdn)
    rw [mem_coe, mem_product]
    constructor
    · simp only [E', mem_filter, mem_Icc]
      refine ⟨⟨sm_pos b d, Nat.le_floor hsR⟩, isSmooth_prod _ (fun _ hx => smL_bound hy0 hx),
        (sm_dvd b d hd0).trans hdn⟩
    · simp only [U, mem_biUnion, mem_range, Multiset.mem_toFinset, Multiset.mem_powersetCard,
        Multiset.coe_card]
      refine ⟨(rmL b d).length, Nat.lt_succ_of_le (length_rmL_le hy hd0 hdZ), ?_, rfl⟩
      exact Multiset.coe_le.mpr (rmL_sublist b hdn hn).subperm
  have hinj : Set.InjOn (fun d => ((smL b d).prod, (rmL b d : Multiset ℕ))) D := by
    intro d hd d' hd' heq
    simp only [D, coe_filter, Nat.mem_divisors, Set.mem_ofPred_eq] at hd hd'
    have hd0 : d ≠ 0 := by rintro rfl; exact hn (Nat.eq_zero_of_zero_dvd hd.1.1)
    have hd0' : d' ≠ 0 := by rintro rfl; exact hn (Nat.eq_zero_of_zero_dvd hd'.1.1)
    simp only [Prod.mk.injEq] at heq
    have h2 : (rmL b d).prod = (rmL b d').prod := by
      have := congrArg Multiset.prod heq.2
      simpa only [Multiset.prod_coe] using this
    rw [← sm_mul_rm b d hd0, ← sm_mul_rm b d' hd0', heq.1, h2]
  have hcard : D.card ≤ E'.card * U.card := by
    have := card_le_card_of_injOn _ hmaps hinj
    rwa [card_product] at this
  have hlen : (rmL b n).length ≤ Ny X y := length_rmL_le hy hn hnX
  have hU : (U.card : ℝ) ≤ G X y Z := by
    have h1 : U.card ≤ ∑ i ∈ range (m + 1), (Ny X y).choose i := by
      refine card_biUnion_le.trans (sum_le_sum fun i _ => ?_)
      refine (Multiset.toFinset_card_le _).trans ?_
      rw [Multiset.card_powersetCard, Multiset.coe_card]
      exact Nat.choose_le_choose i hlen
    unfold G
    exact_mod_cast h1
  calc (D.card : ℝ) ≤ (E'.card : ℝ) * U.card := by exact_mod_cast hcard
    _ ≤ (E'.card : ℝ) * G X y Z := by gcongr


/-- Dyadic decomposition of `1/d` for `P < d ≤ 2^J P`. -/
lemma one_div_le_dyadic {P : ℝ} (hP : 0 < P) {J d : ℕ} (hd : P < d) (hdJ : (d : ℝ) ≤ 2 ^ J * P) :
    (1 / d : ℝ) ≤ ∑ j ∈ range J,
      if 2 ^ j * P < (d : ℝ) ∧ (d : ℝ) ≤ 2 ^ (j + 1) * P then (1 / 2 : ℝ) ^ j / P else 0 := by
  classical
  have hex : ∃ j : ℕ, (d : ℝ) ≤ 2 ^ j * P := ⟨J, hdJ⟩
  have hspec := Nat.find_spec hex
  have h0 : Nat.find hex ≠ 0 := by
    intro h; rw [h] at hspec; simp at hspec; linarith
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero h0
  have hmin : ¬ (d : ℝ) ≤ 2 ^ j * P := Nat.find_min hex (by omega)
  have hjJ : j < J := by
    have := Nat.find_min' hex hdJ
    omega
  rw [hj] at hspec
  have hcond : 2 ^ j * P < (d : ℝ) ∧ (d : ℝ) ≤ 2 ^ (j + 1) * P := ⟨not_le.mp hmin, hspec⟩
  refine le_trans ?_ (single_le_sum (f := fun j => if 2 ^ j * P < (d : ℝ) ∧ (d : ℝ) ≤
    2 ^ (j + 1) * P then (1 / 2 : ℝ) ^ j / P else 0) (fun i _ => by
      split_ifs
      · exact div_nonneg (by positivity) hP.le
      · exact le_refl 0)
    (mem_range.mpr hjJ))
  simp only [hcond, and_self, ite_true]
  have h2P : 0 < 2 ^ j * P := mul_pos (by positivity) hP
  rw [one_div_pow, div_div, one_div_le_one_div (lt_trans h2P hcond.1) h2P]
  exact (not_le.mp hmin).le

lemma G_nonneg (X y Z : ℝ) : 0 ≤ G X y Z := by
  unfold G; positivity

open Classical in
/-- Case `e ≤ R` of Lemma 7.2. -/
lemma case1_bound (q : ℕ) (a t0 : ℤ) (len : ℕ) {X R T' y M : ℝ} (J : ℕ)
    (hcop : IsCoprime a (q : ℤ))
    (hA : ∀ t ∈ Ico t0 (t0 + len), a + q * t ≠ 0 ∧ ((a + q * t).natAbs : ℝ) ≤ X)
    (hlen : (len : ℝ) ≤ R) (hT' : 1 ≤ T') (hy : 2 ≤ y) (hyR : y ≤ R)
    (hM : ∀ F : Finset ℕ, (∀ e ∈ F, 0 < e ∧ IsSmooth y e ∧ (e : ℝ) ≤ R) →
      ∑ e ∈ F, (1 / e : ℝ) ≤ M)
    (hJ : X ≤ 2 ^ J * (T' * R)) :
    ∑ t ∈ Ico t0 (t0 + len), ∑ d ∈ ((a + q * t).natAbs.divisors.filter
        (fun d : ℕ => T' * R < (d : ℝ))).filter (fun d => ((smL ⌊y⌋₊ d).prod : ℝ) ≤ R), (1 / d : ℝ) ≤
      2 * M / T' * ∑ j ∈ range J, (1 / 2 : ℝ) ^ j * G X y (2 ^ (j + 1) * (T' * R)) := by
  set I := Ico t0 (t0 + len)
  set P := T' * R
  have hR : 0 < R := by linarith
  have hP : 0 < P := by positivity
  set D1 : ℤ → Finset ℕ := fun t => ((a + q * t).natAbs.divisors.filter
        (fun d : ℕ => P < (d : ℝ))).filter (fun d => ((smL ⌊y⌋₊ d).prod : ℝ) ≤ R)
  set cls : ℕ → ℕ → Prop := fun j d => 2 ^ j * P < (d : ℝ) ∧ (d : ℝ) ≤ 2 ^ (j + 1) * P
  set Gj : ℕ → ℝ := fun j => G X y (2 ^ (j + 1) * P)
  set E0 := (Icc 1 ⌊R⌋₊).filter (fun e => IsSmooth y e)
  -- step a
  have stepa : ∑ t ∈ I, ∑ d ∈ D1 t, (1 / d : ℝ) ≤
      ∑ t ∈ I, ∑ d ∈ D1 t, ∑ j ∈ range J, if cls j d then (1 / 2 : ℝ) ^ j / P else 0 := by
    apply sum_le_sum; intro t ht
    apply sum_le_sum; intro d hd
    simp only [D1, mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨⟨hdn, hn0⟩, hPd⟩, -⟩ := hd
    have hdn' : (d : ℝ) ≤ X :=
      le_trans (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdn) (hA t ht).2
    exact one_div_le_dyadic hP hPd (hdn'.trans hJ)
  -- step b
  have stepb : ∑ t ∈ I, ∑ d ∈ D1 t, ∑ j ∈ range J, (if cls j d then (1 / 2 : ℝ) ^ j / P else 0) =
      ∑ j ∈ range J, (1 / 2 : ℝ) ^ j / P * ∑ t ∈ I, (((D1 t).filter (cls j)).card : ℝ) := by
    rw [show (∑ t ∈ I, ∑ d ∈ D1 t, ∑ j ∈ range J,
        (if cls j d then (1 / 2 : ℝ) ^ j / P else 0)) =
        ∑ t ∈ I, ∑ j ∈ range J, ∑ d ∈ D1 t, (if cls j d then (1 / 2 : ℝ) ^ j / P else 0) from
      sum_congr rfl (fun t _ => sum_comm)]
    rw [sum_comm]
    apply sum_congr rfl; intro j _
    rw [mul_sum]
    apply sum_congr rfl; intro t _
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  -- step c
  have stepc : ∀ j, ∀ t ∈ I, (((D1 t).filter (cls j)).card : ℝ) ≤
      (((Icc 1 ⌊R⌋₊).filter (fun e => IsSmooth y e ∧ e ∣ (a + q * t).natAbs)).card : ℝ) * Gj j := by
    intro j t ht
    have hn0 : (a + q * t).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (hA t ht).1
    refine le_trans ?_ (card_case1_le hy hn0 (hA t ht).2)
    exact Nat.cast_le.mpr (card_le_card (fun d hd => by
      simp only [D1, cls, mem_filter] at hd ⊢
      exact ⟨hd.1.1.1, hd.1.2, hd.2.2⟩))
  -- step d
  have stepd : ∑ t ∈ I,
      (((Icc 1 ⌊R⌋₊).filter (fun e => IsSmooth y e ∧ e ∣ (a + q * t).natAbs)).card : ℝ) ≤
      2 * R * M := by
    have hswap : ∑ t ∈ I,
        (((Icc 1 ⌊R⌋₊).filter (fun e => IsSmooth y e ∧ e ∣ (a + q * t).natAbs)).card : ℝ) =
        ∑ e ∈ E0, ((I.filter (fun t => (e : ℤ) ∣ a + q * t)).card : ℝ) := by
      simp only [card_eq_sum_ones, Nat.cast_sum, sum_filter, E0]
      rw [sum_comm]
      apply sum_congr rfl; intro e _
      by_cases hs : IsSmooth y e <;> simp [hs, Int.natCast_dvd]
    rw [hswap]
    have hE0 : ∑ e ∈ E0, (1 / e : ℝ) ≤ M := hM E0 (fun e he => by
      simp only [E0, mem_filter, mem_Icc] at he
      exact ⟨he.1.1, he.2, le_trans (by exact_mod_cast he.1.2) (Nat.floor_le hR.le)⟩)
    calc ∑ e ∈ E0, ((I.filter (fun t => (e : ℤ) ∣ a + q * t)).card : ℝ)
        ≤ ∑ e ∈ E0, 2 * R * (1 / e : ℝ) := by
          apply sum_le_sum; intro e he
          simp only [E0, mem_filter, mem_Icc] at he
          have he0 : (0 : ℝ) < e := by exact_mod_cast he.1.1
          have heR : (e : ℝ) ≤ R := le_trans (by exact_mod_cast he.1.2) (Nat.floor_le hR.le)
          refine (card_filter_dvd_le hcop he.1.1).trans ?_
          have h1 : (len : ℝ) / e ≤ R / e := div_le_div_of_nonneg_right hlen he0.le
          have h2 : (1 : ℝ) ≤ R / e := (one_le_div he0).mpr heR
          have : 2 * R * (1 / (e : ℝ)) = R / e + R / e := by ring
          linarith
      _ = 2 * R * ∑ e ∈ E0, (1 / e : ℝ) := by rw [mul_sum]
      _ ≤ 2 * R * M := by gcongr
  calc ∑ t ∈ I, ∑ d ∈ D1 t, (1 / d : ℝ)
      ≤ ∑ j ∈ range J, (1 / 2 : ℝ) ^ j / P * ∑ t ∈ I, (((D1 t).filter (cls j)).card : ℝ) :=
        stepa.trans stepb.le
    _ ≤ ∑ j ∈ range J, (1 / 2 : ℝ) ^ j / P * (Gj j * (2 * R * M)) := by
        apply sum_le_sum; intro j _
        gcongr
        calc ∑ t ∈ I, (((D1 t).filter (cls j)).card : ℝ)
            ≤ ∑ t ∈ I, (((Icc 1 ⌊R⌋₊).filter
                (fun e => IsSmooth y e ∧ e ∣ (a + q * t).natAbs)).card : ℝ) * Gj j :=
              sum_le_sum (stepc j)
          _ = Gj j * ∑ t ∈ I, (((Icc 1 ⌊R⌋₊).filter
                (fun e => IsSmooth y e ∧ e ∣ (a + q * t).natAbs)).card : ℝ) := by
              rw [mul_sum]; exact sum_congr rfl (fun _ _ => mul_comm _ _)
          _ ≤ Gj j * (2 * R * M) := mul_le_mul_of_nonneg_left stepd (G_nonneg _ _ _)
    _ = 2 * M / T' * ∑ j ∈ range J, (1 / 2 : ℝ) ^ j * G X y (2 ^ (j + 1) * (T' * R)) := by
        rw [mul_sum]
        apply sum_congr rfl; intro j _
        simp only [Gj, P]
        field_simp


open Classical in
/-- `S = {s : R/y < s ≤ R, P⁺(s) ≤ y}`. -/
noncomputable def Sset (R y : ℝ) : Finset ℕ :=
  (Icc 1 ⌊R⌋₊).filter (fun s : ℕ => R / y < (s : ℝ) ∧ IsSmooth y s)

open Classical in
/-- `Δ(A_s; Y)` for `A_s = {n/s : n ∈ A, s ∣ n}`, written over the original index set. -/
noncomputable def DeltaSub (q : ℕ) (a : ℤ) (I : Finset ℤ) (s : ℕ) (Y : ℝ) : ℝ :=
  ∑ t ∈ I.filter (fun t : ℤ => (s : ℤ) ∣ a + q * t),
    ∑ d ∈ ((a + q * t).natAbs / s).divisors.filter (fun d : ℕ => Y < (d : ℝ)), (1 / d : ℝ)

/-- Case `e > R`: some `s ∈ S` divides `d`. -/
lemma exists_s {R y : ℝ} (hy : 2 ≤ y) (hyR : y ≤ R) {d : ℕ} (hd : d ≠ 0)
    (he : ¬ ((smL ⌊y⌋₊ d).prod : ℝ) ≤ R) : ∃ s ∈ Sset R y, s ∣ d := by
  classical
  have hy0 : (0 : ℝ) < y := by linarith
  have hB : 1 ≤ R / y := (one_le_div hy0).mpr hyR
  have hRy : R / y ≤ R := div_le_self (by linarith) (by linarith)
  have hl : ∀ x ∈ smL ⌊y⌋₊ d, 0 < x ∧ (x : ℝ) ≤ y := fun x hx => smL_bound hy0.le hx
  obtain ⟨k, hk1, hk2⟩ := prefix_exists (smL ⌊y⌋₊ d) hB hl (by linarith [not_le.mp he])
  have hk2' : (((smL ⌊y⌋₊ d).take k).prod : ℝ) ≤ R := by
    rwa [div_mul_cancel₀ R hy0.ne'] at hk2
  have hsub : List.Sublist ((smL ⌊y⌋₊ d).take k) (smL ⌊y⌋₊ d) := (List.take_prefix k _).sublist
  have htake : ∀ x ∈ (smL ⌊y⌋₊ d).take k, 0 < x ∧ (x : ℝ) ≤ y := fun x hx => hl x (hsub.subset hx)
  refine ⟨((smL ⌊y⌋₊ d).take k).prod, ?_, hsub.prod_dvd_prod.trans (sm_dvd _ d hd)⟩
  simp only [Sset, mem_filter, mem_Icc]
  exact ⟨⟨List.prod_pos (fun x hx => (htake x hx).1), Nat.le_floor hk2'⟩, hk1,
    isSmooth_prod _ htake⟩

open Classical in
/-- Case `e > R` of Lemma 7.2. -/
lemma case2_bound (q : ℕ) (a t0 : ℤ) (len : ℕ) {R T' y : ℝ}
    (hA : ∀ t ∈ Ico t0 (t0 + len), a + q * t ≠ 0) (hy : 2 ≤ y) (hyR : y ≤ R) :
    ∑ t ∈ Ico t0 (t0 + len), ∑ d ∈ ((a + q * t).natAbs.divisors.filter
        (fun d : ℕ => T' * R < (d : ℝ))).filter (fun d => ¬ ((smL ⌊y⌋₊ d).prod : ℝ) ≤ R),
        (1 / d : ℝ) ≤
      ∑ s ∈ Sset R y, (1 / s : ℝ) * DeltaSub q a (Ico t0 (t0 + len)) s (T' * R / s) := by
  set I := Ico t0 (t0 + len)
  set inner : ℤ → ℕ → ℝ := fun t s => ∑ d ∈ ((a + q * t).natAbs / s).divisors.filter
      (fun d : ℕ => T' * R / s < (d : ℝ)), (1 / d : ℝ)
  have hRHS : ∑ s ∈ Sset R y, (1 / s : ℝ) * DeltaSub q a I s (T' * R / s) =
      ∑ t ∈ I, ∑ s ∈ (Sset R y).filter (fun s : ℕ => (s : ℤ) ∣ a + q * t),
        (1 / s : ℝ) * inner t s := by
    simp only [DeltaSub, mul_sum, sum_filter]
    rw [sum_comm]
    apply sum_congr rfl; intro t _
    apply sum_congr rfl; intro s _
    split_ifs <;> simp [inner, sum_filter]
  rw [hRHS]
  apply sum_le_sum; intro t ht
  set n := (a + q * t).natAbs
  have hn : n ≠ 0 := Int.natAbs_ne_zero.mpr (hA t ht)
  set D2 := (n.divisors.filter (fun d : ℕ => T' * R < (d : ℝ))).filter
    (fun d => ¬ ((smL ⌊y⌋₊ d).prod : ℝ) ≤ R)
  have hex : ∀ d ∈ D2, ∃ s ∈ Sset R y, s ∣ d := by
    intro d hd
    simp only [D2, mem_filter, Nat.mem_divisors] at hd
    have hd0 : d ≠ 0 := by rintro rfl; exact hn (Nat.eq_zero_of_zero_dvd hd.1.1.1)
    exact exists_s hy hyR hd0 hd.2
  choose! sf hsfS hsfd using hex
  set Sf := (Sset R y).filter (fun s : ℕ => (s : ℤ) ∣ a + q * t)
  have hmaps : ∀ d ∈ D2, sf d ∈ Sf := by
    intro d hd
    have hdn : d ∣ n := by
      simp only [D2, mem_filter, Nat.mem_divisors] at hd; exact hd.1.1.1
    simp only [Sf, mem_filter]
    exact ⟨hsfS d hd, Int.natCast_dvd.mpr ((hsfd d hd).trans hdn)⟩
  rw [← sum_fiberwise_of_maps_to hmaps]
  apply sum_le_sum; intro s hs
  simp only [Sf, mem_filter, Sset, mem_Icc] at hs
  have hs0 : 0 < s := hs.1.1.1
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs0
  have hsn : s ∣ n := Int.natCast_dvd.mp hs.2
  rw [mul_sum]
  refine sum_le_sum_of_injOn (fun d => d / s) ?_ ?_ ?_ ?_
  · intro d hd d' hd' heq
    simp only [coe_filter, Set.mem_ofPred_eq] at hd hd'
    have h1 : s ∣ d := hd.2 ▸ hsfd d hd.1
    have h2 : s ∣ d' := hd'.2 ▸ hsfd d' hd'.1
    simp only at heq
    rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, heq]
  · intro x hx
    simp only [mem_image, mem_filter] at hx
    obtain ⟨d, ⟨hdD, hds⟩, rfl⟩ := hx
    have hsd : s ∣ d := hds ▸ hsfd d hdD
    simp only [D2, mem_filter, Nat.mem_divisors] at hdD
    simp only [mem_filter, Nat.mem_divisors]
    refine ⟨⟨Nat.div_dvd_div hsd hdD.1.1.1, ?_⟩, ?_⟩
    · exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hsn) hs0).ne'
    · rw [Nat.cast_div hsd hsR.ne']
      exact div_lt_div_of_pos_right hdD.1.2 hsR
  · intro d hd
    simp only [mem_filter] at hd
    have hsd : s ∣ d := hd.2 ▸ hsfd d hd.1
    rw [Nat.cast_div hsd hsR.ne']
    have hd0 : (d : ℝ) ≠ 0 := by
      simp only [D2, mem_filter, Nat.mem_divisors] at hd
      have : d ≠ 0 := by rintro rfl; exact hn (Nat.eq_zero_of_zero_dvd hd.1.1.1.1)
      exact_mod_cast this
    field_simp
    rfl
  · intro x _ _
    positivity


open Classical in
/-- `Δ(A;Y) = ∑_{t ∈ I} ∑_{d ∣ a+qt, d > Y} 1/d` for the progression `A = {a + q t : t ∈ I}`. -/
noncomputable def Delta (q : ℕ) (a : ℤ) (I : Finset ℤ) (Y : ℝ) : ℝ :=
  ∑ t ∈ I, ∑ d ∈ (a + q * t).natAbs.divisors.filter (fun d : ℕ => Y < (d : ℝ)), (1 / d : ℝ)

/-- **Lemma 7.2 (One step).** Let `A = {a + q t : t ∈ I}`, `I = [t0, t0 + len)`, be an
admissible progression (`gcd(a,q) = 1`, `0 < |a + q t| ≤ X`) of length `len ≤ R`; let `T' ≥ 1`
and `2 ≤ y ≤ R`; let `M` bound `∑ 1/e` over every finite set of `y`-smooth `e ≥ 1` (so `M` can be
`M(y) = ∏_{ℓ ≤ y} (1 - 1/ℓ)⁻¹`); and let `J` satisfy `X ≤ 2^J T' R`. Then
`Δ(A; T'R) ≤ (2M/T') ∑_{j<J} 2^{-j} G_y(2^{j+1} T'R) + ∑_{s ∈ S} (1/s) Δ(A_s; T'R/s)`. -/
theorem one_step_le (q : ℕ) (a t0 : ℤ) (len : ℕ) {X R T' y M : ℝ} (J : ℕ)
    (hcop : Int.gcd a q = 1)
    (hA : ∀ t ∈ Ico t0 (t0 + len), a + q * t ≠ 0 ∧ ((a + q * t).natAbs : ℝ) ≤ X)
    (hlen : (len : ℝ) ≤ R) (hT' : 1 ≤ T') (hy : 2 ≤ y) (hyR : y ≤ R)
    (hM : ∀ F : Finset ℕ, (∀ e ∈ F, 0 < e ∧ IsSmooth y e ∧ (e : ℝ) ≤ R) →
      ∑ e ∈ F, (1 / e : ℝ) ≤ M)
    (hJ : X ≤ 2 ^ J * (T' * R)) :
    Delta q a (Ico t0 (t0 + len)) (T' * R) ≤
      2 * M / T' * ∑ j ∈ range J, (1 / 2 : ℝ) ^ j * G X y (2 ^ (j + 1) * (T' * R)) +
      ∑ s ∈ Sset R y, (1 / s : ℝ) * DeltaSub q a (Ico t0 (t0 + len)) s (T' * R / s) := by
  classical
  have hcop' : IsCoprime a (q : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  unfold Delta
  rw [show (∑ t ∈ Ico t0 (t0 + len), ∑ d ∈ (a + q * t).natAbs.divisors.filter
        (fun d : ℕ => T' * R < (d : ℝ)), (1 / d : ℝ)) =
      (∑ t ∈ Ico t0 (t0 + len), ∑ d ∈ ((a + q * t).natAbs.divisors.filter
        (fun d : ℕ => T' * R < (d : ℝ))).filter (fun d => ((smL ⌊y⌋₊ d).prod : ℝ) ≤ R),
          (1 / d : ℝ)) +
      ∑ t ∈ Ico t0 (t0 + len), ∑ d ∈ ((a + q * t).natAbs.divisors.filter
        (fun d : ℕ => T' * R < (d : ℝ))).filter (fun d => ¬ ((smL ⌊y⌋₊ d).prod : ℝ) ≤ R),
          (1 / d : ℝ) by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun t _ => (sum_filter_add_sum_filter_not _ _ _).symm)]
  exact add_le_add (case1_bound q a t0 len J hcop' hA hlen hT' hy hyR hM hJ)
    (case2_bound q a t0 len (fun t ht => (hA t ht).1) hy hyR)

/-- **Lemma 7.2 (One step)**, with the paper's hypothesis on `M` (all finite sets of `y`-smooth
numbers). `one_step_le` only needs the bound for sets of `y`-smooth numbers at most `R`. -/
theorem one_step (q : ℕ) (a t0 : ℤ) (len : ℕ) {X R T' y M : ℝ} (J : ℕ)
    (hcop : Int.gcd a q = 1)
    (hA : ∀ t ∈ Ico t0 (t0 + len), a + q * t ≠ 0 ∧ ((a + q * t).natAbs : ℝ) ≤ X)
    (hlen : (len : ℝ) ≤ R) (hT' : 1 ≤ T') (hy : 2 ≤ y) (hyR : y ≤ R)
    (hM : ∀ F : Finset ℕ, (∀ e ∈ F, 0 < e ∧ IsSmooth y e) → ∑ e ∈ F, (1 / e : ℝ) ≤ M)
    (hJ : X ≤ 2 ^ J * (T' * R)) :
    Delta q a (Ico t0 (t0 + len)) (T' * R) ≤
      2 * M / T' * ∑ j ∈ range J, (1 / 2 : ℝ) ^ j * G X y (2 ^ (j + 1) * (T' * R)) +
      ∑ s ∈ Sset R y, (1 / s : ℝ) * DeltaSub q a (Ico t0 (t0 + len)) s (T' * R / s) :=
  one_step_le q a t0 len J hcop hA hlen hT' hy hyR
    (fun F hF => hM F (fun e he => ⟨(hF e he).1, (hF e he).2.1⟩)) hJ


open Classical in
/-- **Lemma 7.2, first assertion.** A nonempty `A_s = {n/s : n ∈ A, s ∣ n}` is an admissible
progression `{a' + q v : 0 ≤ v < m}` with `gcd(a', q) = 1`, elements nonzero and at most `X/s`
in absolute value, and length `m ≤ len/s + 1`; and `Δ(A_s; Y)` as written in `DeltaSub` is
the `Δ` of that progression. -/
theorem sub_progression (q : ℕ) (a t0 : ℤ) (len s : ℕ) {X : ℝ} (hs : 0 < s)
    (hcop : Int.gcd a q = 1)
    (hA : ∀ t ∈ Ico t0 (t0 + len), a + q * t ≠ 0 ∧ ((a + q * t).natAbs : ℝ) ≤ X)
    (hne : ((Ico t0 (t0 + len)).filter (fun t : ℤ => (s : ℤ) ∣ a + q * t)).Nonempty) :
    ∃ (a' : ℤ) (m : ℕ), Int.gcd a' q = 1 ∧ (m : ℝ) ≤ len / s + 1 ∧
      (∀ v ∈ Ico (0 : ℤ) m, a' + q * v ≠ 0 ∧ ((a' + q * v).natAbs : ℝ) ≤ X / s) ∧
      ∀ Y : ℝ, DeltaSub q a (Ico t0 (t0 + len)) s Y = Delta q a' (Ico 0 m) Y := by
  have hcop' : IsCoprime a (q : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  set F := (Ico t0 (t0 + len)).filter (fun t : ℤ => (s : ℤ) ∣ a + q * t)
  have hs' : (0 : ℤ) < s := by exact_mod_cast hs
  set ts := F.min' hne
  have hts : ts ∈ F := F.min'_mem hne
  have htsF := hts
  simp only [F, mem_filter, mem_Ico] at htsF
  obtain ⟨⟨hts0, hts1⟩, a', ha'⟩ := htsF
  set m0 : ℤ := (t0 + len - 1 - ts) / s
  have hm0 : 0 ≤ m0 := Int.ediv_nonneg (by omega) hs'.le
  set m : ℕ := (m0 + 1).toNat
  have hm : (m : ℤ) = m0 + 1 := Int.toNat_of_nonneg (by omega)
  have hm0s : m0 * s ≤ t0 + len - 1 - ts := Int.ediv_mul_le _ hs'.ne'
  -- F is the image of `v ↦ ts + s v`, `0 ≤ v < m`
  have hF : F = (Ico (0 : ℤ) m).image (fun v => ts + s * v) := by
    ext t
    simp only [F, mem_filter, mem_Ico, mem_image]
    constructor
    · rintro ⟨⟨ht0, ht1⟩, hdt⟩
      have hle : ts ≤ t := F.min'_le t (by simp only [F, mem_filter, mem_Ico]; exact ⟨⟨ht0, ht1⟩, hdt⟩)
      have hd : (s : ℤ) ∣ t - ts := dvd_sub_of_dvd_terms hcop' hdt ⟨a', ha'⟩
      obtain ⟨v, hv⟩ := hd
      refine ⟨v, ⟨?_, ?_⟩, by linarith⟩
      · nlinarith
      · rw [hm]
        have : v ≤ m0 := by
          rw [Int.le_ediv_iff_mul_le hs']
          nlinarith
        omega
    · rintro ⟨v, ⟨hv0, hvm⟩, rfl⟩
      have hvm0 : v ≤ m0 := by omega
      have : s * v ≤ t0 + len - 1 - ts := by nlinarith
      refine ⟨⟨by nlinarith, by omega⟩, ?_⟩
      exact ⟨a' + q * v, by rw [show a + q * (ts + s * v) = (a + q * ts) + s * (q * v) by ring, ha']; ring⟩
  have hterm : ∀ v : ℤ, a + q * (ts + s * v) = s * (a' + q * v) := by
    intro v; rw [show a + q * (ts + s * v) = (a + q * ts) + s * (q * v) by ring, ha']; ring
  have hnat : ∀ v : ℤ, (a + q * (ts + s * v)).natAbs / s = (a' + q * v).natAbs := by
    intro v
    rw [hterm, Int.natAbs_mul, Int.natAbs_natCast, Nat.mul_div_cancel_left _ hs]
  refine ⟨a', m, ?_, ?_, ?_, ?_⟩
  · apply Int.isCoprime_iff_gcd_eq_one.mp
    exact IsCoprime.of_isCoprime_of_dvd_left (hcop'.add_mul_left_left ts) ⟨s, by rw [ha']; ring⟩
  · have hsR : (0 : ℝ) < s := by exact_mod_cast hs
    have key : ((m : ℤ) - 1) * s ≤ len := by rw [hm]; nlinarith
    have key' : ((m : ℝ) - 1) * s ≤ len := by exact_mod_cast key
    rw [div_add_one hsR.ne', le_div_iff₀ hsR]
    nlinarith
  · intro v hv
    have hvF : ts + s * v ∈ F := by rw [hF]; exact mem_image_of_mem _ hv
    simp only [F, mem_filter] at hvF
    obtain ⟨hne0, hX⟩ := hA _ hvF.1
    rw [hterm] at hne0 hX
    refine ⟨fun h => hne0 (by rw [h, mul_zero]), ?_⟩
    rw [Int.natAbs_mul, Int.natAbs_natCast, Nat.cast_mul] at hX
    have hsR : (0 : ℝ) < s := by exact_mod_cast hs
    rw [le_div_iff₀ hsR]; linarith
  · intro Y
    have hDS : DeltaSub q a (Ico t0 (t0 + len)) s Y = ∑ t ∈ F, ∑ d ∈ ((a + q * t).natAbs / s).divisors.filter
        (fun d : ℕ => Y < (d : ℝ)), (1 / d : ℝ) := by
      unfold DeltaSub; congr 1
    rw [hDS]
    unfold Delta
    rw [hF, sum_image (fun v _ w _ h => by
      have : (s : ℤ) * v = s * w := by linarith
      exact mul_left_cancel₀ hs'.ne' this)]
    apply sum_congr rfl; intro v _
    rw [hnat]

/-- Length bound used in the recursion: `len/s + 1 ≤ 2R/s` when `len ≤ R` and `s ≤ R`. -/
lemma len_div_add_one_le {len s : ℕ} {R : ℝ} (hs : 0 < s) (hlen : (len : ℝ) ≤ R)
    (hsR : (s : ℝ) ≤ R) : (len : ℝ) / s + 1 ≤ 2 * R / s := by
  have h : (0 : ℝ) < s := by exact_mod_cast hs
  rw [div_add_one h.ne', div_le_div_iff_of_pos_right h]; linarith


/-- Truncated geometric series. -/
lemma geom_sum_le_inv {p : ℕ} (hp : p.Prime) (K : ℕ) :
    ∑ k ∈ range (K + 1), (1 / (p : ℝ)) ^ k ≤ (1 - 1 / (p : ℝ))⁻¹ := by
  have h0 : (0 : ℝ) ≤ 1 / p := by positivity
  have h1 : (1 : ℝ) / p < 1 := by
    rw [div_lt_one (by exact_mod_cast hp.pos)]; exact_mod_cast hp.one_lt
  rw [← tsum_geometric_of_lt_one h0 h1]
  exact (summable_geometric_of_lt_one h0 h1).sum_le_tsum _ (fun i _ => by positivity)

/-- The hypothesis on `M` in `one_step` holds for `M(y) = ∏_{ℓ ≤ y} (1 - 1/ℓ)⁻¹`: for every finite
set `F` of `y`-smooth positive integers, `∑_{e ∈ F} 1/e ≤ ∏_{ℓ prime, ℓ ≤ y} (1 - 1/ℓ)⁻¹`. -/
theorem sum_inv_smooth_le_euler_prod (y : ℝ) (F : Finset ℕ)
    (hF : ∀ e ∈ F, 0 < e ∧ IsSmooth y e) :
    ∑ e ∈ F, (1 / e : ℝ) ≤
      ∏ p ∈ (range (⌊y⌋₊ + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))⁻¹ := by
  classical
  set P := (range (⌊y⌋₊ + 1)).filter Nat.Prime
  set K := F.sup id
  have hsupp : ∀ e ∈ F, e.primeFactors ⊆ P := by
    intro e he p hp
    simp only [P, mem_filter, mem_range]
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor ((hF e he).2 p hp)), Nat.prime_of_mem_primeFactors hp⟩
  have hval : ∀ e ∈ F, (1 / e : ℝ) = ∏ i : P, (1 / (i : ℝ)) ^ e.factorization i := by
    intro e he
    have he0 : e ≠ 0 := (hF e he).1.ne'
    have h1 : e = ∏ p ∈ P, p ^ e.factorization p := by
      conv_lhs => rw [Nat.prod_primeFactors_pow_factorization he0]
      apply prod_subset (hsupp e he)
      intro p _ hp
      rw [Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization]), pow_zero]
    rw [prod_coe_sort P (fun i => (1 / (i : ℝ)) ^ e.factorization i)]
    conv_lhs => rw [h1]
    push_cast
    rw [one_div, ← prod_inv_distrib]
    apply prod_congr rfl; intro p _
    rw [one_div, inv_pow]
  calc ∑ e ∈ F, (1 / e : ℝ)
      ≤ ∑ x ∈ Fintype.piFinset (fun _ : P => range (K + 1)), ∏ i : P, (1 / (i : ℝ)) ^ x i := by
        refine sum_le_sum_of_injOn (fun e => fun i : P => e.factorization i) ?_ ?_ ?_ ?_
        · intro e he e' he' heq
          simp only [mem_coe] at he he'
          apply Nat.eq_of_factorization_eq (hF e he).1.ne' (hF e' he').1.ne'
          intro p
          by_cases hp : p ∈ P
          · exact congrFun heq ⟨p, hp⟩
          · have h1 : p ∉ e.primeFactors := fun h => hp (hsupp e he h)
            have h2 : p ∉ e'.primeFactors := fun h => hp (hsupp e' he' h)
            rw [← Nat.support_factorization] at h1 h2
            rw [Finsupp.notMem_support_iff.mp h1, Finsupp.notMem_support_iff.mp h2]
        · intro x hx
          simp only [mem_image] at hx
          obtain ⟨e, he, rfl⟩ := hx
          rw [Fintype.mem_piFinset]
          intro i
          rw [mem_range]
          exact Nat.lt_succ_of_le ((Nat.factorization_lt _ (hF e he).1.ne').le.trans
            (le_sup (f := id) he))
        · intro e he
          exact (hval e he).le
        · intro x _ _
          positivity
    _ = ∏ i : P, ∑ k ∈ range (K + 1), (1 / (i : ℝ)) ^ k := (prod_univ_sum _ _).symm
    _ ≤ ∏ i : P, (1 - 1 / (i : ℝ))⁻¹ := by
        apply prod_le_prod₀ (fun i _ => by positivity)
        intro i _
        have hi : (i : ℕ).Prime := by
          have := i.2; simp only [P, mem_filter] at this; exact this.2
        exact geom_sum_le_inv hi K
    _ = ∏ p ∈ P, (1 - 1 / (p : ℝ))⁻¹ := prod_coe_sort P (fun p => (1 - 1 / (p : ℝ))⁻¹)


/-- Lemma 7.2 with the paper's `M(y) = ∏_{ℓ ≤ y} (1 - 1/ℓ)⁻¹`. -/
theorem one_step_euler (q : ℕ) (a t0 : ℤ) (len : ℕ) {X R T' y : ℝ} (J : ℕ)
    (hcop : Int.gcd a q = 1)
    (hA : ∀ t ∈ Ico t0 (t0 + len), a + q * t ≠ 0 ∧ ((a + q * t).natAbs : ℝ) ≤ X)
    (hlen : (len : ℝ) ≤ R) (hT' : 1 ≤ T') (hy : 2 ≤ y) (hyR : y ≤ R)
    (hJ : X ≤ 2 ^ J * (T' * R)) :
    Delta q a (Ico t0 (t0 + len)) (T' * R) ≤
      2 * (∏ p ∈ (range (⌊y⌋₊ + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))⁻¹) / T' *
        ∑ j ∈ range J, (1 / 2 : ℝ) ^ j * G X y (2 ^ (j + 1) * (T' * R)) +
      ∑ s ∈ Sset R y, (1 / s : ℝ) * DeltaSub q a (Ico t0 (t0 + len)) s (T' * R / s) :=
  one_step q a t0 len J hcop hA hlen hT' hy hyR
    (fun F hF => sum_inv_smooth_le_euler_prod y F hF) hJ

/-- For `s ∈ S`, a nonempty `A_s` is an admissible progression (same `q`, same bound `X`) of
length at most `2R/s`, and the second sum in `one_step` is `∑_{s∈S} (1/s) Δ(A_s; T'R/s)`. -/
theorem admissible_of_mem_S (q : ℕ) (a t0 : ℤ) (len s : ℕ) {X R y : ℝ}
    (hcop : Int.gcd a q = 1)
    (hA : ∀ t ∈ Ico t0 (t0 + len), a + q * t ≠ 0 ∧ ((a + q * t).natAbs : ℝ) ≤ X)
    (hlen : (len : ℝ) ≤ R) (hsS : s ∈ Sset R y)
    (hne : ((Ico t0 (t0 + len)).filter (fun t : ℤ => (s : ℤ) ∣ a + q * t)).Nonempty) :
    ∃ (a' : ℤ) (m : ℕ), Int.gcd a' q = 1 ∧ (m : ℝ) ≤ 2 * R / s ∧
      (∀ v ∈ Ico (0 : ℤ) m, a' + q * v ≠ 0 ∧ ((a' + q * v).natAbs : ℝ) ≤ X) ∧
      ∀ Y : ℝ, DeltaSub q a (Ico t0 (t0 + len)) s Y = Delta q a' (Ico 0 m) Y := by
  simp only [Sset, mem_filter, mem_Icc] at hsS
  have hs : 0 < s := hsS.1.1
  have hsR : (s : ℝ) ≤ R := by
    have h1 : (1 : ℝ) ≤ R := by
      have : 1 ≤ ⌊R⌋₊ := hs.trans_le hsS.1.2
      exact_mod_cast (Nat.one_le_floor_iff R).mp this
    exact le_trans (by exact_mod_cast hsS.1.2) (Nat.floor_le (by linarith))
  obtain ⟨a', m, hc, hm, hv, hD⟩ := sub_progression q a t0 len s hs hcop hA hne
  obtain ⟨t, ht⟩ := hne
  have hX : 0 ≤ X := le_trans (by positivity) (hA t (mem_filter.mp ht).1).2
  have hsR' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  refine ⟨a', m, hc, hm.trans (len_div_add_one_le hs hlen hsR), fun v hv' => ?_, hD⟩
  obtain ⟨h1, h2⟩ := hv v hv'
  exact ⟨h1, h2.trans (div_le_self hX hsR')⟩

end ThetaSum

#print axioms ThetaSum.one_step
#print axioms ThetaSum.one_step_euler
#print axioms ThetaSum.sub_progression
#print axioms ThetaSum.admissible_of_mem_S
#print axioms ThetaSum.sum_inv_smooth_le_euler_prod
#print axioms ThetaSum.one_step_le
