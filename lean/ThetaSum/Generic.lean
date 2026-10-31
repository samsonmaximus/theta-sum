import ThetaSum.Tails
import ThetaSum.SignForm

/-
An elementary replacement for **Lemma 6.8** (generic θ), without Vaaler's lemma.

If `‖2 m θ‖ ≥ η` for `1 ≤ m ≤ M`, then for every arithmetic progression `n₀ + 2j` (`0 ≤ j < J`),
  `|∑_j g((n₀ + 2j) θ)| ≤ 6 J / M + 1/η`,
where `g(y) = sgn(1/2 - {y})` (`gsq`). Proof: Dirichlet's theorem gives `q ≤ 1/η` and `a` coprime
to `q` with `|2qθ - a| < η`; the hypothesis forces `q > M`. In a block of `q` consecutive `j` the
points `(n₀ + 2j)θ` are a shifted grid of step `1/q` (as `(a, q) = 1`) perturbed by less than
`η`; any half-period then contains at most `q/2 + 3` of them, so the block sum is at most `6`.
-/

open Finset

namespace ThetaSum

/-- `‖x‖ ≤ |x - a|` for every integer `a`. -/
lemma dnear_le (x : ℝ) (a : ℤ) : dnear x ≤ |x - a| := round_le x a

lemma fract_le_sub_int {x : ℝ} {m : ℤ} (hm : (m : ℝ) ≤ x) : Int.fract x ≤ x - m := by
  rw [Int.fract]
  have : m ≤ ⌊x⌋ := Int.le_floor.mpr hm
  have : (m : ℝ) ≤ ⌊x⌋ := by exact_mod_cast this
  linarith

/-- Grid count: if `(a, q) = 1`, then at most `λ q + 1` of the points `c + i a / q`, `i < q`,
lie in a half-open arc of length `λ` (here `[0, λ)` after the shift by `c`). -/
lemma grid_count (c : ℝ) (q : ℕ) (hq : 0 < q) (a : ℤ) (hcop : IsCoprime a (q : ℤ)) (lam : ℝ)
    (hlam : 0 ≤ lam) :
    (((range q).filter (fun i : ℕ => Int.fract (c + i * a / q) < lam)).card : ℝ) ≤ lam * q + 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set f : ℕ → ℤ := fun i => ⌊(q : ℝ) * Int.fract (c + i * a / q)⌋
  have hf : ∀ i : ℕ, f i = ⌊(q : ℝ) * c⌋ + (i * a - q * ⌊c + i * a / q⌋) := by
    intro i
    simp only [f]
    rw [← Int.floor_add_intCast]
    congr 1
    rw [Int.fract]; push_cast; field_simp; ring
  have hmaps : Set.MapsTo f ((range q).filter (fun i : ℕ => Int.fract (c + i * a / q) < lam))
      (Ico (0 : ℤ) ⌈lam * q⌉) := by
    intro i hi
    simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hi
    simp only [coe_Ico, Set.mem_Ico]
    constructor
    · simp only [f]; apply Int.floor_nonneg.mpr
      exact mul_nonneg hqR.le (Int.fract_nonneg _)
    · simp only [f]
      apply Int.floor_lt.mpr
      have h1 : (q : ℝ) * Int.fract (c + i * a / q) < lam * q := by nlinarith
      exact lt_of_lt_of_le h1 (Int.le_ceil _)
  have hinj : Set.InjOn f ((range q).filter (fun i : ℕ => Int.fract (c + i * a / q) < lam) :
      Set ℕ) := by
    intro i hi i' hi' heq
    simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hi hi'
    rw [hf, hf] at heq
    have h2 : (q : ℤ) ∣ ((i : ℤ) - i') * a := by
      refine ⟨⌊c + i * a / q⌋ - ⌊c + i' * a / q⌋, ?_⟩
      linarith
    have h3 : (q : ℤ) ∣ (i : ℤ) - i' := hcop.symm.dvd_of_dvd_mul_right h2
    obtain ⟨m, hm⟩ := h3
    have hlt1 : (i : ℤ) - i' < q := by omega
    have hlt2 : -(q : ℤ) < (i : ℤ) - i' := by omega
    have hq' : (0 : ℤ) < q := by exact_mod_cast hq
    have : m = 0 := by
      rcases lt_trichotomy m 0 with h | h | h
      · nlinarith
      · exact h
      · nlinarith
    subst this; simp at hm; omega
  have hcard := card_le_card_of_injOn f hmaps hinj
  rw [Int.card_Ico, sub_zero] at hcard
  have : ((⌈lam * q⌉).toNat : ℝ) ≤ lam * q + 1 := by
    have h0 : 0 ≤ ⌈lam * q⌉ := Int.ceil_nonneg (by positivity)
    have : ((⌈lam * q⌉).toNat : ℝ) = ((⌈lam * q⌉ : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h0
    rw [this]
    linarith [Int.ceil_lt_add_one (lam * q)]
  calc _ ≤ ((⌈lam * q⌉).toNat : ℝ) := by exact_mod_cast hcard
    _ ≤ _ := this

/-- If `{y - b} < 1/2` and `|y - z| < η`, then `{z - b + η} < 1/2 + 2η`. -/
lemma fract_perturb {y z b η : ℝ} (h : Int.fract (y - b) < 1 / 2) (hyz : |y - z| < η) :
    Int.fract (z - b + η) < 1 / 2 + 2 * η := by
  have hm : ((⌊y - b⌋ : ℤ) : ℝ) ≤ z - b + η := by
    have := Int.floor_le (y - b)
    have := (abs_lt.mp hyz)
    linarith
  have h1 := fract_le_sub_int hm
  have h2 : y - b - ⌊y - b⌋ < 1 / 2 := by rw [← Int.fract]; exact h
  have := (abs_lt.mp hyz)
  linarith

lemma fract_sub_half {y : ℝ} (h : ¬ Int.fract y < 1 / 2) : Int.fract (y - 1 / 2) < 1 / 2 := by
  rw [not_lt] at h
  have hm : ((⌊y⌋ : ℤ) : ℝ) ≤ y - 1 / 2 := by
    have : Int.fract y = y - ⌊y⌋ := rfl
    linarith
  have := fract_le_sub_int hm
  have : Int.fract y < 1 := Int.fract_lt_one y
  have : Int.fract y = y - ⌊y⌋ := rfl
  linarith

/-- **Block bound.** If `(a, q) = 1`, `|q α - a| < η` and `η q ≤ 1`, then for every `c`,
`|∑_{i<q} g(c + i α)| ≤ 6`. -/
lemma block_bound (c α η : ℝ) (q : ℕ) (hq : 0 < q) (a : ℤ) (hcop : IsCoprime a (q : ℤ))
    (hε : |q * α - a| < η) (hηq : η * q ≤ 1) :
    |∑ i ∈ range q, gsq (c + i * α)| ≤ 6 := by
  classical
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hη0 : 0 < η := lt_of_le_of_lt (abs_nonneg _) hε
  set P : ℕ → Prop := fun i => Int.fract (c + i * α) < 1 / 2
  -- perturbation of each point
  have hpert : ∀ i ∈ range q, |(c + i * α) - (c + i * a / q)| < η := by
    intro i hi
    have hi' : (i : ℝ) < q := by exact_mod_cast mem_range.mp hi
    have e : (c + i * α) - (c + i * a / q) = (i / q) * (q * α - a) := by field_simp; ring
    rw [e, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ i / q)]
    have : (i : ℝ) / q ≤ 1 := by rw [div_le_one hqR]; exact hi'.le
    calc (i : ℝ) / q * |q * α - a| ≤ 1 * |q * α - a| :=
          mul_le_mul_of_nonneg_right this (abs_nonneg _)
      _ < η := by linarith
  have hlam : (0 : ℝ) ≤ 1 / 2 + 2 * η := by positivity
  -- points in the lower half
  have hlow : (((range q).filter P).card : ℝ) ≤ q / 2 + 3 := by
    have hsub : (range q).filter P ⊆
        (range q).filter (fun i : ℕ => Int.fract ((c + η) + i * a / q) < 1 / 2 + 2 * η) := by
      intro i hi
      simp only [mem_filter] at hi ⊢
      refine ⟨hi.1, ?_⟩
      have := fract_perturb (b := 0) (by simpa [P] using hi.2) (hpert i hi.1)
      have e : c + i * a / q - 0 + η = (c + η) + i * a / q := by ring
      rwa [e] at this
    calc (((range q).filter P).card : ℝ) ≤ _ := by exact_mod_cast card_le_card hsub
      _ ≤ (1 / 2 + 2 * η) * q + 1 := grid_count (c + η) q hq a hcop _ hlam
      _ ≤ q / 2 + 3 := by nlinarith
  have hup : (((range q).filter (fun i => ¬ P i)).card : ℝ) ≤ q / 2 + 3 := by
    have hsub : (range q).filter (fun i => ¬ P i) ⊆
        (range q).filter (fun i : ℕ => Int.fract ((c - 1 / 2 + η) + i * a / q) < 1 / 2 + 2 * η) := by
      intro i hi
      simp only [mem_filter] at hi ⊢
      refine ⟨hi.1, ?_⟩
      have h1 : Int.fract (c + i * α - 1 / 2) < 1 / 2 := fract_sub_half hi.2
      have := fract_perturb (b := 1 / 2) h1 (hpert i hi.1)
      have e : c + i * a / q - 1 / 2 + η = (c - 1 / 2 + η) + i * a / q := by ring
      rwa [e] at this
    calc (((range q).filter (fun i => ¬ P i)).card : ℝ) ≤ _ := by exact_mod_cast card_le_card hsub
      _ ≤ (1 / 2 + 2 * η) * q + 1 := grid_count (c - 1 / 2 + η) q hq a hcop _ hlam
      _ ≤ q / 2 + 3 := by nlinarith
  have hsplit : ∑ i ∈ range q, gsq (c + i * α) =
      (((range q).filter P).card : ℝ) - (((range q).filter (fun i => ¬ P i)).card : ℝ) := by
    unfold gsq
    rw [sum_ite]
    simp only [sum_const, nsmul_eq_mul, mul_one, mul_neg]
    ring
  have htot : (((range q).filter P).card : ℝ) + (((range q).filter (fun i => ¬ P i)).card : ℝ) = q := by
    have := card_filter_add_card_filter_not (s := range q) P
    rw [card_range] at this
    exact_mod_cast this
  rw [hsplit, abs_le]
  constructor <;> linarith

/-- **Generic θ** (elementary form of Lemma 6.8). Let `M ≥ 1`, `0 < η ≤ 1/2`, and let `θ` satisfy
`‖2 m θ‖ ≥ η` for `1 ≤ m ≤ M`. Then for every integer `n₀` and every `J`,
  `|∑_{0 ≤ j < J} g((n₀ + 2j) θ)| ≤ 6 J / M + 1/η`. -/
theorem generic_bound (M : ℕ) (hM : 1 ≤ M) {η θ : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (hθ : ∀ m ∈ Icc 1 M, η ≤ dnear (2 * m * θ)) (n₀ : ℤ) (J : ℕ) :
    |∑ j ∈ range J, gsq ((n₀ + 2 * j) * θ)| ≤ 6 * J / M + 1 / η := by
  set α := 2 * θ
  set Q := ⌊1 / η⌋₊
  have hQ1 : 2 ≤ Q := by
    apply Nat.le_floor
    rw [le_div_iff₀ hη]; push_cast; linarith
  have hQη : (1 : ℝ) / (Q + 1) < η := by
    rw [div_lt_iff₀ (by positivity)]
    have := Nat.lt_floor_add_one (1 / η)
    rw [div_lt_iff₀ hη] at this
    nlinarith
  have hQle : (Q : ℝ) ≤ 1 / η := Nat.floor_le (by positivity)
  obtain ⟨a0, q0, hq0, hq0Q, happ⟩ := Real.exists_int_int_abs_mul_sub_le α (n := Q) (by omega)
  -- reduce `a0 / q0` to lowest terms
  set d := Int.gcd a0 q0
  have hd0 : 0 < d := Int.gcd_pos_of_ne_zero_right a0 hq0.ne'
  have hdq : (d : ℤ) ∣ q0 := Int.gcd_dvd_right a0 q0
  have hda : (d : ℤ) ∣ a0 := Int.gcd_dvd_left a0 q0
  obtain ⟨qz, hqz⟩ := hdq
  obtain ⟨a, ha⟩ := hda
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd0
  have hqz0 : 0 < qz := by
    by_contra h; rw [not_lt] at h; nlinarith
  have hcopZ : Int.gcd a qz = 1 := by
    have h := Int.gcd_mul_left (d : ℤ) a qz
    rw [← ha, ← hqz, Int.natAbs_natCast] at h
    -- `h : d = d * gcd a qz`
    have h' : d * Int.gcd a qz = d * 1 := by rw [mul_one]; exact h.symm
    exact Nat.eq_of_mul_eq_mul_left hd0 h'
  set q := qz.toNat
  have hqq : (q : ℤ) = qz := Int.toNat_of_nonneg hqz0.le
  have hq : 0 < q := by omega
  have hcop : IsCoprime a (q : ℤ) := by rw [hqq, Int.isCoprime_iff_gcd_eq_one]; exact hcopZ
  have hεd : |(q : ℝ) * α - a| ≤ |(q0 : ℝ) * α - a0| := by
    have e : (q0 : ℝ) * α - a0 = d * ((q : ℝ) * α - a) := by
      have : ((q : ℤ) : ℝ) = (qz : ℝ) := by exact_mod_cast hqq
      push_cast at this
      rw [hqz, ha]; push_cast; rw [← this]; ring
    rw [e, abs_mul, abs_of_pos (by exact_mod_cast hd0 : (0 : ℝ) < d)]
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd0
    nlinarith [abs_nonneg ((q : ℝ) * α - a)]
  have hε : |(q : ℝ) * α - a| < η := lt_of_le_of_lt (hεd.trans happ) hQη
  have hqQ : (q : ℝ) ≤ Q := by
    have h1 : (q : ℤ) ≤ q0 := by
      rw [hqq, hqz]
      have : (1 : ℤ) ≤ d := by exact_mod_cast hd0
      nlinarith
    have : (q : ℤ) ≤ Q := le_trans h1 hq0Q
    exact_mod_cast this
  have hηq : η * q ≤ 1 := by
    have := hqQ.trans hQle
    rw [le_div_iff₀ hη] at this; linarith
  -- `q > M`
  have hqM : M < q := by
    by_contra h
    rw [not_lt] at h
    have h1 := hθ q (mem_Icc.mpr ⟨by omega, h⟩)
    have h2 : dnear (2 * (q : ℝ) * θ) ≤ |(q : ℝ) * α - a| := by
      have := dnear_le (2 * (q : ℝ) * θ) a
      have e : 2 * (q : ℝ) * θ = (q : ℝ) * α := by simp only [α]; ring
      rw [e] at this ⊢; exact this
    linarith
  -- block decomposition by strong induction on `J`
  have key : ∀ J : ℕ, |∑ j ∈ range J, gsq ((n₀ + 2 * j) * θ)| ≤ 6 * J / q + q := by
    intro J
    induction J using Nat.strong_induction_on with
    | _ J ih =>
      by_cases hJ : J < q
      · calc |∑ j ∈ range J, gsq ((n₀ + 2 * j) * θ)|
            ≤ ∑ j ∈ range J, |gsq ((n₀ + 2 * j) * θ)| := abs_sum_le_sum_abs _ _
          _ ≤ ∑ j ∈ range J, (1 : ℝ) := by
              apply sum_le_sum; intro j _; unfold gsq; split_ifs <;> norm_num
          _ = J := by simp
          _ ≤ 6 * J / q + q := by
              have : (J : ℝ) ≤ q := by exact_mod_cast hJ.le
              have : 0 ≤ 6 * (J : ℝ) / q := by positivity
              linarith
      · rw [not_lt] at hJ
        have hsplit : ∑ j ∈ range J, gsq ((n₀ + 2 * j) * θ) =
            ∑ j ∈ range (J - q), gsq ((n₀ + 2 * j) * θ) +
              ∑ i ∈ range q, gsq (((n₀ + 2 * (J - q : ℕ)) * θ) + i * α) := by
          have h := sum_range_add (fun j : ℕ => gsq ((n₀ + 2 * j) * θ)) (J - q) q
          rw [Nat.sub_add_cancel hJ] at h
          rw [h]
          congr 1
          apply sum_congr rfl; intro i _
          congr 1; push_cast; simp only [α]; ring
        rw [hsplit]
        have hb := block_bound ((n₀ + 2 * (J - q : ℕ)) * θ) α η q hq a hcop hε hηq
        have hi := ih (J - q) (by omega)
        have hJq : ((J - q : ℕ) : ℝ) = J - q := by rw [Nat.cast_sub hJ]
        rw [hJq] at hi
        have hqR : (0 : ℝ) < q := by exact_mod_cast hq
        have e : 6 * ((J : ℝ) - q) / q + q + 6 = 6 * J / q + q := by field_simp; ring
        calc _ ≤ |∑ j ∈ range (J - q), gsq ((n₀ + 2 * j) * θ)| +
              |∑ i ∈ range q, gsq (((n₀ + 2 * (J - q : ℕ)) * θ) + i * α)| := abs_add_le _ _
          _ ≤ 6 * ((J : ℝ) - q) / q + q + 6 := by linarith
          _ = _ := e
  refine (key J).trans ?_
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 : 6 * (J : ℝ) / q ≤ 6 * J / M := by
    apply div_le_div_of_nonneg_left (by positivity) hMR
    exact_mod_cast hqM.le
  have h2 : (q : ℝ) ≤ 1 / η := hqQ.trans hQle
  linarith

/-- The form used in §8: if moreover `J ≤ t/2` and `t ≥ N > 0`, then
`(1/t) |∑ g| ≤ 3/M + 1/(η N)`. -/
theorem generic_bound_div (M : ℕ) (hM : 1 ≤ M) {η θ : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (hθ : ∀ m ∈ Icc 1 M, η ≤ dnear (2 * m * θ)) (n₀ : ℤ) (J : ℕ) {t N : ℝ} (hN : 0 < N)
    (htN : N ≤ t) (hJt : (J : ℝ) ≤ t / 2) :
    |∑ j ∈ range J, gsq ((n₀ + 2 * j) * θ)| / t ≤ 3 / M + 1 / (η * N) := by
  have ht : 0 < t := lt_of_lt_of_le hN htN
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  rw [div_le_iff₀ ht]
  refine (generic_bound M hM hη hη2 hθ n₀ J).trans ?_
  have h1 : 6 * (J : ℝ) / M ≤ 3 / M * t := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hMR]; linarith
  have h2 : 1 / η ≤ 1 / (η * N) * t := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    have : 1 / η * (η * N) = N := by field_simp
    linarith
  linarith

end ThetaSum

#print axioms ThetaSum.generic_bound
#print axioms ThetaSum.generic_bound_div
