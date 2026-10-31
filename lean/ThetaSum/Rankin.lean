import ThetaSum.OneStep

/-
Lemma 7.1 (Rankin's trick) of the paper, in the form used for the base case of Theorem D:
for `0 < α ≤ 1/2`, `Y > 0` and a nonzero integer `n` with `log n ≤ 2L` (`L ≥ e`),
  `∑_{d ∣ n, d > Y} 1/d ≤ Y^{-α} exp(4 L^α (1/α + 2))`.
The paper bounds `log P(α) ≤ 4 (4L)^α (log log (4L) + 1)` using `θ(ℓ) ≥ ℓ/2`; we use instead
the elementary bound `∑_{p ∣ n} p^{α-1} ≤ L^α/α + 2 L^α` (split the primes at `L`), which is
of the same order `O(L^α)` and needs no information on primes.
-/

open Finset

namespace ThetaSum

lemma rpow_pow_comm' {x : ℝ} (hx : 0 ≤ x) (k : ℕ) (r : ℝ) : (x ^ k) ^ r = (x ^ r) ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, mul_comm, Real.rpow_mul hx, Real.rpow_natCast]

lemma geom_sum_rpow_le {p : ℕ} (hp : p.Prime) {r : ℝ} (hr : r < 0) (K : ℕ) :
    ∑ k ∈ range (K + 1), ((p : ℝ) ^ r) ^ k ≤ (1 - (p : ℝ) ^ r)⁻¹ := by
  have h0 : (0 : ℝ) ≤ (p : ℝ) ^ r := by positivity
  have h1 : (p : ℝ) ^ r < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) hr
  rw [← tsum_geometric_of_lt_one h0 h1]
  exact (summable_geometric_of_lt_one h0 h1).sum_le_tsum _ (fun i _ => by positivity)

/-- `σ_r(n) = ∑_{d ∣ n} d^r ≤ ∏_{p ∣ n} (1 - p^r)⁻¹` for `r < 0`. -/
theorem sum_divisors_rpow_le (n : ℕ) (hn : n ≠ 0) {r : ℝ} (hr : r < 0) :
    ∑ d ∈ n.divisors, (d : ℝ) ^ r ≤ ∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ r)⁻¹ := by
  classical
  set P := n.primeFactors
  set K := n
  have hsupp : ∀ d ∈ n.divisors, d.primeFactors ⊆ P := fun d hd =>
    Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hn
  have hd0 : ∀ d ∈ n.divisors, d ≠ 0 := fun d hd => Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
  have hval : ∀ d ∈ n.divisors, (d : ℝ) ^ r = ∏ i : P, ((i : ℝ) ^ r) ^ d.factorization i := by
    intro d hd
    have h1 : d = ∏ p ∈ P, p ^ d.factorization p := by
      conv_lhs => rw [Nat.prod_primeFactors_pow_factorization (hd0 d hd)]
      apply prod_subset (hsupp d hd)
      intro p _ hp
      rw [Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization]), pow_zero]
    rw [prod_coe_sort P (fun i => ((i : ℝ) ^ r) ^ d.factorization i)]
    conv_lhs => rw [h1]
    push_cast
    rw [← Real.finsetProd_rpow _ _ (fun i _ => by positivity)]
    exact prod_congr rfl (fun p _ => rpow_pow_comm' (by positivity) _ _)
  calc ∑ d ∈ n.divisors, (d : ℝ) ^ r
      ≤ ∑ x ∈ Fintype.piFinset (fun _ : P => range (K + 1)), ∏ i : P, ((i : ℝ) ^ r) ^ x i := by
        refine sum_le_sum_of_injOn (fun e => fun i : P => e.factorization i) ?_ ?_ ?_ ?_
        · intro e he e' he' heq
          simp only [mem_coe] at he he'
          apply Nat.eq_of_factorization_eq (hd0 e he) (hd0 e' he')
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
          exact Nat.lt_succ_of_le ((Nat.factorization_lt _ (hd0 e he)).le.trans
            (Nat.divisor_le he))
        · intro e he
          exact (hval e he).le
        · intro x _ _
          positivity
    _ = ∏ i : P, ∑ k ∈ range (K + 1), ((i : ℝ) ^ r) ^ k := (prod_univ_sum _ _).symm
    _ ≤ ∏ i : P, (1 - (i : ℝ) ^ r)⁻¹ := by
        apply prod_le_prod₀ (fun i _ => by positivity)
        intro i _
        exact geom_sum_rpow_le (Nat.prime_of_mem_primeFactors i.2) hr K
    _ = ∏ p ∈ P, (1 - (p : ℝ) ^ r)⁻¹ := prod_coe_sort P (fun p => (1 - (p : ℝ) ^ r)⁻¹)

lemma inv_one_sub_le_exp {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 3 / 4) :
    (1 - x)⁻¹ ≤ Real.exp (4 * x) := by
  have h1 : 0 < 1 - x := by linarith
  rw [inv_le_iff_one_le_mul₀' h1]
  have h2 : 1 + 4 * x ≤ Real.exp (4 * x) := by linarith [Real.add_one_le_exp (4 * x)]
  nlinarith

lemma two_rpow_neg_half_le : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
  rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, inv_le_comm₀ (by positivity) (by norm_num)]
  rw [Real.le_sqrt (by norm_num) (by norm_num)]
  norm_num

/-- `∏_{p ∣ n} (1 - p^{α-1})⁻¹ ≤ exp (4 ∑_{p ∣ n} p^{α-1})` for `α ≤ 1/2`. -/
lemma prod_le_exp_sum (n : ℕ) {α : ℝ} (hα : α ≤ 1 / 2) :
    ∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (α - 1))⁻¹ ≤
      Real.exp (4 * ∑ p ∈ n.primeFactors, (p : ℝ) ^ (α - 1)) := by
  rw [mul_sum, Real.exp_sum]
  apply prod_le_prod₀
  · intro p hp
    have : (p : ℝ) ^ (α - 1) < 1 := Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt) (by linarith)
    exact inv_nonneg.mpr (by linarith)
  · intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    apply inv_one_sub_le_exp (by positivity)
    calc (p : ℝ) ^ (α - 1) ≤ (2 : ℝ) ^ (α - 1) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
      _ ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ ≤ 3 / 4 := two_rpow_neg_half_le

/-- `∑_{m=1}^{B} m^{α-1} ≤ B^α / α` for `0 < α ≤ 1`. -/
lemma sum_Icc_rpow_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (B : ℕ) :
    ∑ m ∈ Icc 1 B, (m : ℝ) ^ (α - 1) ≤ (B : ℝ) ^ α / α := by
  induction B with
  | zero => simp [Real.zero_rpow hα.ne']
  | succ B ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hB1 : (0 : ℝ) < (B + 1 : ℕ) := by positivity
    -- Bernoulli: B^α = (B+1)^α (1 - 1/(B+1))^α ≤ (B+1)^α (1 - α/(B+1))
    have hbern : (1 + (-(1 / ((B + 1 : ℕ) : ℝ)))) ^ α ≤ 1 + α * (-(1 / ((B + 1 : ℕ) : ℝ))) :=
      rpow_one_add_le_one_add_mul_self (by
        have : 1 / ((B + 1 : ℕ) : ℝ) ≤ 1 := by
          rw [div_le_one hB1]; exact_mod_cast Nat.succ_pos B
        linarith) hα.le hα1
    have hBeq : (B : ℝ) = ((B + 1 : ℕ) : ℝ) * (1 + (-(1 / ((B + 1 : ℕ) : ℝ)))) := by
      field_simp; push_cast; ring
    have hpow : (B : ℝ) ^ α = ((B + 1 : ℕ) : ℝ) ^ α * (1 + (-(1 / ((B + 1 : ℕ) : ℝ)))) ^ α := by
      have hnn : (0 : ℝ) ≤ 1 + (-(1 / ((B + 1 : ℕ) : ℝ))) := by
        have : 1 / ((B + 1 : ℕ) : ℝ) ≤ 1 := by
          rw [div_le_one hB1]; exact_mod_cast Nat.succ_pos B
        linarith
      conv_lhs => rw [hBeq]
      exact Real.mul_rpow hB1.le hnn
    have hsub : ((B + 1 : ℕ) : ℝ) ^ α * (1 / ((B + 1 : ℕ) : ℝ)) = ((B + 1 : ℕ) : ℝ) ^ (α - 1) := by
      rw [Real.rpow_sub hB1, Real.rpow_one, div_eq_mul_one_div]; ring
    have hmain : (B : ℝ) ^ α ≤ ((B + 1 : ℕ) : ℝ) ^ α - α * ((B + 1 : ℕ) : ℝ) ^ (α - 1) := by
      rw [hpow, ← hsub]
      have h0 : 0 ≤ ((B + 1 : ℕ) : ℝ) ^ α := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hbern h0]
    have hstep : ((B + 1 : ℕ) : ℝ) ^ (α - 1) ≤ (((B + 1 : ℕ) : ℝ) ^ α - (B : ℝ) ^ α) / α := by
      rw [le_div_iff₀ hα]; linarith
    calc ∑ k ∈ Icc 1 B, (k : ℝ) ^ (α - 1) + ((B + 1 : ℕ) : ℝ) ^ (α - 1)
        ≤ (B : ℝ) ^ α / α + (((B + 1 : ℕ) : ℝ) ^ α - (B : ℝ) ^ α) / α := add_le_add ih hstep
      _ = ((B + 1 : ℕ) : ℝ) ^ α / α := by ring

/-- `∑_{p ∣ n} p^{α-1} ≤ L^α (1/α + 2)` when `log n ≤ 2L` and `L ≥ e`. -/
theorem sum_primeFactors_rpow_le {n : ℕ} (hn : n ≠ 0) {L α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hL : Real.exp 1 ≤ L) (hnL : Real.log n ≤ 2 * L) :
    ∑ p ∈ n.primeFactors, (p : ℝ) ^ (α - 1) ≤ L ^ α * (1 / α + 2) := by
  classical
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hL
  have hlogL : 1 ≤ Real.log L := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hL
  set B := ⌊L⌋₊
  rw [← sum_filter_add_sum_filter_not n.primeFactors (fun p => p ≤ B)]
  have hsmall : ∑ p ∈ n.primeFactors.filter (fun p => p ≤ B), (p : ℝ) ^ (α - 1) ≤ L ^ α / α := by
    calc ∑ p ∈ n.primeFactors.filter (fun p => p ≤ B), (p : ℝ) ^ (α - 1)
        ≤ ∑ m ∈ Icc 1 B, (m : ℝ) ^ (α - 1) := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro p hp
            simp only [mem_filter] at hp
            exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp.1).one_lt.le, hp.2⟩
          · intro _ _ _; positivity
      _ ≤ (B : ℝ) ^ α / α := sum_Icc_rpow_le hα hα1 B
      _ ≤ L ^ α / α := by
          gcongr
          exact Nat.floor_le hL0.le
  set Lg := n.primeFactors.filter (fun p => ¬ p ≤ B)
  have hLg : ∀ p ∈ Lg, L < (p : ℝ) := by
    intro p hp
    simp only [Lg, mem_filter, not_le] at hp
    exact (Nat.floor_lt hL0.le).mp hp.2
  have hcard : (Lg.card : ℝ) ≤ 2 * L := by
    have h1 : L ^ Lg.card ≤ ∏ p ∈ Lg, (p : ℝ) := by
      rw [← prod_const]
      exact prod_le_prod₀ (fun _ _ => hL0.le) (fun p hp => (hLg p hp).le)
    have h2 : ∏ p ∈ Lg, (p : ℝ) ≤ n := by
      have h3 : ∏ p ∈ Lg, p ≤ ∏ p ∈ n.primeFactors, p :=
        prod_le_prod_of_subset_of_one_le (filter_subset _ _)
          (fun p hp _ => (Nat.prime_of_mem_primeFactors hp).one_lt.le)
      have h4 : ∏ p ∈ n.primeFactors, p ≤ n :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)
      rw [← Nat.cast_prod]; exact_mod_cast h3.trans h4
    have h5 : (Lg.card : ℝ) * Real.log L ≤ Real.log n := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) (h1.trans h2)
    nlinarith
  have hlarge : ∑ p ∈ Lg, (p : ℝ) ^ (α - 1) ≤ 2 * L ^ α := by
    calc ∑ p ∈ Lg, (p : ℝ) ^ (α - 1) ≤ ∑ p ∈ Lg, L ^ (α - 1) :=
          sum_le_sum (fun p hp => Real.rpow_le_rpow_of_nonpos hL0 (hLg p hp).le (by linarith))
      _ = Lg.card * L ^ (α - 1) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 2 * L * L ^ (α - 1) := by gcongr
      _ = 2 * L ^ α := by
          rw [Real.rpow_sub hL0, Real.rpow_one]; field_simp
  calc _ ≤ L ^ α / α + 2 * L ^ α := add_le_add hsmall hlarge
    _ = L ^ α * (1 / α + 2) := by ring

/-- Rankin's trick for one integer. -/
lemma rankin_one {n : ℕ} {Y α : ℝ} (hY : 0 < Y) (hα : 0 ≤ α) :
    ∑ d ∈ n.divisors.filter (fun d : ℕ => Y < (d : ℝ)), (1 / d : ℝ) ≤
      Y ^ (-α) * ∑ d ∈ n.divisors, (d : ℝ) ^ (α - 1) := by
  rw [mul_sum]
  refine (sum_le_sum (fun d hd => ?_)).trans
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity))
  simp only [mem_filter] at hd
  have hd0 : (0 : ℝ) < d := hY.trans hd.2
  have h1 : (1 / d : ℝ) = (d : ℝ) ^ (-α) * (d : ℝ) ^ (α - 1) := by
    rw [← Real.rpow_add hd0, show -α + (α - 1) = (-1 : ℝ) by ring, Real.rpow_neg_one, one_div]
  rw [h1]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hY hd.2.le (by linarith))
    (by positivity)

/-- **Lemma 7.1** (base case of Theorem D). If every term of the progression is a nonzero integer
`n` with `log n ≤ 2L`, then `Δ(A; Y) ≤ |I| · Y^{-α} · exp(4 L^α (1/α + 2))`. -/
theorem rankin_delta (q : ℕ) (a t0 : ℤ) (len : ℕ) {L Y α : ℝ} (hY : 0 < Y) (hα : 0 < α)
    (hα2 : α ≤ 1 / 2) (hL : Real.exp 1 ≤ L)
    (hA : ∀ t ∈ Ico t0 (t0 + len), a + q * t ≠ 0 ∧ Real.log ((a + q * t).natAbs) ≤ 2 * L) :
    Delta q a (Ico t0 (t0 + len)) Y ≤
      len * (Y ^ (-α) * Real.exp (4 * (L ^ α * (1 / α + 2)))) := by
  unfold Delta
  have hcard : ((Ico t0 (t0 + len)).card : ℝ) = len := by
    rw [Int.card_Ico]; simp
  rw [← hcard, ← nsmul_eq_mul, ← sum_const]
  apply sum_le_sum
  intro t ht
  have hn : (a + q * t).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (hA t ht).1
  refine (rankin_one hY hα.le).trans ?_
  gcongr
  refine (sum_divisors_rpow_le _ hn (by linarith)).trans ((prod_le_exp_sum _ hα2).trans ?_)
  gcongr
  exact sum_primeFactors_rpow_le hn hα (by linarith) hL (hA t ht).2

end ThetaSum
