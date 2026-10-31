import ThetaSum.OneStep

/-
Bounds for the first term of Lemma 7.2 and for the sums `∑ 1/e`, `∑ 1/s`.

* `G_le_rpow`: `G_y(Z) ≤ Z^θ` with `θ = log(N_y + 1)/log y` (for `Z ≥ 1`, `y > 1`). The paper uses
  instead `∑_{i ≤ m} binom(N, i) ≤ (eN/m)^m`; the cruder `≤ (N+1)^m` suffices.
* `dyadic_sum_le`: `∑_{j<J} 2^{-j} G_y(2^{j+1} P) ≤ 4 (2P)^θ` when `θ ≤ 1/2` (this replaces Lemma 7.3).
* `sum_inv_le_one_add_log`: `∑_{e ∈ F} 1/e ≤ 1 + log R` for a set `F` of positive integers `≤ R`.
  The paper bounds these sums by Mertens' `M(y) ≤ e^γ (1 + log y)`; since all the `e` (in case
  `e ≤ R`) and all the `s ∈ S` are at most `R`, the harmonic bound suffices.
-/

open Finset

namespace ThetaSum

lemma sum_pow_le_succ_pow (N m : ℕ) : ∑ i ∈ range (m + 1), N ^ i ≤ (N + 1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, pow_succ (N + 1)]
    have h1 : N ^ (m + 1) ≤ N * (N + 1) ^ m := by
      rw [pow_succ, mul_comm]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    nlinarith

/-- `G_y(Z) ≤ Z^{log(N_y+1)/log y}`. -/
theorem G_le_rpow (X : ℝ) {y Z : ℝ} (hy : 1 < y) (hZ : 1 ≤ Z) :
    G X y Z ≤ Z ^ (Real.log ((Ny X y : ℝ) + 1) / Real.log y) := by
  set N := Ny X y
  set m := ⌊Real.log Z / Real.log y⌋₊
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hlogZ : 0 ≤ Real.log Z := Real.log_nonneg hZ
  have h1 : G X y Z ≤ ((N + 1 : ℕ) : ℝ) ^ m := by
    unfold G
    have : ∑ i ∈ range (m + 1), N.choose i ≤ (N + 1) ^ m :=
      (sum_le_sum (fun i _ => Nat.choose_le_pow N i)).trans (sum_pow_le_succ_pow N m)
    exact_mod_cast this
  have hN1 : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos N
  have h2 : ((N + 1 : ℕ) : ℝ) ^ m ≤ ((N + 1 : ℕ) : ℝ) ^ (Real.log Z / Real.log y) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (Nat.floor_le (div_nonneg hlogZ hlogy.le))
  refine h1.trans (h2.trans (le_of_eq ?_))
  have hZ0 : 0 < Z := by linarith
  rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos hZ0]
  push_cast
  congr 1
  ring

lemma sqrt_two_div_two_le : (2 : ℝ) ^ (1 / 2 : ℝ) / 2 ≤ 3 / 4 := by
  rw [← Real.sqrt_eq_rpow, div_le_iff₀ (by norm_num), Real.sqrt_le_left (by norm_num)]
  norm_num

/-- Replacement for Lemma 7.3: `∑_{j<J} 2^{-j} G_y(2^{j+1} P) ≤ 4 (2P)^θ`, `θ = log(N_y+1)/log y`,
provided `θ ≤ 1/2`. -/
theorem dyadic_sum_le (X : ℝ) {y P : ℝ} (hy : 1 < y) (hP : 1 ≤ P)
    (hθ : Real.log ((Ny X y : ℝ) + 1) / Real.log y ≤ 1 / 2) (J : ℕ) :
    ∑ j ∈ range J, (1 / 2 : ℝ) ^ j * G X y (2 ^ (j + 1) * P) ≤
      4 * (2 * P) ^ (Real.log ((Ny X y : ℝ) + 1) / Real.log y) := by
  set θ := Real.log ((Ny X y : ℝ) + 1) / Real.log y
  have hθ0 : 0 ≤ θ := div_nonneg (Real.log_nonneg (by have := (Ny X y).cast_nonneg (α := ℝ); linarith))
    (Real.log_pos hy).le
  have hterm : ∀ j : ℕ, (1 / 2 : ℝ) ^ j * G X y (2 ^ (j + 1) * P) ≤ (3 / 4 : ℝ) ^ j * (2 * P) ^ θ := by
    intro j
    have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hZ : (1 : ℝ) ≤ 2 ^ (j + 1) * P := by
      have : (1 : ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ (by norm_num)
      nlinarith
    have hG := G_le_rpow X hy hZ
    have hsplit : (2 : ℝ) ^ (j + 1) * P = 2 ^ j * (2 * P) := by ring
    rw [hsplit, Real.mul_rpow (by positivity) (by positivity)] at hG
    have hpow : ((2 : ℝ) ^ j) ^ θ ≤ ((2 : ℝ) ^ (1 / 2 : ℝ)) ^ j := by
      rw [show ((2 : ℝ) ^ (1 / 2 : ℝ)) ^ j = ((2 : ℝ) ^ j) ^ (1 / 2 : ℝ) by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
          ← Real.rpow_mul (by norm_num), mul_comm]]
      exact Real.rpow_le_rpow_of_exponent_le h2j hθ
    calc (1 / 2 : ℝ) ^ j * G X y (2 ^ (j + 1) * P)
        ≤ (1 / 2 : ℝ) ^ j * (((2 : ℝ) ^ (1 / 2 : ℝ)) ^ j * (2 * P) ^ θ) := by
          rw [hsplit]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact hG.trans (mul_le_mul_of_nonneg_right hpow (by positivity))
      _ = ((2 : ℝ) ^ (1 / 2 : ℝ) / 2) ^ j * (2 * P) ^ θ := by
          rw [div_eq_mul_one_div ((2 : ℝ) ^ (1 / 2 : ℝ)) 2, mul_pow]; ring
      _ ≤ (3 / 4 : ℝ) ^ j * (2 * P) ^ θ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) sqrt_two_div_two_le j)
            (by positivity)
  have hgeom : ∑ j ∈ range J, (3 / 4 : ℝ) ^ j ≤ 4 := by
    have h0 : (0 : ℝ) ≤ 3 / 4 := by norm_num
    have h1 : (3 / 4 : ℝ) < 1 := by norm_num
    calc ∑ j ∈ range J, (3 / 4 : ℝ) ^ j ≤ ∑' j, (3 / 4 : ℝ) ^ j :=
          (summable_geometric_of_lt_one h0 h1).sum_le_tsum _ (fun i _ => by positivity)
      _ = 4 := by rw [tsum_geometric_of_lt_one h0 h1]; norm_num
  calc ∑ j ∈ range J, (1 / 2 : ℝ) ^ j * G X y (2 ^ (j + 1) * P)
      ≤ ∑ j ∈ range J, (3 / 4 : ℝ) ^ j * (2 * P) ^ θ := sum_le_sum (fun j _ => hterm j)
    _ = (∑ j ∈ range J, (3 / 4 : ℝ) ^ j) * (2 * P) ^ θ := by rw [sum_mul]
    _ ≤ 4 * (2 * P) ^ θ := by gcongr

/-- `∑_{e ∈ F} 1/e ≤ 1 + log R` for a finite set `F` of positive integers at most `R` (`R ≥ 1`). -/
theorem sum_inv_le_one_add_log {R : ℝ} (hR : 1 ≤ R) (F : Finset ℕ)
    (hF : ∀ e ∈ F, 0 < e ∧ (e : ℝ) ≤ R) : ∑ e ∈ F, (1 / e : ℝ) ≤ 1 + Real.log R := by
  have hsub : F ⊆ Icc 1 ⌊R⌋₊ := fun e he =>
    mem_Icc.mpr ⟨(hF e he).1, Nat.le_floor (hF e he).2⟩
  calc ∑ e ∈ F, (1 / e : ℝ) ≤ ∑ e ∈ Icc 1 ⌊R⌋₊, (1 / e : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = (harmonic ⌊R⌋₊ : ℝ) := by
        rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]
    _ ≤ 1 + Real.log ⌊R⌋₊ := harmonic_le_one_add_log _
    _ ≤ 1 + Real.log R := by
        have h1 : 1 ≤ ⌊R⌋₊ := Nat.le_floor (by exact_mod_cast hR)
        have h1' : (0 : ℝ) < ⌊R⌋₊ := by exact_mod_cast h1
        have h2 := Real.log_le_log h1' (Nat.floor_le (by linarith : (0 : ℝ) ≤ R))
        linarith

/-- `∑_{s ∈ S} 1/s ≤ 1 + log R`. -/
theorem sum_Sset_le {R y : ℝ} (hR : 1 ≤ R) : ∑ s ∈ Sset R y, (1 / s : ℝ) ≤ 1 + Real.log R := by
  apply sum_inv_le_one_add_log hR
  intro s hs
  simp only [Sset, mem_filter, mem_Icc] at hs
  exact ⟨hs.1.1, le_trans (by exact_mod_cast hs.1.2) (Nat.floor_le (by linarith))⟩

/-- Lemma 7.2 with `M = 1 + log R`. -/
theorem one_step_harmonic (q : ℕ) (a t0 : ℤ) (len : ℕ) {X R T' y : ℝ} (J : ℕ)
    (hcop : Int.gcd a q = 1)
    (hA : ∀ t ∈ Ico t0 (t0 + len), a + q * t ≠ 0 ∧ ((a + q * t).natAbs : ℝ) ≤ X)
    (hlen : (len : ℝ) ≤ R) (hT' : 1 ≤ T') (hy : 2 ≤ y) (hyR : y ≤ R)
    (hJ : X ≤ 2 ^ J * (T' * R)) :
    Delta q a (Ico t0 (t0 + len)) (T' * R) ≤
      2 * (1 + Real.log R) / T' * ∑ j ∈ range J, (1 / 2 : ℝ) ^ j * G X y (2 ^ (j + 1) * (T' * R)) +
      ∑ s ∈ Sset R y, (1 / s : ℝ) * DeltaSub q a (Ico t0 (t0 + len)) s (T' * R / s) :=
  one_step_le q a t0 len J hcop hA hlen hT' hy hyR
    (fun F hF => sum_inv_le_one_add_log (by linarith) F
      (fun e he => ⟨(hF e he).1, (hF e he).2.2⟩)) hJ

end ThetaSum
