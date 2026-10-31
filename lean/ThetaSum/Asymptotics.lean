import ThetaSum.TheoremD

/-
The conditions `Good γ₀ L` and the final inequality `Bnd γ₀ L J ≤ exp(-γ₀ κ / 4)` hold for all
large `L`; then **Theorem D**.
-/

open Finset Filter

namespace ThetaSum

lemma ev_log_pow_le (k : ℕ) (C : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ L : ℝ in atTop, C * Real.log L ^ k ≤ L ^ γ := by
  have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hγ).def (c := 1 / (|C| + 1)) (by positivity)
  filter_upwards [h, eventually_ge_atTop 1] with L h1 hL1
  have hl : 0 ≤ Real.log L := Real.log_nonneg hL1
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
    Real.rpow_natCast] at h1
  have hk : 0 ≤ Real.log L ^ k := by positivity
  have h2 : (|C| + 1) * Real.log L ^ k ≤ L ^ γ := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)] at h1; linarith
  have h3 : C * Real.log L ^ k ≤ (|C| + 1) * Real.log L ^ k :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) hk
  linarith

lemma ev_rpow_le (C : ℝ) {a b : ℝ} (hab : a < b) : ∀ᶠ L : ℝ in atTop, C * L ^ a ≤ L ^ b := by
  have ht : Tendsto (fun L : ℝ => L ^ (-(b - a))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  have h := (ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (|C| + 1) by positivity)))
  filter_upwards [h, eventually_gt_atTop 0] with L h1 hL0
  have hsplit : L ^ a = L ^ (-(b - a)) * L ^ b := by
    rw [← Real.rpow_add hL0]; ring_nf
  have h2 : (|C| + 1) * L ^ (-(b - a)) ≤ 1 := by
    rw [lt_div_iff₀ (by positivity)] at h1; linarith
  have hLb : 0 ≤ L ^ b := by positivity
  have hLa : 0 ≤ L ^ a := by positivity
  calc C * L ^ a ≤ (|C| + 1) * L ^ a :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) hLa
    _ = ((|C| + 1) * L ^ (-(b - a))) * L ^ b := by rw [hsplit]; ring
    _ ≤ 1 * L ^ b := mul_le_mul_of_nonneg_right h2 hLb
    _ = L ^ b := one_mul _

lemma log_succ_le_two_log {L : ℝ} (hL : 2 ≤ L) : Real.log (L + 1) ≤ 2 * Real.log L := by
  rw [← Real.log_rpow (by linarith), show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact Real.log_le_log (by linarith) (by nlinarith)

lemma log_succ_le_self {L : ℝ} (hL : 0 ≤ L) : Real.log (L + 1) ≤ L := by
  have := Real.log_le_sub_one_of_pos (show 0 < L + 1 by linarith); linarith

lemma JJ_spec {γ₀ : ℝ} (hγ : 0 < γ₀) : 1 ≤ γ₀ * JJ γ₀ := by
  have : 1 / γ₀ ≤ (JJ γ₀ : ℝ) := Nat.le_ceil _
  rw [div_le_iff₀ hγ] at this; linarith

lemma kap_div_uu {γ₀ L : ℝ} (hL : 0 < L) (hℓ : 0 < Real.log (L + 1)) :
    kap γ₀ L / uu γ₀ L = 4 * Real.log (L + 1) := by
  have hk : 0 < kap γ₀ L := Real.rpow_pos_of_pos hL _
  simp only [uu]; field_simp

/-- `2L / u^J ≤ 2 (4 log(L+1))^J`. -/
lemma first_xb_le {γ₀ L : ℝ} (hγ : 0 < γ₀) (hL : 1 ≤ L) (hℓ : 0 < Real.log (L + 1)) :
    2 * L / uu γ₀ L ^ JJ γ₀ ≤ 2 * (4 * Real.log (L + 1)) ^ JJ γ₀ := by
  have hL0 : 0 < L := by linarith
  have hk : 0 < kap γ₀ L := Real.rpow_pos_of_pos hL0 _
  have hkJ : L ≤ kap γ₀ L ^ JJ γ₀ := by
    simp only [kap]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    calc L = L ^ (1 : ℝ) := (Real.rpow_one L).symm
      _ ≤ L ^ (γ₀ * JJ γ₀) := Real.rpow_le_rpow_of_exponent_le hL (JJ_spec hγ)
  have hu : uu γ₀ L ^ JJ γ₀ = kap γ₀ L ^ JJ γ₀ / (4 * Real.log (L + 1)) ^ JJ γ₀ := by
    simp only [uu]; rw [div_pow]
  rw [hu, div_div_eq_mul_div, div_le_iff₀ (by positivity)]
  have h4 : 0 ≤ (4 * Real.log (L + 1)) ^ JJ γ₀ := by positivity
  nlinarith

lemma scale_le {γ x y : ℝ} (hγ : 0 < γ) {k : ℝ} (hk : 0 < k) (h : k / γ * x ≤ y) :
    x ≤ γ / k * y := by
  have e : γ / k * (k / γ * x) = x := by field_simp
  rw [← e]; exact mul_le_mul_of_nonneg_left h (by positivity)

/-- `Good γ₀ L` from explicit inequalities between `log L`, constants and `L^γ₀`. -/
theorem good_of {γ₀ L : ℝ} (hγ : 0 < γ₀) (hLe : Real.exp 1 ≤ L) (hL3 : 3 ≤ L)
    (h1 : 8 * (1 + 16 / γ₀) * Real.log L ≤ L ^ γ₀)
    (h2 : 2 * JJ γ₀ * Real.log 2 ≤ L ^ γ₀)
    (h3 : 2 * 8 ^ JJ γ₀ * Real.log L ^ JJ γ₀ ≤ γ₀ / 48 * L ^ γ₀)
    (h4 : 2 * Real.log 2 ≤ γ₀ / 48 * L ^ γ₀)
    (h5 : 16 * Real.log L ≤ γ₀ / 48 * L ^ γ₀) : Good γ₀ L := by
  have hL0 : 0 < L := by linarith
  have hlam : 1 ≤ Real.log L := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hLe
  have hℓ1 : 1 ≤ Real.log (L + 1) := by
    have := Real.log_le_log hL0 (show L ≤ L + 1 by linarith); linarith
  have hℓ0 : 0 < Real.log (L + 1) := by linarith
  have hℓ2 : Real.log (L + 1) ≤ 2 * Real.log L := log_succ_le_two_log (by linarith)
  have hκ : kap γ₀ L = L ^ γ₀ := rfl
  refine ⟨hLe, hℓ1, ?_, ?_, ?_⟩
  · show 1 + 16 / γ₀ ≤ kap γ₀ L / (4 * Real.log (L + 1))
    rw [le_div_iff₀ (by positivity), hκ]
    have hpos : 0 ≤ 1 + 16 / γ₀ := by positivity
    calc (1 + 16 / γ₀) * (4 * Real.log (L + 1)) ≤ (1 + 16 / γ₀) * (4 * (2 * Real.log L)) :=
          mul_le_mul_of_nonneg_left (by linarith) hpos
      _ = 8 * (1 + 16 / γ₀) * Real.log L := by ring
      _ ≤ L ^ γ₀ := h1
  · rw [hκ]; linarith
  · show 2 * L / uu γ₀ L ^ JJ γ₀ + 2 * (Real.log 2 + kap γ₀ L / uu γ₀ L) ≤ γ₀ / 16 * kap γ₀ L
    rw [kap_div_uu hL0 hℓ0, hκ]
    have hfx := first_xb_le hγ (by linarith : (1 : ℝ) ≤ L) hℓ0
    have hpow : (4 * Real.log (L + 1)) ^ JJ γ₀ ≤ 8 ^ JJ γ₀ * Real.log L ^ JJ γ₀ := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) _
    have : 2 * L / uu γ₀ L ^ JJ γ₀ ≤ 2 * 8 ^ JJ γ₀ * Real.log L ^ JJ γ₀ := by
      calc 2 * L / uu γ₀ L ^ JJ γ₀ ≤ 2 * (4 * Real.log (L + 1)) ^ JJ γ₀ := hfx
        _ ≤ 2 * (8 ^ JJ γ₀ * Real.log L ^ JJ γ₀) := by linarith
        _ = 2 * 8 ^ JJ γ₀ * Real.log L ^ JJ γ₀ := by ring
    linarith

/-- The constant in the final estimate. -/
noncomputable def K0 (γ₀ : ℝ) : ℝ :=
  Real.log (JJ γ₀ + 1) + JJ γ₀ * Real.log 13 + γ₀ / 2 * JJ γ₀ * Real.log 2 +
    Real.log (105 * 2 ^ JJ γ₀)

/-- The final inequality `Bnd ≤ exp(-γ₀ κ / 4)` from explicit inequalities. -/
theorem bnd_of {γ₀ L : ℝ} (hγ : 0 < γ₀) (hγ1 : γ₀ < 1) (hLe : Real.exp 1 ≤ L) (hL3 : 3 ≤ L)
    (h6 : K0 γ₀ ≤ γ₀ / 16 * L ^ γ₀)
    (h7 : ((JJ γ₀ : ℝ) + 1) * Real.log L ≤ γ₀ / 16 * L ^ γ₀)
    (h8 : 4 * (2 / γ₀ + 2) * L ^ (γ₀ / 2) ≤ γ₀ / 16 * L ^ γ₀) :
    Bnd γ₀ L (JJ γ₀) ≤ Real.exp (-(γ₀ / 4 * kap γ₀ L)) := by
  set J := JJ γ₀
  have hL0 : 0 < L := by linarith
  have hlam : 1 ≤ Real.log L := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hLe
  have hℓ1 : 1 ≤ Real.log (L + 1) := by
    have := Real.log_le_log hL0 (show L ≤ L + 1 by linarith); linarith
  have hℓ0 : 0 < Real.log (L + 1) := by linarith
  have hℓL : Real.log (L + 1) ≤ L := log_succ_le_self hL0.le
  have hκ : kap γ₀ L = L ^ γ₀ := rfl
  have hκ0 : 0 ≤ kap γ₀ L := (Real.rpow_pos_of_pos hL0 _).le
  set κ := kap γ₀ L
  set c := cc γ₀ L
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hc : c = 1 + 2 * L + 2 * Real.log 2 + 8 * Real.log (L + 1) := by
    show 1 + (2 * L / uu γ₀ L ^ 0 + 2 * (Real.log 2 + kap γ₀ L / uu γ₀ L)) = _
    rw [pow_zero, div_one, kap_div_uu hL0 hℓ0]; ring
  have hc0 : 1 ≤ c := by rw [hc]; linarith
  have hc13 : c ≤ 13 * L := by rw [hc]; linarith
  set A : ℝ := γ₀ / 2 * J * Real.log 2 + 4 * (L ^ (γ₀ / 2) * (2 / γ₀ + 2))
  have hA0 : 0 ≤ A := by positivity
  have hEb : Eb γ₀ L = Real.exp (-(7 * γ₀ / 16 * κ)) * Real.exp A := by
    show Real.exp (γ₀ / 16 * κ - γ₀ / 2 * κ + γ₀ / 2 * J * Real.log 2) *
      Real.exp (4 * (L ^ (γ₀ / 2) * (1 / (γ₀ / 2) + 2))) = _
    rw [← Real.exp_add, ← Real.exp_add, show 1 / (γ₀ / 2) = 2 / γ₀ by field_simp]
    congr 1
    simp only [A]; ring
  have hE1 : E1 γ₀ L ≤ Real.exp (-(7 * γ₀ / 16 * κ)) * (8 * c * 2 ^ J) := by
    show 8 * c * 2 ^ J * Real.exp (-(κ / 2)) ≤ _
    rw [mul_comm (Real.exp (-(7 * γ₀ / 16 * κ)))]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have : 7 * γ₀ / 16 * κ ≤ 1 / 2 * κ := mul_le_mul_of_nonneg_right (by linarith) hκ0
    linarith
  set E := Real.exp A
  set B : ℝ := 2 ^ J * L
  have hE : 1 ≤ E := Real.one_le_exp hA0
  have hB : 1 ≤ B := by
    have : (1 : ℝ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
    nlinarith
  have hcB : 8 * c * 2 ^ J ≤ 104 * B := by
    have h2J : (0 : ℝ) ≤ 2 ^ J := by positivity
    have := mul_le_mul_of_nonneg_left hc13 (show (0 : ℝ) ≤ 8 * 2 ^ J by positivity)
    calc 8 * c * 2 ^ J = 8 * 2 ^ J * c := by ring
      _ ≤ 8 * 2 ^ J * (13 * L) := this
      _ = 104 * B := by simp only [B]; ring
  have hM : E + 8 * c * 2 ^ J ≤ Real.exp (A + Real.log (105 * 2 ^ J) + Real.log L) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log (by positivity), Real.exp_log hL0]
    have ha : E ≤ E * B := le_mul_of_one_le_right (by linarith) hB
    have hb : B ≤ E * B := le_mul_of_one_le_left (by linarith) hE
    have e : E * (105 * 2 ^ J) * L = E * B + 104 * (E * B) := by simp only [B]; ring
    rw [e]; linarith
  have hsum : Eb γ₀ L + E1 γ₀ L ≤
      Real.exp (-(7 * γ₀ / 16 * κ)) * Real.exp (A + Real.log (105 * 2 ^ J) + Real.log L) := by
    rw [hEb]
    calc Real.exp (-(7 * γ₀ / 16 * κ)) * E + E1 γ₀ L
        ≤ Real.exp (-(7 * γ₀ / 16 * κ)) * E + Real.exp (-(7 * γ₀ / 16 * κ)) * (8 * c * 2 ^ J) := by
          linarith
      _ = Real.exp (-(7 * γ₀ / 16 * κ)) * (E + 8 * c * 2 ^ J) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hM (by positivity)
  have hpre : ((J : ℝ) + 1) * c ^ J ≤
      Real.exp (Real.log (J + 1) + J * (Real.log 13 + Real.log L)) := by
    rw [Real.exp_add, Real.exp_log (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [← Real.log_mul (by norm_num) hL0.ne', ← Real.log_pow, Real.exp_log (by positivity)]
    exact pow_le_pow_left₀ (by linarith) hc13 J
  have hexp : Real.log (J + 1) + J * (Real.log 13 + Real.log L) +
      (A + Real.log (105 * 2 ^ J) + Real.log L) ≤ 3 * γ₀ / 16 * κ := by
    have e : Real.log (J + 1) + J * (Real.log 13 + Real.log L) +
        (A + Real.log (105 * 2 ^ J) + Real.log L) =
        K0 γ₀ + ((J : ℝ) + 1) * Real.log L + 4 * (2 / γ₀ + 2) * L ^ (γ₀ / 2) := by
      simp only [K0, A, J]; ring
    rw [e, hκ]; linarith
  have hBnd0 : 0 ≤ Eb γ₀ L + E1 γ₀ L := by
    have : 0 ≤ Eb γ₀ L := by unfold Eb; positivity
    have : 0 ≤ E1 γ₀ L := by
      unfold E1; have : 0 ≤ cc γ₀ L := by linarith
      positivity
    linarith
  calc Bnd γ₀ L J = ((J : ℝ) + 1) * c ^ J * (Eb γ₀ L + E1 γ₀ L) := rfl
    _ ≤ Real.exp (Real.log (J + 1) + J * (Real.log 13 + Real.log L)) *
          (Real.exp (-(7 * γ₀ / 16 * κ)) * Real.exp (A + Real.log (105 * 2 ^ J) + Real.log L)) :=
        mul_le_mul hpre hsum hBnd0 (by positivity)
    _ = Real.exp (Real.log (J + 1) + J * (Real.log 13 + Real.log L) +
          (A + Real.log (105 * 2 ^ J) + Real.log L) - 7 * γ₀ / 16 * κ) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-(γ₀ / 4 * κ)) := by
        apply Real.exp_le_exp.mpr; linarith

theorem eventually_good {γ₀ : ℝ} (hγ : 0 < γ₀) (hγ1 : γ₀ < 1) :
    ∀ᶠ L : ℝ in atTop, Good γ₀ L ∧
      Bnd γ₀ L (JJ γ₀) ≤ Real.exp (-(γ₀ / 4 * kap γ₀ L)) := by
  set J := JJ γ₀
  have e1 := ev_log_pow_le 1 (8 * (1 + 16 / γ₀)) hγ
  have e2 := ev_rpow_le (2 * J * Real.log 2) hγ
  have e3 := ev_log_pow_le J (48 / γ₀ * (2 * 8 ^ J)) hγ
  have e4 := ev_rpow_le (48 / γ₀ * (2 * Real.log 2)) hγ
  have e5 := ev_log_pow_le 1 (48 / γ₀ * 16) hγ
  have e6 := ev_rpow_le (16 / γ₀ * K0 γ₀) hγ
  have e7 := ev_log_pow_le 1 (16 / γ₀ * ((J : ℝ) + 1)) hγ
  have e8 := ev_rpow_le (16 / γ₀ * (4 * (2 / γ₀ + 2))) (show γ₀ / 2 < γ₀ by linarith)
  filter_upwards [e1, e2, e3, e4, e5, e6, e7, e8, eventually_ge_atTop (Real.exp 1),
    eventually_ge_atTop (3 : ℝ)] with L h1 h2 h3 h4 h5 h6 h7 h8 hLe hL3
  simp only [Real.rpow_zero, mul_one, pow_one] at h1 h2 h3 h4 h5 h6 h7 h8
  rw [mul_assoc] at h3 h5 h7 h8
  refine ⟨good_of hγ hLe hL3 h1 h2 (scale_le hγ (by norm_num) h3) (scale_le hγ (by norm_num) h4)
      (scale_le hγ (by norm_num) h5), ?_⟩
  exact bnd_of hγ hγ1 hLe hL3 (scale_le hγ (by norm_num) h6) (scale_le hγ (by norm_num) h7)
    (scale_le hγ (by norm_num) h8)

/-- **Theorem D.** Let `0 < γ₀ < 1`. There is `L₀` such that for every integer `q ≥ 1` with
`log q ≥ L₀`, putting `T = exp((log q)^γ₀)`: for every integer `a` coprime to `q`, every real
`R ≥ 1`, and every set `I = [t0, t0 + len)` of `len ≤ R` consecutive integers with
`0 < |a + q t| ≤ q²` for all `t ∈ I`,
  `∑_{t ∈ I} ∑_{d ∣ a + q t, d > T R} 1/d ≤ T^{-γ₀/4}`. -/
theorem theorem_D {γ₀ : ℝ} (hγ : 0 < γ₀) (hγ1 : γ₀ < 1) :
    ∃ L₀ : ℝ, ∀ q : ℕ, L₀ ≤ Real.log q →
      ∀ (a t0 : ℤ) (len : ℕ) (R : ℝ), Int.gcd a q = 1 → 1 ≤ R → (len : ℝ) ≤ R →
        (∀ t ∈ Ico t0 (t0 + len), a + q * t ≠ 0 ∧ ((a + q * t).natAbs : ℝ) ≤ (q : ℝ) ^ 2) →
        Delta q a (Ico t0 (t0 + len)) (Real.exp (Real.log q ^ γ₀) * R) ≤
          Real.exp (Real.log q ^ γ₀) ^ (-(γ₀ / 4)) := by
  obtain ⟨L₀, hL₀⟩ := (eventually_good hγ hγ1).exists_forall_of_atTop
  refine ⟨L₀, fun q hq a t0 len R hcop hR1 hlen hA => ?_⟩
  obtain ⟨hG, hB⟩ := hL₀ (Real.log q) hq
  have hRHS : Real.exp (Real.log q ^ γ₀) ^ (-(γ₀ / 4)) =
      Real.exp (-(γ₀ / 4 * kap γ₀ (Real.log q))) := by
    rw [← Real.exp_mul]; congr 1; simp only [kap]; ring
  rw [hRHS]
  by_cases hR : Real.log R ≤ xb γ₀ (Real.log q) 0
  · have h := core q hγ hγ1 hG (JJ γ₀) le_rfl a t0 len R ⟨hcop, hA⟩ hlen hR1
      (by rw [Nat.sub_self]; exact hR)
    rw [Nat.sub_self, pow_zero, div_one] at h
    exact h.trans hB
  · rw [not_le] at hR
    have hLe := hG.1
    have hL0 : 0 < Real.log q := lt_of_lt_of_le (Real.exp_pos 1) hLe
    have hq0 : (0 : ℝ) < q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · rw [h, Nat.cast_zero, Real.log_zero] at hL0; exact absurd hL0 (lt_irrefl 0)
      · exact_mod_cast h
    have hu0 : 0 < uu γ₀ (Real.log q) := by
      have := hG.2.2.1; have : 0 < 16 / γ₀ := by positivity
      linarith
    have hx0 : 2 * Real.log q ≤ xb γ₀ (Real.log q) 0 := by
      show 2 * Real.log q ≤ 2 * Real.log q / uu γ₀ (Real.log q) ^ 0 +
        2 * (Real.log 2 + kap γ₀ (Real.log q) / uu γ₀ (Real.log q))
      rw [pow_zero, div_one]
      have : 0 ≤ kap γ₀ (Real.log q) / uu γ₀ (Real.log q) :=
        div_nonneg (Real.rpow_pos_of_pos hL0 _).le hu0.le
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
      linarith
    have hqR : (q : ℝ) ^ 2 < R := by
      have h2 : Real.log ((q : ℝ) ^ 2) < Real.log R := by
        rw [Real.log_pow]; push_cast; linarith
      exact (Real.log_lt_log_iff (by positivity) (by linarith)).mp h2
    have hTR : R ≤ Real.exp (Real.log q ^ γ₀) * R :=
      le_mul_of_one_le_left (by linarith) (Real.one_le_exp (Real.rpow_nonneg hL0.le _))
    rw [delta_eq_zero_of_large q a _ (fun t ht => (hA t ht).2) (by linarith)]
    positivity

end ThetaSum

#print axioms ThetaSum.theorem_D
