import ThetaSum.Asymptotics

/-
**Theorem D\*** of the paper: the conclusion of Theorem D for much smaller thresholds `T`.

If `log log q ≥ 1000` and `log T ≥ (log log q)^3`, then for every admissible progression
`A = {a + q t : t ∈ I}` (`gcd(a,q) = 1`, `0 < |a + q t| ≤ q²`) of length at most `R ≥ 1`,
  `∑_{t ∈ I} ∑_{d ∣ a + q t, d > T R} 1/d ≤ exp(-log T / (4 log log q))`.

The recursion of Theorem D is run with abstract parameters (`core_gen`), and then with
`L = log q`, `ℓ = log L`, `κ = log T`, `α = 1/ℓ`, `β = 1/(16 log(L+1))`, `u = κ/(4 log(L+1))`,
`J = ⌈ℓ/4⌉`.  The threshold `log log q ≥ 1000` is explicit (and far from optimal).
-/

open Finset Filter

namespace ThetaSum

section ParamsG

variable (L κ u α β : ℝ) (J : ℕ)

noncomputable def xg (j : ℕ) : ℝ := 2 * L / u ^ j + 2 * (Real.log 2 + κ / u)
noncomputable def ccg : ℝ := 1 + xg L κ u 0
noncomputable def Ebg : ℝ :=
  Real.exp (β * κ - α * κ + α * J * Real.log 2) * Real.exp (4 * (L ^ α * (1 / α + 2)))
noncomputable def E1g : ℝ := 8 * ccg L κ u * 2 ^ J * Real.exp (-(κ / 2))
noncomputable def Bndg (i : ℕ) : ℝ :=
  (i + 1) * ccg L κ u ^ i * (Ebg L κ α β J + E1g L κ u J)

end ParamsG

/-- The recursion of Theorem D for abstract parameters. -/
theorem core_gen (q : ℕ) {κ u α β : ℝ} (J : ℕ) (hα : 0 < α) (hα2 : α ≤ 1 / 2)
    (hL : Real.exp 1 ≤ Real.log q) (hL1 : 1 ≤ Real.log (Real.log q + 1))
    (hu2 : 2 ≤ u) (huβ : 1 ≤ (u - 1) * β) (hκ0 : 0 < κ)
    (hθ : 4 * Real.log (Real.log q + 1) * u ≤ κ)
    (hJ : (J : ℝ) * Real.log 2 ≤ κ / 2) (hxJ : xg (Real.log q) κ u J ≤ β * κ) :
    ∀ i ≤ J, ∀ (a t0 : ℤ) (len : ℕ) (R : ℝ), Adm q a (Ico t0 (t0 + len)) →
      (len : ℝ) ≤ R → 1 ≤ R → Real.log R ≤ xg (Real.log q) κ u (J - i) →
      Delta q a (Ico t0 (t0 + len)) (Real.exp κ / 2 ^ (J - i) * R) ≤
        Bndg (Real.log q) κ u α β J i := by
  set L := Real.log q
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hL
  have hu0 : 0 < u := by linarith
  have hxrec : ∀ j : ℕ, Real.log 2 + (κ + xg L κ u j) / u ≤ xg L κ u (j + 1) := by
    intro j
    simp only [xg]
    have hpj : 0 < u ^ j := by positivity
    rw [pow_succ]
    have hA : 0 ≤ Real.log 2 + κ / u := by
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); positivity
    have key : (κ + (2 * L / u ^ j + 2 * (Real.log 2 + κ / u))) / u =
        2 * L / (u ^ j * u) + κ / u + 2 * (Real.log 2 + κ / u) / u := by
      field_simp
      ring
    rw [key]
    have h2u : 2 * (Real.log 2 + κ / u) / u ≤ Real.log 2 + κ / u := by
      rw [div_le_iff₀ hu0]; nlinarith
    linarith
  have hxnn : ∀ j : ℕ, 0 ≤ xg L κ u j := by
    intro j
    simp only [xg]; have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); positivity
  have hxmono : ∀ j : ℕ, xg L κ u j ≤ xg L κ u 0 := by
    intro j
    simp only [xg, pow_zero, div_one]
    have : 2 * L / u ^ j ≤ 2 * L := div_le_self (by positivity) (one_le_pow₀ (by linarith))
    linarith
  have hc1 : 1 ≤ ccg L κ u := by
    simp only [ccg]; linarith [hxnn 0]
  have hEb0 : 0 ≤ Ebg L κ α β J := by unfold Ebg; positivity
  have hE10 : 0 ≤ E1g L κ u J := by
    unfold E1g
    have : 0 ≤ ccg L κ u := by linarith
    positivity
  have hBnd0 : ∀ i, 0 ≤ Bndg L κ u α β J i := fun i => by
    unfold Bndg; have : 0 ≤ ccg L κ u := by linarith
    positivity
  have hEbB : ∀ i, Ebg L κ α β J ≤ Bndg L κ u α β J i := by
    intro i
    unfold Bndg
    have h1 : 1 ≤ ((i : ℝ) + 1) * ccg L κ u ^ i := by
      have : (1 : ℝ) ≤ ccg L κ u ^ i := one_le_pow₀ hc1
      have : (1 : ℝ) ≤ (i : ℝ) + 1 := by have := (Nat.cast_nonneg i : (0 : ℝ) ≤ i); linarith
      nlinarith
    nlinarith
  have hbase : ∀ j ≤ J, ∀ (a t0 : ℤ) (len : ℕ) (R : ℝ), Adm q a (Ico t0 (t0 + len)) →
      (len : ℝ) ≤ R → 1 ≤ R → Real.log R ≤ β * κ →
      Delta q a (Ico t0 (t0 + len)) (Real.exp κ / 2 ^ j * R) ≤ Ebg L κ α β J := by
    intro j hj a t0 len R hA hlen hR hRb
    exact base_level q (α := α) (β := β) (κ := κ) J j hj hα hα2 hL a t0 len R hA hlen hR hRb
  intro i
  induction i with
  | zero =>
    intro _ a t0 len R hA hlen hR hRx
    simp only [Nat.sub_zero] at hRx ⊢
    exact (hbase J le_rfl a t0 len R hA hlen hR (hRx.trans hxJ)).trans (hEbB 0)
  | succ i ih =>
    intro hi a t0 len R hA hlen hR hRx
    set j := J - (i + 1)
    have hjJ : j ≤ J := Nat.sub_le _ _
    have hj1 : j + 1 = J - i := by omega
    by_cases hRb : Real.log R ≤ β * κ
    · exact (hbase j hjJ a t0 len R hA hlen hR hRb).trans (hEbB _)
    · rw [not_le] at hRb
      have hjlog : (j : ℝ) * Real.log 2 ≤ κ / 2 := by
        have : (j : ℝ) ≤ J := by exact_mod_cast hjJ
        have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
        nlinarith
      have IH : ∀ (a' : ℤ) (m : ℕ) (R' : ℝ), Adm q a' (Ico 0 m) → (m : ℝ) ≤ R' → 1 ≤ R' →
          Real.log R' ≤ xg L κ u (j + 1) →
          Delta q a' (Ico 0 m) (Real.exp κ / 2 ^ (j + 1) * R') ≤ Bndg L κ u α β J i := by
        intro a' m R' hA' hm hR' hlog
        rw [hj1] at hlog ⊢
        have := ih (by omega) a' 0 m R' (by simpa using hA') hm hR' hlog
        simpa using this
      have hstep := rec_step q (u := u) (β := β) (b := Bndg L κ u α β J i) (xj := xg L κ u j)
        (xj1 := xg L κ u (j + 1)) j hL1 hL0.le (by linarith) huβ hκ0.le hjlog hθ (hxrec j)
        (hBnd0 i) IH a t0 len R hA hlen hR hRb hRx
      refine hstep.trans ?_
      have hx0 : 1 + xg L κ u j ≤ ccg L κ u := by simp only [ccg]; linarith [hxmono j]
      have h2j : (2 : ℝ) ^ j ≤ 2 ^ J := pow_le_pow_right₀ (by norm_num) hjJ
      have hfirst : 8 * (1 + xg L κ u j) * 2 ^ j * Real.exp (-(κ / 2)) ≤ E1g L κ u J := by
        unfold E1g
        have : 0 ≤ 1 + xg L κ u j := by linarith [hxnn j]
        gcongr
      have hsecond : (1 + xg L κ u j) * Bndg L κ u α β J i ≤ ccg L κ u * Bndg L κ u α β J i :=
        mul_le_mul_of_nonneg_right hx0 (hBnd0 i)
      have hrec : E1g L κ u J + ccg L κ u * Bndg L κ u α β J i ≤ Bndg L κ u α β J (i + 1) := by
        have e : Bndg L κ u α β J (i + 1) = ccg L κ u * Bndg L κ u α β J i +
            ccg L κ u ^ (i + 1) * (Ebg L κ α β J + E1g L κ u J) := by
          unfold Bndg; push_cast; ring
        have hpow : (1 : ℝ) ≤ ccg L κ u ^ (i + 1) := one_le_pow₀ hc1
        have h3 : 1 * (Ebg L κ α β J + E1g L κ u J) ≤
            ccg L κ u ^ (i + 1) * (Ebg L κ α β J + E1g L κ u J) :=
          mul_le_mul_of_nonneg_right hpow (by linarith)
        rw [e]; linarith
      linarith

/-! ### The parameters of Theorem D\* -/

lemma exp_four_lt : Real.exp 4 < 55 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  calc Real.exp 1 ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 := pow_le_pow_left₀ h0 h.le 4
    _ < 55 := by norm_num

lemma exp_one_lt_three : Real.exp 1 < 3 := by
  have := Real.exp_one_lt_d9; linarith

/-- The final inequality for the parameters of Theorem D\*. -/
theorem bndg_star {L κ : ℝ} (hL0 : 0 < L) (hℓ : 1000 ≤ Real.log L) (hκ : Real.log L ^ 3 ≤ κ) :
    Bndg L κ (κ / (4 * Real.log (L + 1))) (1 / Real.log L) (1 / (16 * Real.log (L + 1)))
      ⌈Real.log L / 4⌉₊ ⌈Real.log L / 4⌉₊ ≤ Real.exp (-(κ / (4 * Real.log L))) := by
  set ℓ := Real.log L
  set ℓ1 := Real.log (L + 1)
  set J := ⌈ℓ / 4⌉₊
  set u := κ / (4 * ℓ1)
  have hℓ0 : 0 < ℓ := by linarith
  have hLe : L = Real.exp ℓ := (Real.exp_log hL0).symm
  have hL1 : 1 ≤ L := by rw [hLe]; exact Real.one_le_exp (by linarith)
  have hL2 : 2 ≤ L := by
    rw [hLe]; have := Real.add_one_le_exp ℓ; linarith
  have hℓ1a : ℓ ≤ ℓ1 := Real.log_le_log hL0 (by linarith)
  have hℓ1b : ℓ1 ≤ 2 * ℓ := log_succ_le_two_log hL2
  have hℓ1L : ℓ1 ≤ L := log_succ_le_self hL0.le
  have hℓ10 : 0 < ℓ1 := by linarith
  have hκ0 : 0 < κ := by
    have : 0 < ℓ ^ 3 := by positivity
    linarith
  have hκu : κ / u = 4 * ℓ1 := by simp only [u]; field_simp
  -- `J` bounds
  have hJlo : ℓ / 4 ≤ (J : ℝ) := Nat.le_ceil _
  have hJhi : (J : ℝ) < ℓ / 4 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  -- `c ≤ 13 L`
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hc : ccg L κ u = 1 + 2 * L + 2 * Real.log 2 + 8 * ℓ1 := by
    simp only [ccg, xg, pow_zero, div_one]; rw [hκu]; ring
  have hc13 : ccg L κ u ≤ 13 * L := by rw [hc]; linarith
  have hc1 : 1 ≤ ccg L κ u := by rw [hc]; linarith
  -- the Rankin factor: `L^{1/ℓ} = e`
  have hLα : L ^ (1 / ℓ) = Real.exp 1 := by
    rw [Real.rpow_def_of_pos hL0]; congr 1; field_simp; rfl
  have hEb : Ebg L κ (1 / ℓ) (1 / (16 * ℓ1)) J ≤
      Real.exp (-(15 / 16 * (κ / ℓ))) * Real.exp (12 * ℓ + 25) := by
    unfold Ebg
    rw [hLα, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : 1 / (16 * ℓ1) * κ ≤ 1 / 16 * (κ / ℓ) := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      have : κ / ℓ * ℓ = κ := by field_simp
      nlinarith
    have h2 : 1 / ℓ * J * Real.log 2 ≤ 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div, div_le_iff₀ hℓ0]
      nlinarith
    have h3 : 4 * (Real.exp 1 * (1 / (1 / ℓ) + 2)) ≤ 12 * ℓ + 24 := by
      rw [one_div_one_div]
      have := exp_one_lt_three
      nlinarith
    have h4 : 1 / ℓ * κ = κ / ℓ := by ring
    linarith
  have hE1 : E1g L κ u J ≤ Real.exp (-(15 / 16 * (κ / ℓ))) * (104 * L * 2 ^ J) := by
    unfold E1g
    have hexp : Real.exp (-(κ / 2)) ≤ Real.exp (-(15 / 16 * (κ / ℓ))) := by
      apply Real.exp_le_exp.mpr
      have : 15 / 16 * (κ / ℓ) ≤ κ / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      linarith
    have h8c : 8 * ccg L κ u * 2 ^ J ≤ 104 * L * 2 ^ J := by
      have : (0 : ℝ) < 2 ^ J := by positivity
      nlinarith
    calc 8 * ccg L κ u * 2 ^ J * Real.exp (-(κ / 2))
        ≤ 104 * L * 2 ^ J * Real.exp (-(15 / 16 * (κ / ℓ))) :=
          mul_le_mul h8c hexp (by positivity) (by positivity)
      _ = _ := by ring
  -- sum of the two
  set X := 104 * L * 2 ^ J * Real.exp (12 * ℓ + 25)
  have hX1 : Real.exp (12 * ℓ + 25) ≤ X := by
    have : (1 : ℝ) ≤ 104 * L * 2 ^ J := by
      have : (1 : ℝ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
      nlinarith
    simp only [X]; nlinarith [Real.exp_pos (12 * ℓ + 25)]
  have hX2 : 104 * L * 2 ^ J ≤ X := by
    have : (1 : ℝ) ≤ Real.exp (12 * ℓ + 25) := Real.one_le_exp (by linarith)
    have : (0 : ℝ) ≤ 104 * L * 2 ^ J := by positivity
    simp only [X]; nlinarith
  have hsum : Ebg L κ (1 / ℓ) (1 / (16 * ℓ1)) J + E1g L κ u J ≤
      Real.exp (-(15 / 16 * (κ / ℓ))) * (2 * X) := by
    have hp : 0 < Real.exp (-(15 / 16 * (κ / ℓ))) := Real.exp_pos _
    nlinarith
  have hlogX : Real.log (2 * X) ≤ 14 * ℓ + 32 := by
    have hX : 2 * X = Real.exp (Real.log 208 + ℓ + J * Real.log 2 + (12 * ℓ + 25)) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num), ← hLe,
        show (J : ℝ) * Real.log 2 = Real.log (2 ^ J) by rw [Real.log_pow],
        Real.exp_log (by positivity)]
      simp only [X]; ring
    rw [hX, Real.log_exp]
    have h208 : Real.log 208 < 6 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have e6 : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
      have h := Real.exp_one_gt_d9
      rw [e6]
      calc (208 : ℝ) < (2.7182818283 : ℝ) ^ 6 := by norm_num
        _ ≤ Real.exp 1 ^ 6 := pow_le_pow_left₀ (by norm_num) h.le 6
    nlinarith
  -- prefactor
  have hpre : ((J : ℝ) + 1) * ccg L κ u ^ J ≤ Real.exp (ℓ ^ 2 / 4 + 2 * ℓ + 4) := by
    have h1 : ((J : ℝ) + 1) ≤ Real.exp J := by linarith [Real.add_one_le_exp (J : ℝ)]
    have h2 : ccg L κ u ^ J ≤ Real.exp (J * (Real.log 13 + ℓ)) := by
      rw [← Real.log_mul (by norm_num) hL0.ne', ← Real.log_pow, Real.exp_log (by positivity)]
      exact pow_le_pow_left₀ (by linarith) hc13 J
    have h13 : Real.log 13 < 3 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have e3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add, ← Real.exp_add]; norm_num
      have := Real.exp_one_gt_d9
      rw [e3]; nlinarith
    calc ((J : ℝ) + 1) * ccg L κ u ^ J ≤ Real.exp J * Real.exp (J * (Real.log 13 + ℓ)) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = Real.exp (J + J * (Real.log 13 + ℓ)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (ℓ ^ 2 / 4 + 2 * ℓ + 4) := by
          apply Real.exp_le_exp.mpr
          have hl13 : 0 ≤ Real.log 13 := Real.log_nonneg (by norm_num)
          have : (J : ℝ) * (Real.log 13 + ℓ) ≤ (ℓ / 4 + 1) * (3 + ℓ) := by
            apply mul_le_mul hJhi.le (by linarith) (by positivity) (by positivity)
          have ex : (ℓ / 4 + 1) * (3 + ℓ) = ℓ ^ 2 / 4 + 7 * ℓ / 4 + 3 := by ring
          linarith
  have hBsum0 : 0 ≤ Ebg L κ (1 / ℓ) (1 / (16 * ℓ1)) J + E1g L κ u J := by
    have : 0 ≤ Ebg L κ (1 / ℓ) (1 / (16 * ℓ1)) J := by unfold Ebg; positivity
    have : 0 ≤ E1g L κ u J := by
      unfold E1g
      have : 0 ≤ ccg L κ u := by linarith
      positivity
    linarith
  have hκℓ : ℓ ^ 2 ≤ κ / ℓ := by
    rw [le_div_iff₀ hℓ0]
    have : ℓ ^ 2 * ℓ = ℓ ^ 3 := by ring
    linarith
  calc Bndg L κ u (1 / ℓ) (1 / (16 * ℓ1)) J J
      = ((J : ℝ) + 1) * ccg L κ u ^ J * (Ebg L κ (1 / ℓ) (1 / (16 * ℓ1)) J + E1g L κ u J) := rfl
    _ ≤ Real.exp (ℓ ^ 2 / 4 + 2 * ℓ + 4) * (Real.exp (-(15 / 16 * (κ / ℓ))) * (2 * X)) :=
        mul_le_mul hpre hsum hBsum0 (by positivity)
    _ = Real.exp ((ℓ ^ 2 / 4 + 2 * ℓ + 4) + -(15 / 16 * (κ / ℓ)) + Real.log (2 * X)) := by
        rw [Real.exp_add ((ℓ ^ 2 / 4 + 2 * ℓ + 4) + -(15 / 16 * (κ / ℓ))) (Real.log (2 * X)),
          Real.exp_add (ℓ ^ 2 / 4 + 2 * ℓ + 4) (-(15 / 16 * (κ / ℓ))),
          Real.exp_log (by positivity)]
        ring
    _ ≤ Real.exp (-(κ / (4 * ℓ))) := by
        apply Real.exp_le_exp.mpr
        have e : κ / (4 * ℓ) = 1 / 4 * (κ / ℓ) := by field_simp
        rw [e]
        have hsq : 1000 * ℓ ≤ ℓ ^ 2 := by
          have := mul_le_mul_of_nonneg_right hℓ hℓ0.le
          rw [sq]; exact this
        linarith

/-- **Theorem D\*** (paper). Let `q` be an integer with `log log q ≥ 1000`, and let `T > 0`
satisfy `log T ≥ (log log q)^3`. For every integer `a` coprime to `q`, every real `R ≥ 1`, and every
set `I = [t0, t0 + len)` of `len ≤ R` consecutive integers with `0 < |a + q t| ≤ q²` on `I`,
  `∑_{t ∈ I} ∑_{d ∣ a + q t, d > T R} 1/d ≤ exp(-log T / (4 log log q))`. -/
theorem theorem_D_star (q : ℕ) (hq : 1000 ≤ Real.log (Real.log q)) (T : ℝ) (hT : 0 < T)
    (hTq : Real.log (Real.log q) ^ 3 ≤ Real.log T)
    (a t0 : ℤ) (len : ℕ) (R : ℝ) (hcop : Int.gcd a q = 1) (hR1 : 1 ≤ R) (hlen : (len : ℝ) ≤ R)
    (hA : ∀ t ∈ Ico t0 (t0 + len), a + q * t ≠ 0 ∧ ((a + q * t).natAbs : ℝ) ≤ (q : ℝ) ^ 2) :
    Delta q a (Ico t0 (t0 + len)) (T * R) ≤
      Real.exp (-(Real.log T / (4 * Real.log (Real.log q)))) := by
  set L := Real.log q
  set ℓ := Real.log L
  set κ := Real.log T
  set ℓ1 := Real.log (L + 1)
  set u := κ / (4 * ℓ1)
  set J := ⌈ℓ / 4⌉₊
  have hℓ0 : 0 < ℓ := by linarith
  -- `L > 0`
  have hL0 : 0 < L := by
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    rcases Nat.eq_zero_or_pos q with h | h
    · exfalso; simp only [L, ℓ, h, Nat.cast_zero, Real.log_zero] at hq; linarith
    · have h1 : (1 : ℝ) ≤ q := by exact_mod_cast h
      have hL : 0 ≤ L := Real.log_nonneg h1
      rcases hL.lt_or_eq with h2 | h2
      · exact h2
      · exfalso; simp only [ℓ, ← h2, Real.log_zero] at hq; linarith
  have hLe : L = Real.exp ℓ := (Real.exp_log hL0).symm
  have hL2 : 2 ≤ L := by rw [hLe]; have := Real.add_one_le_exp ℓ; linarith
  have hLexp : Real.exp 1 ≤ L := by rw [hLe]; exact Real.exp_le_exp.mpr (by linarith)
  have hℓ1a : ℓ ≤ ℓ1 := Real.log_le_log hL0 (by linarith)
  have hℓ1b : ℓ1 ≤ 2 * ℓ := log_succ_le_two_log hL2
  have hℓ10 : 0 < ℓ1 := by linarith
  have hκ0 : 0 < κ := by
    have : 0 < ℓ ^ 3 := by positivity
    linarith
  have hT : T = Real.exp κ := (Real.exp_log hT).symm
  -- `u ≥ ℓ² / 8`
  have hu8 : ℓ ^ 2 / 8 ≤ u := by
    simp only [u]
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have : ℓ ^ 2 * (4 * ℓ1) ≤ ℓ ^ 2 * (8 * ℓ) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have hℓ2 : 125000 ≤ ℓ ^ 2 / 8 := by nlinarith
  have hu2 : 2 ≤ u := by linarith
  have huβ : 1 ≤ (u - 1) * (1 / (16 * ℓ1)) := by
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hθ : 4 * Real.log (L + 1) * u ≤ κ := by
    simp only [u, ℓ1]; rw [mul_div_cancel₀ _ (by positivity)]
  have hJlo : ℓ / 4 ≤ (J : ℝ) := Nat.le_ceil _
  have hJhi : (J : ℝ) < ℓ / 4 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hJ : (J : ℝ) * Real.log 2 ≤ κ / 2 := by
    have : (J : ℝ) * Real.log 2 ≤ ℓ / 4 + 1 := by nlinarith
    nlinarith
  -- `u^J ≥ L`
  have huJ : L ≤ u ^ J := by
    have hu4 : Real.exp 4 ≤ u := by linarith [exp_four_lt]
    calc L = Real.exp ℓ := hLe
      _ ≤ Real.exp (4 * J) := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp 4 ^ J := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ u ^ J := pow_le_pow_left₀ (Real.exp_pos 4).le hu4 J
  have hκu : κ / u = 4 * ℓ1 := by simp only [u]; field_simp
  have hxJ : xg L κ u J ≤ 1 / (16 * ℓ1) * κ := by
    simp only [xg]
    rw [hκu]
    have h1 : 2 * L / u ^ J ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have h2 : ℓ ^ 2 / 32 ≤ 1 / (16 * ℓ1) * κ := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
      have : ℓ ^ 3 ≤ κ := hTq
      nlinarith
    nlinarith
  have hα2 : 1 / ℓ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hL1 : 1 ≤ Real.log (L + 1) := by
    have : 1 ≤ ℓ := by linarith
    linarith
  have hcore := core_gen q (κ := κ) (u := u) (α := 1 / ℓ) (β := 1 / (16 * ℓ1)) J
    (by positivity) hα2 hLexp hL1 hu2 huβ hκ0 hθ hJ hxJ
  have hB := bndg_star (L := L) (κ := κ) hL0 hq hTq
  rw [hT]
  by_cases hR : Real.log R ≤ xg L κ u 0
  · have h := hcore J le_rfl a t0 len R ⟨hcop, hA⟩ hlen hR1 (by rw [Nat.sub_self]; exact hR)
    rw [Nat.sub_self, pow_zero, div_one] at h
    refine h.trans (hB.trans (le_of_eq ?_))
    simp only [κ, ℓ, L]
  · rw [not_le] at hR
    have hx0 : 2 * L ≤ xg L κ u 0 := by
      simp only [xg, pow_zero, div_one]
      have : 0 ≤ κ / u := div_nonneg hκ0.le (by linarith)
      linarith
    have hq0 : (0 : ℝ) < q := by
      have hne : (q : ℝ) ≠ 0 := by
        intro h; simp only [L, h, Real.log_zero] at hL0; exact lt_irrefl 0 hL0
      exact lt_of_le_of_ne (Nat.cast_nonneg q) (Ne.symm hne)
    have hqR : (q : ℝ) ^ 2 < R := by
      have h2 : Real.log ((q : ℝ) ^ 2) < Real.log R := by
        rw [Real.log_pow]; push_cast; linarith
      exact (Real.log_lt_log_iff (by positivity) (by linarith)).mp h2
    have hTR : R ≤ Real.exp κ * R := le_mul_of_one_le_left (by linarith) (Real.one_le_exp hκ0.le)
    rw [delta_eq_zero_of_large q a _ (fun t ht => (hA t ht).2) (by linarith)]
    positivity

end ThetaSum

#print axioms ThetaSum.theorem_D_star
