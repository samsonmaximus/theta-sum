import ThetaSum.Recursion

/-
**Theorem D** of the paper: for `0 < γ₀ < 1` there is `L₀` such that for every `q` with
`log q ≥ L₀`, `T = exp((log q)^γ₀)`, every `a` coprime to `q`, every `R ≥ 1` and every interval
`I` of at most `R` integers with `0 < |a + q t| ≤ q²` on `I`,
  `∑_{t ∈ I} ∑_{d ∣ a + qt, d > TR} 1/d ≤ T^{-γ₀/4}`.

Parameters (cf. the paper): `L = log q`, `κ = L^γ₀`, `α = γ₀/2`, `β = γ₀/16` (paper: `γ₀/8`),
`u = κ/(4 log(L+1))` (paper: `⌊κ/(3 log L)⌋`; it need not be an integer), `J = ⌈1/γ₀⌉`
(paper: `⌈1/γ₀⌉ + 1`), and the log-length bounds `x_j = 2L/u^j + 2(log 2 + κ/u)` (an explicit
majorant of the paper's recursively defined `x_j`).
-/

open Finset Filter

namespace ThetaSum

section Params

variable (γ₀ L : ℝ)

noncomputable def kap : ℝ := L ^ γ₀
noncomputable def uu : ℝ := kap γ₀ L / (4 * Real.log (L + 1))
noncomputable def xb (j : ℕ) : ℝ := 2 * L / uu γ₀ L ^ j + 2 * (Real.log 2 + kap γ₀ L / uu γ₀ L)
noncomputable def JJ : ℕ := ⌈1 / γ₀⌉₊
noncomputable def cc : ℝ := 1 + xb γ₀ L 0
noncomputable def Eb : ℝ :=
  Real.exp (γ₀ / 16 * kap γ₀ L - γ₀ / 2 * kap γ₀ L + γ₀ / 2 * JJ γ₀ * Real.log 2) *
    Real.exp (4 * (L ^ (γ₀ / 2) * (1 / (γ₀ / 2) + 2)))
noncomputable def E1 : ℝ := 8 * cc γ₀ L * 2 ^ JJ γ₀ * Real.exp (-(kap γ₀ L / 2))
noncomputable def Bnd (i : ℕ) : ℝ := (i + 1) * cc γ₀ L ^ i * (Eb γ₀ L + E1 γ₀ L)

/-- The conditions on `L` (all true for `L` large in terms of `γ₀`). -/
def Good : Prop :=
  Real.exp 1 ≤ L ∧ 1 ≤ Real.log (L + 1) ∧ 1 + 16 / γ₀ ≤ uu γ₀ L ∧
    (JJ γ₀ : ℝ) * Real.log 2 ≤ kap γ₀ L / 2 ∧ xb γ₀ L (JJ γ₀) ≤ γ₀ / 16 * kap γ₀ L

end Params

lemma delta_eq_zero_of_large (q : ℕ) (a : ℤ) (I : Finset ℤ) {Y : ℝ}
    (hA : ∀ t ∈ I, ((a + q * t).natAbs : ℝ) ≤ (q : ℝ) ^ 2) (hY : (q : ℝ) ^ 2 < Y) :
    Delta q a I Y = 0 := by
  unfold Delta
  apply sum_eq_zero
  intro t ht
  apply sum_eq_zero
  intro d hd
  exfalso
  simp only [mem_filter, Nat.mem_divisors] at hd
  have h1 : (d : ℝ) ≤ (a + q * t).natAbs := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hd.1.2) hd.1.1
  linarith [hA t ht]

/-- The recursion, for parameters satisfying `Good`. -/
theorem core (q : ℕ) {γ₀ : ℝ} (hγ : 0 < γ₀) (hγ1 : γ₀ < 1) (hG : Good γ₀ (Real.log q)) :
    ∀ i ≤ JJ γ₀, ∀ (a t0 : ℤ) (len : ℕ) (R : ℝ), Adm q a (Ico t0 (t0 + len)) →
      (len : ℝ) ≤ R → 1 ≤ R → Real.log R ≤ xb γ₀ (Real.log q) (JJ γ₀ - i) →
      Delta q a (Ico t0 (t0 + len)) (Real.exp (kap γ₀ (Real.log q)) / 2 ^ (JJ γ₀ - i) * R) ≤
        Bnd γ₀ (Real.log q) i := by
  obtain ⟨hL, hL1, hu, hJ, hxJ⟩ := hG
  set L := Real.log q
  set κ := kap γ₀ L
  set u := uu γ₀ L
  set J := JJ γ₀
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hL
  have hκ0 : 0 < κ := Real.rpow_pos_of_pos hL0 _
  have hℓ0 : 0 < Real.log (L + 1) := by linarith
  have h16 : 16 < 16 / γ₀ := by rw [lt_div_iff₀ hγ]; linarith
  have hu2 : 2 ≤ u := by linarith
  have huβ : 1 ≤ (u - 1) * (γ₀ / 16) := by
    have : 16 / γ₀ ≤ u - 1 := by linarith
    rw [div_le_iff₀ hγ] at this; nlinarith
  have hθ : 4 * Real.log (L + 1) * u ≤ κ := by
    simp only [u, uu]; rw [mul_div_cancel₀ _ (by positivity)]
  have hxrec : ∀ j : ℕ, Real.log 2 + (κ + xb γ₀ L j) / u ≤ xb γ₀ L (j + 1) := by
    intro j
    simp only [xb]
    have hu0 : 0 < u := by linarith
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
  have hxmono : ∀ j : ℕ, xb γ₀ L j ≤ xb γ₀ L 0 := by
    intro j
    simp only [xb, pow_zero, div_one]
    have : 2 * L / u ^ j ≤ 2 * L := div_le_self (by positivity) (one_le_pow₀ (by linarith))
    linarith
  have hc1 : 1 ≤ cc γ₀ L := by
    simp only [cc]
    have := hxmono 0
    have : 0 ≤ xb γ₀ L 0 := by
      simp only [xb]; have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); positivity
    linarith
  have hEb0 : 0 ≤ Eb γ₀ L := by unfold Eb; positivity
  have hE10 : 0 ≤ E1 γ₀ L := by
    unfold E1
    have : 0 ≤ cc γ₀ L := by linarith
    positivity
  have hBnd0 : ∀ i, 0 ≤ Bnd γ₀ L i := fun i => by
    unfold Bnd; have : 0 ≤ cc γ₀ L := by linarith
    positivity
  have hEbB : ∀ i, Eb γ₀ L ≤ Bnd γ₀ L i := by
    intro i
    unfold Bnd
    have h1 : 1 ≤ ((i : ℝ) + 1) * cc γ₀ L ^ i := by
      have : (1 : ℝ) ≤ cc γ₀ L ^ i := one_le_pow₀ hc1
      have : (1 : ℝ) ≤ (i : ℝ) + 1 := by have := (Nat.cast_nonneg i : (0 : ℝ) ≤ i); linarith
      nlinarith
    nlinarith
  have hbase : ∀ j ≤ J, ∀ (a t0 : ℤ) (len : ℕ) (R : ℝ), Adm q a (Ico t0 (t0 + len)) →
      (len : ℝ) ≤ R → 1 ≤ R → Real.log R ≤ γ₀ / 16 * κ →
      Delta q a (Ico t0 (t0 + len)) (Real.exp κ / 2 ^ j * R) ≤ Eb γ₀ L := by
    intro j hj a t0 len R hA hlen hR hRb
    have := base_level q (α := γ₀ / 2) (β := γ₀ / 16) (κ := κ) J j hj (by linarith) (by linarith)
      hL a t0 len R hA hlen hR hRb
    exact this
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
    by_cases hRb : Real.log R ≤ γ₀ / 16 * κ
    · exact (hbase j hjJ a t0 len R hA hlen hR hRb).trans (hEbB _)
    · rw [not_le] at hRb
      have hjlog : (j : ℝ) * Real.log 2 ≤ κ / 2 := by
        have : (j : ℝ) ≤ J := by exact_mod_cast hjJ
        have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
        nlinarith
      have IH : ∀ (a' : ℤ) (m : ℕ) (R' : ℝ), Adm q a' (Ico 0 m) → (m : ℝ) ≤ R' → 1 ≤ R' →
          Real.log R' ≤ xb γ₀ L (j + 1) →
          Delta q a' (Ico 0 m) (Real.exp κ / 2 ^ (j + 1) * R') ≤ Bnd γ₀ L i := by
        intro a' m R' hA' hm hR' hlog
        rw [hj1] at hlog ⊢
        have := ih (by omega) a' 0 m R' (by simpa using hA') hm hR' hlog
        simpa using this
      have hstep := rec_step q (u := u) (β := γ₀ / 16) (b := Bnd γ₀ L i) (xj := xb γ₀ L j)
        (xj1 := xb γ₀ L (j + 1)) j hL1 hL0.le (by linarith) huβ hκ0.le hjlog hθ (hxrec j)
        (hBnd0 i) IH a t0 len R hA hlen hR hRb hRx
      refine hstep.trans ?_
      have hx0 : 1 + xb γ₀ L j ≤ cc γ₀ L := by simp only [cc]; linarith [hxmono j]
      have h2j : (2 : ℝ) ^ j ≤ 2 ^ J := pow_le_pow_right₀ (by norm_num) hjJ
      have hfirst : 8 * (1 + xb γ₀ L j) * 2 ^ j * Real.exp (-(κ / 2)) ≤ E1 γ₀ L := by
        unfold E1
        have : 0 ≤ 1 + xb γ₀ L j := by
          have : 0 ≤ xb γ₀ L j := by
            simp only [xb]; have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
            have : 0 < u := by linarith
            positivity
          linarith
        gcongr
      have hsecond : (1 + xb γ₀ L j) * Bnd γ₀ L i ≤ cc γ₀ L * Bnd γ₀ L i :=
        mul_le_mul_of_nonneg_right hx0 (hBnd0 i)
      have hrec : E1 γ₀ L + cc γ₀ L * Bnd γ₀ L i ≤ Bnd γ₀ L (i + 1) := by
        have e : Bnd γ₀ L (i + 1) = cc γ₀ L * Bnd γ₀ L i + cc γ₀ L ^ (i + 1) * (Eb γ₀ L + E1 γ₀ L) := by
          unfold Bnd; push_cast; ring
        have hpow : (1 : ℝ) ≤ cc γ₀ L ^ (i + 1) := one_le_pow₀ hc1
        have h3 : 1 * (Eb γ₀ L + E1 γ₀ L) ≤ cc γ₀ L ^ (i + 1) * (Eb γ₀ L + E1 γ₀ L) :=
          mul_le_mul_of_nonneg_right hpow (by linarith)
        rw [e]; linarith
      linarith

end ThetaSum
