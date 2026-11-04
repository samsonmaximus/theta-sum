import ThetaSum.LowerHalf

/-!
# A general form of the explicit bound for `R_K(p)`

`one_termG`, `block_kloostG`, `R_boundG`: copies of `one_term`, `block_kloost` (`HeadsBG.lean`) and
`R_bound` (`RBound.lean`) in which
* the Bourgain–Garaev input is assumed only for `N ≥ E₀` (an arbitrary threshold), and
* in the dyadic blocks `[2^j K_*, 2^{j+1} K_*)` the saving `log(2^j K_*/3)^{-3/2}` is kept
  block by block (instead of the uniform `log(K_*/3)^{-3/2}`).
`sum_dyadic_pow` then bounds `∑_{j<J} log(2^j K_*/3)^{-3/2} ≤ 2 (1 + log(J+1)) / √(log(K_*/3))`.
-/

open Finset

namespace ThetaSum

lemma one_termG (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 3 ≤ p) (b : ZMod p) (hb : b ≠ 0)
    (E₀ : ℝ) (hBG : ∀ b : ZMod p, b ≠ 0 → ∀ N : ℕ, E₀ ≤ N → N < p →
      ‖Tsum p b N‖ ≤ bgB C p N)
    (a N' : ℕ) (ha : 6 ≤ a) (h1 : a ≤ 3 * N') (h2 : N' ≤ 2 * a) (h2a : 2 * a < p)
    (hE : E₀ ≤ (a : ℝ) / 3) :
    ‖Tsum p b N'‖ ≤ C * Real.log (Real.log p) ^ 3 * Real.log p *
      Real.log ((a : ℝ) / 3) ^ (-(3 / 2 : ℝ)) * (2 * a) := by
  have ha3 : (1 : ℝ) < (a : ℝ) / 3 := by
    rw [lt_div_iff₀ (by norm_num)]; have : (6 : ℝ) ≤ a := by exact_mod_cast ha
    linarith
  have hN'R : (a : ℝ) / 3 ≤ N' := by
    rw [div_le_iff₀ (by norm_num)]; have : (a : ℝ) ≤ 3 * N' := by exact_mod_cast h1
    linarith
  have hla : 0 < Real.log ((a : ℝ) / 3) := Real.log_pos ha3
  have hlN : Real.log ((a : ℝ) / 3) ≤ Real.log N' := Real.log_le_log (by linarith) hN'R
  have hb' := hBG b hb N' (hE.trans hN'R) (by omega)
  refine hb'.trans ?_
  unfold bgB
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hlp : 0 < Real.log p := Real.log_pos hp1
  have hX : 0 ≤ C * Real.log (Real.log p) ^ 3 * Real.log p := by
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
    have : 1 ≤ Real.log p := by
      rw [← Real.log_exp 1]
      apply Real.log_le_log (Real.exp_pos 1)
      linarith [Real.exp_one_lt_d9]
    have : 0 ≤ Real.log (Real.log p) := Real.log_nonneg this
    positivity
  have hpow : Real.log N' ^ (-(3 / 2 : ℝ)) ≤ Real.log ((a : ℝ) / 3) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hla hlN (by norm_num)
  have hN2 : (N' : ℝ) ≤ 2 * a := by exact_mod_cast h2
  have hpos : 0 ≤ Real.log N' ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  calc C * Real.log (Real.log p) ^ 3 * Real.log p * Real.log N' ^ (-(3 / 2 : ℝ)) * N'
      = (C * Real.log (Real.log p) ^ 3 * Real.log p) * (Real.log N' ^ (-(3 / 2 : ℝ)) * N') := by ring
    _ ≤ (C * Real.log (Real.log p) ^ 3 * Real.log p) *
          (Real.log ((a : ℝ) / 3) ^ (-(3 / 2 : ℝ)) * (2 * a)) := by
        apply mul_le_mul_of_nonneg_left _ hX
        exact mul_le_mul hpow hN2 (Nat.cast_nonneg _) (Real.rpow_nonneg hla.le _)
    _ = _ := by ring

/-- **Block Kloosterman bound** from (HBG): for `6 ≤ a`, `x ≤ b ≤ 2a`, `2a < p` and
`log(a/3) ≥ (log p)^{9/10}/2`, every `c ≢ 0` gives
`‖∑_{k ∈ [a,x), k odd} e(c (2k)^{-1}/p)‖ ≤ 4 · C (log log p)³ (log p) (log(a/3))^{-3/2} (2a)`. -/
theorem block_kloostG (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hp2 : p ≠ 2)
    (E₀ : ℝ) (hBG : ∀ b : ZMod p, b ≠ 0 → ∀ N : ℕ, E₀ ≤ N → N < p →
      ‖Tsum p b N‖ ≤ bgB C p N)
    (a b : ℕ) (ha : 6 ≤ a) (hb : b ≤ 2 * a) (h2a : 2 * a < p)
    (hE : E₀ ≤ (a : ℝ) / 3) :
    ∀ c : ZMod p, c ≠ 0 → ∀ x, a ≤ x → x ≤ b →
      ‖∑ k ∈ (Ico a x).filter Odd, psiP p (c * ((2 * k : ℕ) : ZMod p)⁻¹)‖ ≤
        4 * (C * Real.log (Real.log p) ^ 3 * Real.log p *
          Real.log ((a : ℝ) / 3) ^ (-(3 / 2 : ℝ)) * (2 * a)) := by
  haveI := Fact.mk hp
  intro c hc x hax hxb
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this; omega
  have h4 : (4 : ZMod p) ≠ 0 := by
    have : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hb1 : c * 2⁻¹ ≠ 0 := mul_ne_zero hc (inv_ne_zero h2)
  have hb2 : c * 4⁻¹ ≠ 0 := mul_ne_zero hc (inv_ne_zero h4)
  refine (odd_interval_bound p hp c a x (by omega) hax).trans ?_
  have t1 := one_termG C hC p hp3 _ hb1 E₀ hBG a (x - 1) ha (by omega) (by omega) h2a hE
  have t2 := one_termG C hC p hp3 _ hb1 E₀ hBG a (a - 1) ha (by omega) (by omega) h2a hE
  have t3 := one_termG C hC p hp3 _ hb2 E₀ hBG a ((x + 1) / 2 - 1) ha (by omega) (by omega) h2a hE
  have t4 := one_termG C hC p hp3 _ hb2 E₀ hBG a ((a + 1) / 2 - 1) ha (by omega) (by omega) h2a hE
  linarith

/-- **Explicit bound for `|R_K(p)|`** with a general Bourgain–Garaev threshold `E₀` and the
dyadic savings `log(2^j K_*/3)^{-3/2}` kept block by block. -/
theorem R_boundG (hV : HV) (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (E₀ : ℝ) (hBG : ∀ b : ZMod p, b ≠ 0 → ∀ N : ℕ, E₀ ≤ N → N < p →
      ‖Tsum p b N‖ ≤ bgB C p N)
    (K N H Ks J : ℕ) (hN : 1 ≤ N) (hH : 1 ≤ H) (hHp : H < p) (hNp : N < p)
    (hKs6 : 6 ≤ Ks) (hNKs : 2 * N + 1 ≤ Ks) (hKsKW : Ks ≤ K) (hKW : 2 * K < p)
    (hE : E₀ ≤ (Ks : ℝ) / 3) (hJ : K ≤ 2 ^ J * Ks)
    (Ttail : ℝ)
    (htail : ∑ k ∈ (Ioo (N + 1) K).filter Odd, (1 / k : ℝ) * |phiTail k N (uInv p k)| ≤ Ttail) :
    |RsumK K p| ≤ 2 / Real.pi * (2 + Real.log N) * (1 + Real.log Ks) +
      2 / (H + 1) * (2 / Real.pi * (2 + Real.log N) * (1 + Real.log K)) +
      (∑ h ∈ Icc 1 H, 4 / (Real.pi * h) + 4) * (16 / Real.pi * (2 + Real.log N) *
        (C * (Real.log (Real.log p) ^ 3 * Real.log p) *
          ∑ j ∈ range J, Real.log (((2 ^ j * Ks : ℕ) : ℝ) / 3) ^ (-(3 / 2 : ℝ)))) +
      Ttail := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hpi := Real.pi_pos
  set X := Real.log (Real.log p) ^ 3 * Real.log p
  have hX : 0 ≤ X := by
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast (by omega : 3 ≤ p)
    have : 1 ≤ Real.log p := by
      rw [← Real.log_exp 1]; apply Real.log_le_log (Real.exp_pos 1); linarith [Real.exp_one_lt_d9]
    have : 0 ≤ Real.log (Real.log p) := Real.log_nonneg this
    have : 0 ≤ Real.log (p : ℝ) := by linarith
    positivity
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  -- decomposition
  have hRs : RsumK K p = -(∑ k ∈ (Ico 3 K).filter Odd, (1 / k : ℝ) * headTh N k (uInv p k)) -
      ∑ k ∈ (Ico 3 K).filter Odd, (1 / k : ℝ) * phiTail k N (uInv p k) := by
    unfold RsumK
    have h1 : ∀ k ∈ (Ico 3 K).filter Odd, Fsum k p / (k : ℝ) ^ 2 =
        -((1 / k : ℝ) * headTh N k (uInv p k)) - (1 / k : ℝ) * phiTail k N (uInv p k) := by
      intro k hk
      simp only [mem_filter, mem_Ico] at hk
      rw [Fsum_split p k N hp hk.1.1 hk.2 (by omega)]; ring
    rw [sum_congr rfl h1, sum_sub_distrib, sum_neg_distrib]
  -- tails
  have hT : |∑ k ∈ (Ico 3 K).filter Odd, (1 / k : ℝ) * phiTail k N (uInv p k)| ≤ Ttail := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hsub : (Ioo (N + 1) K).filter Odd ⊆ (Ico 3 K).filter Odd := by
      intro k hk; simp only [mem_filter, mem_Ioo, mem_Ico] at hk ⊢; exact ⟨⟨by omega, hk.1.2⟩, hk.2⟩
    rw [← sum_subset hsub]
    · refine le_trans (le_of_eq ?_) htail
      apply sum_congr rfl; intro k hk
      simp only [mem_filter, mem_Ioo] at hk
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / k)]
    · intro k hk hk'
      simp only [mem_filter, mem_Ioo, mem_Ico, not_and] at hk hk'
      have hkN : k ≤ N + 1 := by
        by_contra h
        exact hk' (by omega) hk.2
      have : phiTail k N (uInv p k) = 0 := by
        unfold phiTail
        apply sum_eq_zero; intro n hn
        simp only [mem_filter, mem_Ioo] at hn; omega
      rw [this]; simp
  -- heads
  set fH : ℕ → ℝ := fun k => (1 / k : ℝ) * headTh N k (uInv p k)
  have hsplitH := sum_filter_Ico_split fH 3 Ks K (by omega) hKsKW
  have hsmall : |∑ k ∈ (Ico 3 Ks).filter Odd, fH k| ≤
      2 / Real.pi * (2 + Real.log N) * (1 + Real.log Ks) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ (Ico 3 Ks).filter Odd, |fH k| ≤
          ∑ k ∈ (Ico 3 Ks).filter Odd, 2 / Real.pi * (2 + Real.log N) * (1 / k : ℝ) := by
          apply sum_le_sum; intro k hk
          simp only [fH]
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / k)]
          have := headTh_trivial N k (uInv p k) hN
          have hk0 : (0 : ℝ) ≤ 1 / k := by positivity
          nlinarith
      _ = 2 / Real.pi * (2 + Real.log N) * ∑ k ∈ (Ico 3 Ks).filter Odd, (1 / k : ℝ) := by rw [mul_sum]
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply sum_inv_le_log Ks
          intro k hk; simp only [mem_filter, mem_Ico] at hk; omega
  -- the big range, in Kloosterman form and split into dyadic blocks
  set a : ℕ → ℕ := fun j => min (2 ^ j * Ks) K
  set b : ℕ → ℕ := fun j => min (2 ^ (j + 1) * Ks) K
  have hbigeq : ∑ k ∈ (Ico Ks K).filter Odd, fH k =
      ∑ j ∈ range J, ∑ k ∈ (Ico (a j) (b j)).filter Odd, headTerm p N k := by
    have h1 : ∑ k ∈ (Ico Ks K).filter Odd, fH k = ∑ k ∈ (Ico Ks K).filter Odd, headTerm p N k := by
      apply sum_congr rfl; intro k hk
      simp only [mem_filter, mem_Ico] at hk
      exact headTh_eq_headTerm p N k hp hp2 (by omega) hk.2 (by omega) (by omega)
    rw [h1]
    simp only [sum_filter]
    exact dyadic_split _ Ks K J hKsKW hJ
  have ha : ∀ j, Ks ≤ a j ∧ a j ≤ b j ∧ b j ≤ 2 * a j ∧ a j ≤ K ∧ b j ≤ K := by
    intro j
    have h1 : Ks ≤ 2 ^ j * Ks := Nat.le_mul_of_pos_left Ks (by positivity)
    have h2 : 2 ^ (j + 1) * Ks = 2 * (2 ^ j * Ks) := by ring
    simp only [a, b]; rw [h2]
    refine ⟨le_min h1 hKsKW, ?_, ?_, min_le_right _ _, min_le_right _ _⟩
    · apply min_le_min_right; omega
    · rcases le_total (2 ^ j * Ks) K with h | h
      · rw [min_eq_left h]; exact min_le_left _ _
      · rw [min_eq_right h]; omega
  set Bj : ℕ → ℝ := fun j => (∑ h ∈ Icc 1 H, 4 / (Real.pi * h) + 4) * (16 / Real.pi * (2 + Real.log N) *
      (C * X * Real.log (((2 ^ j * Ks : ℕ) : ℝ) / 3) ^ (-(3 / 2 : ℝ))))
  have hSh0 : 0 ≤ ∑ h ∈ Icc 1 H, 4 / (Real.pi * h) := by
    apply sum_nonneg; intro h _; positivity
  have hBj0 : ∀ j, 0 ≤ Bj j := by
    intro j
    have h6 : (6 : ℝ) ≤ ((2 ^ j * Ks : ℕ) : ℝ) := by
      exact_mod_cast le_trans hKs6 (Nat.le_mul_of_pos_left Ks (by positivity))
    have hl : 0 ≤ Real.log (((2 ^ j * Ks : ℕ) : ℝ) / 3) :=
      Real.log_nonneg (by rw [le_div_iff₀ (by norm_num)]; linarith)
    have h1 := Real.rpow_nonneg hl (-(3 / 2 : ℝ))
    have h2 := mul_nonneg hC hX
    simp only [Bj]; positivity
  have hblock : ∀ j ∈ range J, |∑ k ∈ (Ico (a j) (b j)).filter Odd, headTerm p N k| ≤
      2 / (H + 1) * ∑ k ∈ (Ico (a j) (b j)).filter Odd, ∑ n ∈ (Icc 1 N).filter Odd, wt n k + Bj j := by
    intro j _
    obtain ⟨hKa, hab, hb2, haK, hbK⟩ := ha j
    rcases Nat.lt_or_ge (a j) (b j) with hlt | hge
    swap
    · have hem : (Ico (a j) (b j)).filter Odd = ∅ := by
        ext k; simp only [mem_filter, mem_Ico, Finset.notMem_empty, iff_false]; omega
      rw [hem, sum_empty, sum_empty, abs_zero, mul_zero, zero_add]; exact hBj0 j
    have haj : a j = 2 ^ j * Ks := by
      simp only [a]; apply min_eq_left; by_contra hc; push_neg at hc
      have : min (2 ^ j * Ks) K = K := min_eq_right hc.le
      simp only [a] at hlt; rw [this] at hlt; omega
    have hE' : E₀ ≤ (a j : ℝ) / 3 := by
      refine hE.trans ?_
      have : (Ks : ℝ) ≤ a j := by exact_mod_cast hKa
      linarith
    set Mb := 4 * (C * Real.log (Real.log p) ^ 3 * Real.log p *
      Real.log ((a j : ℝ) / 3) ^ (-(3 / 2 : ℝ)) * (2 * a j))
    have hla : 0 < Real.log ((a j : ℝ) / 3) := by
      apply Real.log_pos; rw [lt_div_iff₀ (by norm_num)]
      have : (6 : ℝ) ≤ a j := by exact_mod_cast (le_trans hKs6 hKa)
      linarith
    have hMb0 : 0 ≤ Mb := by
      have : 0 ≤ Real.log ((a j : ℝ) / 3) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hla.le _
      have hX' : 0 ≤ Real.log (Real.log p) ^ 3 * Real.log p := hX
      simp only [Mb]
      have : 0 ≤ C * Real.log (Real.log p) ^ 3 * Real.log p := by
        rw [mul_assoc]; exact mul_nonneg hC hX'
      positivity
    have hMb := block_kloostG C hC p hp (by omega) hp2 E₀ hBG (a j) (b j) (le_trans hKs6 hKa) hb2
      (by omega) hE'
    have hbh := block_heads hV p hp hp2 N H (a j) (b j) hH hN (by omega) hab (by omega) hHp hNp
      Mb hMb0 hMb
    refine hbh.trans (add_le_add le_rfl ?_)
    have hWa := Wa_bound N (a j) hN (by omega)
    have ha0 : (0 : ℝ) < a j := by exact_mod_cast (by omega : 0 < a j)
    have hcast : ((a j : ℕ) : ℝ) = ((2 ^ j * Ks : ℕ) : ℝ) := by rw [haj]
    have hWM : (∑ n ∈ (Icc 1 N).filter Odd, wt n (a j)) * Mb ≤
        16 / Real.pi * (2 + Real.log N) *
          (C * X * Real.log (((2 ^ j * Ks : ℕ) : ℝ) / 3) ^ (-(3 / 2 : ℝ))) := by
      calc (∑ n ∈ (Icc 1 N).filter Odd, wt n (a j)) * Mb ≤ 2 / (Real.pi * a j) * (2 + Real.log N) * Mb :=
            mul_le_mul_of_nonneg_right hWa hMb0
        _ = 16 / Real.pi * (2 + Real.log N) * (C * X * Real.log ((a j : ℝ) / 3) ^ (-(3 / 2 : ℝ))) := by
            simp only [Mb, X]; field_simp; ring
        _ = _ := by rw [hcast]
    have hS4 : 0 ≤ ∑ h ∈ Icc 1 H, 4 / (Real.pi * h) + 4 := by linarith
    calc (∑ h ∈ Icc 1 H, 4 / (Real.pi * h) + 4) * (∑ n ∈ (Icc 1 N).filter Odd, wt n (a j)) * Mb
        = (∑ h ∈ Icc 1 H, 4 / (Real.pi * h) + 4) * ((∑ n ∈ (Icc 1 N).filter Odd, wt n (a j)) * Mb) := by ring
      _ ≤ Bj j := mul_le_mul_of_nonneg_left hWM hS4
  have hZ : ∑ j ∈ range J, ∑ k ∈ (Ico (a j) (b j)).filter Odd, ∑ n ∈ (Icc 1 N).filter Odd, wt n k ≤
      2 / Real.pi * (2 + Real.log N) * (1 + Real.log K) := by
    have e : ∑ j ∈ range J, ∑ k ∈ (Ico (a j) (b j)).filter Odd, ∑ n ∈ (Icc 1 N).filter Odd, wt n k =
        ∑ k ∈ (Ico Ks K).filter Odd, ∑ n ∈ (Icc 1 N).filter Odd, wt n k := by
      simp only [sum_filter]
      exact (dyadic_split _ Ks K J hKsKW hJ).symm
    rw [e]
    apply Z_bound N hN _ K
    intro k hk; simp only [mem_filter, mem_Ico] at hk; omega
  have hbig : |∑ k ∈ (Ico Ks K).filter Odd, fH k| ≤
      2 / (H + 1) * (2 / Real.pi * (2 + Real.log N) * (1 + Real.log K)) + ∑ j ∈ range J, Bj j := by
    rw [hbigeq]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_sum hblock).trans ?_
    rw [sum_add_distrib, ← mul_sum]
    have hH0 : (0 : ℝ) ≤ 2 / (H + 1) := by positivity
    linarith [mul_le_mul_of_nonneg_left hZ hH0]
  rw [hRs, hsplitH]
  calc |-(∑ k ∈ (Ico 3 Ks).filter Odd, fH k + ∑ k ∈ (Ico Ks K).filter Odd, fH k) -
        ∑ k ∈ (Ico 3 K).filter Odd, (1 / k : ℝ) * phiTail k N (uInv p k)|
      ≤ |∑ k ∈ (Ico 3 Ks).filter Odd, fH k| + |∑ k ∈ (Ico Ks K).filter Odd, fH k| +
          |∑ k ∈ (Ico 3 K).filter Odd, (1 / k : ℝ) * phiTail k N (uInv p k)| := by
        have h1 := abs_sub (-(∑ k ∈ (Ico 3 Ks).filter Odd, fH k + ∑ k ∈ (Ico Ks K).filter Odd, fH k))
          (∑ k ∈ (Ico 3 K).filter Odd, (1 / k : ℝ) * phiTail k N (uInv p k))
        have h2 := abs_add_le (∑ k ∈ (Ico 3 Ks).filter Odd, fH k) (∑ k ∈ (Ico Ks K).filter Odd, fH k)
        rw [abs_neg] at h1
        linarith
    _ ≤ _ := by
        have hBs : ∑ j ∈ range J, Bj j = (∑ h ∈ Icc 1 H, 4 / (Real.pi * h) + 4) *
            (16 / Real.pi * (2 + Real.log N) * (C * (Real.log (Real.log p) ^ 3 * Real.log p) *
              ∑ j ∈ range J, Real.log (((2 ^ j * Ks : ℕ) : ℝ) / 3) ^ (-(3 / 2 : ℝ)))) := by
          simp only [Bj, X, mul_sum]
        rw [hBs] at hbig
        linarith

end ThetaSum

#print axioms ThetaSum.R_boundG
