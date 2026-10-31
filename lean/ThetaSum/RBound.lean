import ThetaSum.Decomp

/-
The explicit bound for `|R_{K_W}(p)|`: heads below `K_*` (trivially), heads in `[K_*, K_W)`
(dyadic blocks, Lemma 6.6 with the Bourgain–Garaev bound), and the tails (as a hypothesis
`htail`, supplied by `tails_sum_explicit` in the final assembly).
-/

open Finset

namespace ThetaSum

lemma oddsum_Icc (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ (Icc 1 N).filter Odd, (1 / n : ℝ) ≤ 2 + Real.log N := by
  have hsub : (Icc 1 N).filter Odd ⊆ insert 1 ((Icc 1 N).filter (fun n => Odd n ∧ 3 ≤ n)) := by
    intro n hn
    simp only [mem_filter, mem_Icc, mem_insert] at hn ⊢
    obtain ⟨⟨h0, hN'⟩, ⟨m, hm⟩⟩ := hn
    by_cases h1 : n = 1
    · left; exact h1
    · right; exact ⟨⟨h0, hN'⟩, ⟨m, hm⟩, by omega⟩
  calc ∑ n ∈ (Icc 1 N).filter Odd, (1 / n : ℝ)
      ≤ ∑ n ∈ insert 1 ((Icc 1 N).filter (fun n => Odd n ∧ 3 ≤ n)), (1 / n : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = 1 / (1 : ℕ) + ∑ n ∈ (Icc 1 N).filter (fun n => Odd n ∧ 3 ≤ n), (1 / n : ℝ) := by
        rw [sum_insert]; simp only [mem_filter]; omega
    _ ≤ 1 + Real.log (N + 1) / 2 := by
        have := odd_sum_le (N + 1) (by omega) ((Icc 1 N).filter (fun n => Odd n ∧ 3 ≤ n))
          (by intro n hn; simp only [mem_filter, mem_Icc] at hn; exact ⟨hn.2.2, by omega, hn.2.1⟩)
        push_cast at this
        simp only [Nat.cast_one, div_one]; linarith
    _ ≤ 2 + Real.log N := by
        have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
        have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
        have h1 : Real.log ((N : ℝ) + 1) ≤ Real.log (2 * N) := Real.log_le_log (by positivity) (by linarith)
        rw [Real.log_mul (by norm_num) hN0.ne'] at h1
        have := Real.log_two_lt_d9
        have : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
        linarith

lemma Wa_bound (N a : ℕ) (hN : 1 ≤ N) (ha : 2 * N ≤ a) :
    ∑ n ∈ (Icc 1 N).filter Odd, wt n a ≤ 2 / (Real.pi * a) * (2 + Real.log N) := by
  have hpi := Real.pi_pos
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  calc ∑ n ∈ (Icc 1 N).filter Odd, wt n a ≤ ∑ n ∈ (Icc 1 N).filter Odd, 2 / (Real.pi * a) * (1 / n : ℝ) := by
        apply sum_le_sum; intro n hn
        simp only [mem_filter, mem_Icc] at hn
        have := (weight_bounds n a hn.1.1 (by omega)).2
        unfold wt
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1.1
        calc _ ≤ 2 / (Real.pi * n * a) := this
          _ = _ := by field_simp
    _ = 2 / (Real.pi * a) * ∑ n ∈ (Icc 1 N).filter Odd, (1 / n : ℝ) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (oddsum_Icc N hN) (by positivity)

lemma Z_bound (N : ℕ) (hN : 1 ≤ N) (A : Finset ℕ) (K : ℕ) (hA : ∀ k ∈ A, 2 * N ≤ k ∧ k < K) :
    ∑ k ∈ A, ∑ n ∈ (Icc 1 N).filter Odd, wt n k ≤ 2 / Real.pi * (2 + Real.log N) * (1 + Real.log K) := by
  have hpi := Real.pi_pos
  calc ∑ k ∈ A, ∑ n ∈ (Icc 1 N).filter Odd, wt n k ≤ ∑ k ∈ A, 2 / Real.pi * (2 + Real.log N) * (1 / k : ℝ) := by
        apply sum_le_sum; intro k hk
        have hk0 : (0 : ℝ) < k := by have := hA k hk; exact_mod_cast (by omega : 0 < k)
        refine (Wa_bound N k hN (hA k hk).1).trans (le_of_eq ?_)
        field_simp
    _ = 2 / Real.pi * (2 + Real.log N) * ∑ k ∈ A, (1 / k : ℝ) := by rw [mul_sum]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by
          have : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
          positivity)
        apply sum_inv_le_log K A
        intro k hk; have := hA k hk; omega

lemma sum_filter_Ico_split (f : ℕ → ℝ) (a m b : ℕ) (ham : a ≤ m) (hmb : m ≤ b) :
    ∑ k ∈ (Ico a b).filter Odd, f k = ∑ k ∈ (Ico a m).filter Odd, f k + ∑ k ∈ (Ico m b).filter Odd, f k := by
  simp only [sum_filter]
  rw [sum_Ico_consecutive _ ham hmb]

/-- **Explicit bound for `|R_K(p)|`**, for any bound `4 · Q · 2a` on the odd-`k` Kloosterman sums
over the blocks `[a, x) ⊆ [a, 2a]`, `a ≥ K_*`. -/
theorem R_bound_gen (hV : HV) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (K N H Ks J : ℕ) (hN : 1 ≤ N) (hH : 1 ≤ H) (hHp : H < p) (hNp : N < p)
    (hKs6 : 6 ≤ Ks) (hNKs : 2 * N + 1 ≤ Ks) (hKsKW : Ks ≤ K) (hKW : 2 * K < p)
    (hJ : K ≤ 2 ^ J * Ks) (Q : ℝ) (hQ : 0 ≤ Q)
    (hKl : ∀ a b : ℕ, Ks ≤ a → b ≤ 2 * a → 2 * a < p → ∀ c : ZMod p, c ≠ 0 → ∀ x, a ≤ x → x ≤ b →
      ‖∑ k ∈ (Ico a x).filter Odd, psiP p (c * ((2 * k : ℕ) : ZMod p)⁻¹)‖ ≤ 4 * (Q * (2 * a)))
    (Ttail : ℝ)
    (htail : ∑ k ∈ (Ioo (N + 1) K).filter Odd, (1 / k : ℝ) * |phiTail k N (uInv p k)| ≤ Ttail) :
    |RsumK K p| ≤ 2 / Real.pi * (2 + Real.log N) * (1 + Real.log Ks) +
      2 / (H + 1) * (2 / Real.pi * (2 + Real.log N) * (1 + Real.log K)) +
      J * ((∑ h ∈ Icc 1 H, 4 / (Real.pi * h) + 4) * (16 / Real.pi * (2 + Real.log N) * Q)) +
      Ttail := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hpi := Real.pi_pos
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
  set Bh : ℝ := (∑ h ∈ Icc 1 H, 4 / (Real.pi * h) + 4) * (16 / Real.pi * (2 + Real.log N) * Q)
  have hSh0 : 0 ≤ ∑ h ∈ Icc 1 H, 4 / (Real.pi * h) := by
    apply sum_nonneg; intro h _; positivity
  have hblock : ∀ j ∈ range J, |∑ k ∈ (Ico (a j) (b j)).filter Odd, headTerm p N k| ≤
      2 / (H + 1) * ∑ k ∈ (Ico (a j) (b j)).filter Odd, ∑ n ∈ (Icc 1 N).filter Odd, wt n k + Bh := by
    intro j _
    obtain ⟨hKa, hab, hb2, haK, hbK⟩ := ha j
    set Mb := 4 * (Q * (2 * a j))
    have hMb0 : 0 ≤ Mb := by positivity
    have hMb := hKl (a j) (b j) hKa hb2 (by omega)
    have hbh := block_heads hV p hp hp2 N H (a j) (b j) hH hN (by omega) hab (by omega) hHp hNp
      Mb hMb0 hMb
    refine hbh.trans (add_le_add le_rfl ?_)
    have hWa := Wa_bound N (a j) hN (by omega)
    have ha0 : (0 : ℝ) < a j := by exact_mod_cast (by omega : 0 < a j)
    have hWM : (∑ n ∈ (Icc 1 N).filter Odd, wt n (a j)) * Mb ≤
        16 / Real.pi * (2 + Real.log N) * Q := by
      calc (∑ n ∈ (Icc 1 N).filter Odd, wt n (a j)) * Mb ≤ 2 / (Real.pi * a j) * (2 + Real.log N) * Mb :=
            mul_le_mul_of_nonneg_right hWa hMb0
        _ = 16 / Real.pi * (2 + Real.log N) * Q := by
            simp only [Mb]; field_simp; ring
    have hS4 : 0 ≤ ∑ h ∈ Icc 1 H, 4 / (Real.pi * h) + 4 := by linarith
    calc (∑ h ∈ Icc 1 H, 4 / (Real.pi * h) + 4) * (∑ n ∈ (Icc 1 N).filter Odd, wt n (a j)) * Mb
        = (∑ h ∈ Icc 1 H, 4 / (Real.pi * h) + 4) * ((∑ n ∈ (Icc 1 N).filter Odd, wt n (a j)) * Mb) := by ring
      _ ≤ Bh := mul_le_mul_of_nonneg_left hWM hS4
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
      2 / (H + 1) * (2 / Real.pi * (2 + Real.log N) * (1 + Real.log K)) + J * Bh := by
    rw [hbigeq]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_sum hblock).trans ?_
    rw [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
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
        have := hsmall; have := hbig; have := hT
        simp only [Bh] at *
        linarith

/-- **Explicit bound for `|R_K(p)|`** from the Bourgain–Garaev-type bound `bgB`. -/
theorem R_bound (hV : HV) (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hBG : ∀ b : ZMod p, b ≠ 0 → ∀ N : ℕ, Real.log p ^ (9 / 10 : ℝ) / 2 ≤ Real.log N → N < p →
      ‖Tsum p b N‖ ≤ bgB C p N)
    (K N H Ks J : ℕ) (hN : 1 ≤ N) (hH : 1 ≤ H) (hHp : H < p) (hNp : N < p)
    (hKs6 : 6 ≤ Ks) (hNKs : 2 * N + 1 ≤ Ks) (hKsKW : Ks ≤ K) (hKW : 2 * K < p)
    (hlog : Real.log p ^ (9 / 10 : ℝ) / 2 ≤ Real.log ((Ks : ℝ) / 3)) (hJ : K ≤ 2 ^ J * Ks)
    (Ttail : ℝ)
    (htail : ∑ k ∈ (Ioo (N + 1) K).filter Odd, (1 / k : ℝ) * |phiTail k N (uInv p k)| ≤ Ttail) :
    |RsumK K p| ≤ 2 / Real.pi * (2 + Real.log N) * (1 + Real.log Ks) +
      2 / (H + 1) * (2 / Real.pi * (2 + Real.log N) * (1 + Real.log K)) +
      J * ((∑ h ∈ Icc 1 H, 4 / (Real.pi * h) + 4) * (16 / Real.pi * (2 + Real.log N) *
        (C * (Real.log (Real.log p) ^ 3 * Real.log p) * Real.log ((Ks : ℝ) / 3) ^ (-(3 / 2 : ℝ))))) +
      Ttail := by
  have hp2 : p ≠ 2 := by omega
  set X := Real.log (Real.log p) ^ 3 * Real.log p
  have hX : 0 ≤ X := by
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast (by omega : 3 ≤ p)
    have : 1 ≤ Real.log p := by
      rw [← Real.log_exp 1]; apply Real.log_le_log (Real.exp_pos 1); linarith [Real.exp_one_lt_d9]
    have : 0 ≤ Real.log (Real.log p) := Real.log_nonneg this
    have : 0 ≤ Real.log (p : ℝ) := by linarith
    positivity
  have hKs3 : (1 : ℝ) < (Ks : ℝ) / 3 := by
    rw [lt_div_iff₀ (by norm_num)]; have : (6 : ℝ) ≤ Ks := by exact_mod_cast hKs6
    linarith
  refine R_bound_gen hV p hp hp5 K N H Ks J hN hH hHp hNp hKs6 hNKs hKsKW hKW hJ
    (C * X * Real.log ((Ks : ℝ) / 3) ^ (-(3 / 2 : ℝ)))
    (mul_nonneg (mul_nonneg hC hX) (Real.rpow_nonneg (Real.log_pos hKs3).le _)) ?_ Ttail htail
  intro a b hKa hb2 h2a c hc x hax hxb
  have hlogA : Real.log p ^ (9 / 10 : ℝ) / 2 ≤ Real.log ((a : ℝ) / 3) := by
    refine hlog.trans (Real.log_le_log (by positivity) ?_)
    have : (Ks : ℝ) ≤ a := by exact_mod_cast hKa
    linarith
  refine (block_kloost C hC p hp (by omega) hp2 hBG a b (le_trans hKs6 hKa) hb2 h2a hlogA c hc x hax hxb).trans ?_
  have hpowle : Real.log ((a : ℝ) / 3) ^ (-(3 / 2 : ℝ)) ≤ Real.log ((Ks : ℝ) / 3) ^ (-(3 / 2 : ℝ)) := by
    apply Real.rpow_le_rpow_of_nonpos (Real.log_pos hKs3) _ (by norm_num)
    apply Real.log_le_log (by positivity)
    have : (Ks : ℝ) ≤ a := by exact_mod_cast hKa
    linarith
  have ha0 : (0 : ℝ) ≤ 2 * a := by positivity
  have hCX : 0 ≤ C * X := mul_nonneg hC hX
  calc 4 * (C * Real.log (Real.log p) ^ 3 * Real.log p * Real.log ((a : ℝ) / 3) ^ (-(3 / 2 : ℝ)) * (2 * a))
      = 4 * ((C * X * Real.log ((a : ℝ) / 3) ^ (-(3 / 2 : ℝ))) * (2 * a)) := by simp only [X]; ring
    _ ≤ 4 * ((C * X * Real.log ((Ks : ℝ) / 3) ^ (-(3 / 2 : ℝ))) * (2 * a)) := by
        gcongr

end ThetaSum
