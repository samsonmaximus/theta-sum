import ThetaSum.FormalConjectures
import ThetaSum.WeakHyp
import ThetaSum.ConstantC0
import ThetaSum.ZetaClosed
import ThetaSum.TheoremDStar
import ThetaSum.TheoremC
import ThetaSum.TheoremCStar

/-!
# Main theorems: one file for a reviewer

`lake build ThetaSum.MainTheorems` (or `lake env lean ThetaSum/MainTheorems.lean`) prints the
statement and the axioms of every headline result. Every `#print axioms` should report exactly
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no `Lean.ofReduceBool`).
-/

open ThetaSum

-- Conjecture 3.3 of arXiv:2501.03234 (C₁ k < S(k) < C₂ k^{1+ε} for all large primes k)
#check @ThetaSum.conjecture_3_3_of_HKS         -- assuming only (HKS), weaker than (HBG)
#check @ThetaSum.HKS
#check @ThetaSum.HKS_of_HBG
#check @Arxiv.«2501.03234».conjecture_4_4_of_HKS
#check @ThetaSum.conjecture_3_3_of_BG          -- assuming only (HBG)
#check @ThetaSum.conjecture_3_3_upper          -- upper half, unconditional
#check @ThetaSum.conjecture_1_1_eventually_of_BG
#check @ThetaSum.conjecture_3_1_eventually_of_BG
#check @ThetaSum.conjecture_3_2_eventually_of_BG
#check @ThetaSum.HBG                           -- the one remaining hypothesis (Bourgain–Garaev)

-- The formal-conjectures file `Arxiv/2501.03234/ArithmeticSumS.lean`
#check @Arxiv.«2501.03234».S_fst_10
#check @Arxiv.«2501.03234».conjecture_4_4_of_BG
#check @Arxiv.«2501.03234».conjecture_1_1_upto
#check @Arxiv.«2501.03234».conjecture_4_1_upto
#check @Arxiv.«2501.03234».conjecture_4_2_upto
#check @Arxiv.«2501.03234».conjecture_4_3_upto
#check @Arxiv.«2501.03234».conjecture_1_1_eventually_of_BG
#check @Arxiv.«2501.03234».conjecture_4_1_eventually_of_BG
#check @Arxiv.«2501.03234».conjecture_4_2_eventually_of_BG
#check @Arxiv.«2501.03234».conjecture_4_3_eventually_of_BG

-- Finite range (kernel-checked computation) and Lemma 2.5
#check @ThetaSum.S_pos_upto
#check @ThetaSum.S_gt_two_mul_upto
#check @ThetaSum.S_gt_three_mul_upto
#check @ThetaSum.S_233
#check @ThetaSum.S_3119
#check @ThetaSum.S_eq_lemma25
#check @ThetaSum.Ffl_recip
#check @ThetaSum.Sfast_eq

-- Analytic and arithmetic ingredients
#check @ThetaSum.theorem_D
#check @ThetaSum.theorem_D_star
#check @ThetaSum.hK34                          -- Kloosterman: |K(b,ℓ)| ≤ 2 p^{3/4}
#check @ThetaSum.kl_four_le                    -- |K(b,ℓ)|⁴ ≤ 3 p³
#check @Vaaler.vaaler_lemma
#check @ThetaSum.hV_holds
#check @Recip.reciprocity                      -- reciprocity for the tangent sums (Lemma 4.1)
#check @TheoremB.S_eq_Psi_Phi                  -- Theorem B decomposition
#check @TheoremB.HBweak34_of_HK34              -- Theorem B (Kloosterman form)
#check @ThetaSum.hBweak34
#check @Arxiv.«2501.03234».theorem_A
#check @Arxiv.«2501.03234».S_abs_le            -- |S(p)| ≤ 5 p H_p²
#check @ThetaSum.lower_half_HBweak34_HBG
#check @ThetaSum.lower_half


-- Theorem B(ii) with the exact constant, Theorem C, and the constant c₀
#check @ThetaSum.theorem_B_c0                   -- unconditional, o(p) error, cutoff p^{3/4}(log p)^4
#check @ThetaSum.c0_closed_form                 -- c₀ = K₀/2 + log 2/6 + (3/π²)·Re ζ'(2)
#check @ThetaSum.SLodd_closed_form
#check @ThetaSum.deriv_zeta_two
#check @TheoremB.Psi_asymp
#check @TheoremB.I_asymp_K0
#check @TheoremB.Cp_one_asymp
#check @ThetaSum.theorem_C                      -- from (HBGfull)
#check @ThetaSum.theorem_C_star                 -- from (HBGfull)
#check @ThetaSum.theorem_C_c0
#check @ThetaSum.theorem_C_star_c0

#print axioms ThetaSum.conjecture_3_3_of_HKS
#print axioms ThetaSum.HKS_of_HBG
#print axioms Arxiv.«2501.03234».conjecture_4_4_of_HKS
#print axioms ThetaSum.conjecture_3_3_of_BG
#print axioms ThetaSum.conjecture_3_3_upper
#print axioms ThetaSum.conjecture_1_1_eventually_of_BG
#print axioms ThetaSum.conjecture_3_1_eventually_of_BG
#print axioms ThetaSum.conjecture_3_2_eventually_of_BG
#print axioms Arxiv.«2501.03234».S_fst_10
#print axioms Arxiv.«2501.03234».conjecture_4_4_of_BG
#print axioms Arxiv.«2501.03234».conjecture_1_1_upto
#print axioms Arxiv.«2501.03234».conjecture_4_1_upto
#print axioms Arxiv.«2501.03234».conjecture_4_2_upto
#print axioms Arxiv.«2501.03234».conjecture_4_3_upto
#print axioms Arxiv.«2501.03234».conjecture_1_1_eventually_of_BG
#print axioms Arxiv.«2501.03234».conjecture_4_1_eventually_of_BG
#print axioms Arxiv.«2501.03234».conjecture_4_2_eventually_of_BG
#print axioms Arxiv.«2501.03234».conjecture_4_3_eventually_of_BG
#print axioms Arxiv.«2501.03234».conjecture_4_4_def_0
#print axioms Arxiv.«2501.03234».conjecture_4_4_def_1
#print axioms Arxiv.«2501.03234».conjecture_4_4_def_2
#print axioms Arxiv.«2501.03234».conjecture_4_4_def_3
#print axioms ThetaSum.S_pos_upto
#print axioms ThetaSum.S_gt_two_mul_upto
#print axioms ThetaSum.S_gt_three_mul_upto
#print axioms ThetaSum.S_233
#print axioms ThetaSum.S_3119
#print axioms ThetaSum.S_eq_lemma25
#print axioms ThetaSum.Ffl_recip
#print axioms ThetaSum.Sfast_eq
#print axioms ThetaSum.theorem_D
#print axioms ThetaSum.theorem_D_star
#print axioms ThetaSum.hK34
#print axioms ThetaSum.kl_four_le
#print axioms Vaaler.vaaler_lemma
#print axioms ThetaSum.hV_holds
#print axioms Recip.reciprocity
#print axioms TheoremB.S_eq_Psi_Phi
#print axioms TheoremB.HBweak34_of_HK34
#print axioms ThetaSum.hBweak34
#print axioms Arxiv.«2501.03234».theorem_A
#print axioms Arxiv.«2501.03234».S_abs_le
-- companion paper, Lemma: |G_d(n)| ≤ G_d(1)
#print axioms Arxiv.«2501.03234».Gsum_abs_le
#print axioms ThetaSum.lower_half_HBweak34_HBG
#print axioms ThetaSum.lower_half

-- Theorems C and C* (from HBGfull). Note: the c·p term is redundant in these statements
-- (the error exceeds p); their content is S(p) = (p/2) log p + O(error).
#check @ThetaSum.theorem_C
#print axioms ThetaSum.theorem_C
#check @ThetaSum.theorem_C_star
#print axioms ThetaSum.theorem_C_star
#print axioms ThetaSum.theorem_B_c0
#print axioms ThetaSum.c0_closed_form
#print axioms ThetaSum.SLodd_closed_form
#print axioms ThetaSum.deriv_zeta_two
#print axioms TheoremB.Psi_asymp
#print axioms TheoremB.I_asymp_K0
#print axioms TheoremB.Cp_one_asymp
#print axioms ThetaSum.theorem_C
#print axioms ThetaSum.theorem_C_star
#print axioms ThetaSum.theorem_C_c0
#print axioms ThetaSum.theorem_C_star_c0
