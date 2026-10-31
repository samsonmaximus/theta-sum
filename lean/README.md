# Lean formalization

Lean 4 with Mathlib v4.35.0, about 17,000 lines. No `sorry`, no `native_decide`, and no added axioms: `#print axioms` for every headline theorem (see `ThetaSum/MainTheorems.lean`) lists only `propext`, `Classical.choice` and `Quot.sound`.

```
lake exe cache get   # download compiled Mathlib
lake build           # about 30 minutes from scratch on 4 cores
lake env lean ThetaSum/MainTheorems.lean   # prints the statements and axioms
```

## Definitions

`S'` and `S` are copied verbatim from Google DeepMind's formal-conjectures file `ArithmeticSumS.lean` (in `Upper/Defs.lean` and `ThetaSum/Hypotheses.lean`; `ThetaSum.S_bridge` proves the copies equal by `rfl`):

```lean
def S' (h k : ℕ) : ℤ := ∑ j ∈ Finset.Ico 1 k, (-1 : ℤ) ^ (j + 1 + ⌊(h * j : ℚ) / k⌋₊)
def S (k : ℕ) : ℤ := ∑ h ∈ Finset.Ico 1 k, S' h k
```

## The one assumed input

The formal proof assumes **(HKS)**, a power-of-log saving for short Kloosterman sums (`ThetaSum/WeakHyp.lean`): for some δ > 0, θ < 1 and C, for all large primes p, all b ≢ 0 (mod p) and all N < p with log N ≥ (log p)^θ,

  |Σ_{n=1}^{N} e(b n⁻¹/p)| ≤ C N (log p)^{−δ}.

`ThetaSum.HKS_of_HBG` derives (HKS) from **(HBG)**, the bound of Bourgain and Garaev (Izv. Math. 78 (2014), Theorem 16) restricted to log N ≥ ½(log p)^{9/10}. This range lies inside the range covered by their proof (Lemma 6.5 of the paper). The Bourgain–Garaev bound itself is not formalized.

## Main results

| Result | Hypothesis | Lean |
|---|---|---|
| Conjecture 3.3: C₁k < S(k) < C₂k^{1+ε} for all large primes k | (HKS) | `ThetaSum.conjecture_3_3_of_HKS` |
| the same | (HBG) | `ThetaSum.conjecture_3_3_of_BG` |
| (HBG) implies (HKS) | — | `ThetaSum.HKS_of_HBG` |
| Upper half of Conjecture 3.3; Theorem A; \|S(p)\| ≤ 5p·H_p² | — | `ThetaSum.conjecture_3_3_upper`, `theorem_A`, `S_abs_le` |
| formal-conjectures `conjecture_4_4 n`, every n | (HKS) | `Arxiv.«2501.03234».conjecture_4_4_of_HKS` |
| S(k) > 0, > 2k, > 3k for all large primes k | (HBG) | `conjecture_1_1_eventually_of_BG`, `conjecture_3_1_eventually_of_BG`, `conjecture_3_2_eventually_of_BG` |
| S(k) > 0, > k, > 2k, > 3k for all k ≤ 2·10⁴; S(233) = 440, S(3119) = 9194 | — | `S_pos_upto`, `S_gt_self_upto`, `S_gt_two_mul_upto`, `S_gt_three_mul_upto`, `S_233`, `S_3119` (kernel computation) |
| Theorems C and C* (asymptotic formula) | Bourgain–Garaev in the range of Lemma 6.5 | `ThetaSum.theorem_C`, `ThetaSum.theorem_C_star` |
| Theorems D and D* (large divisors in progressions) | — | `ThetaSum.theorem_D`, `ThetaSum.theorem_D_star` |
| Theorem B(ii) with the constant c₀; c₀ in closed form | — | `ThetaSum.theorem_B_c0`, `ThetaSum.c0_closed_form` |
| Reciprocity law; Kloosterman's bound 2p^{3/4}; Vaaler's lemma | — | `Recip.reciprocity`, `ThetaSum.hK34`, `Vaaler.vaaler_lemma` |

The formal proofs follow the paper with some changes (for example, Kloosterman's bound replaces Weil's bound). [`PROOF_MAP.md`](PROOF_MAP.md) lists every result of the paper with its Lean counterpart and the differences.
