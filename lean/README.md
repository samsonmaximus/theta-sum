# Lean formalization

This directory contains the Lean 4 formalization of the proof of Conjecture 3.3 of Berndt, Bhat, Meyer, Xie and Zaharescu (arXiv:2501.03234) in [`paper/theta_sum_conj33.pdf`](../paper/theta_sum_conj33.pdf). All theorem, lemma and section numbers in this directory refer to that paper. Its Appendix A describes the formalization, and the table in its Section 8.3 lists the main correspondences.

Lean 4 with Mathlib v4.35.0, about 17,000 lines. No `sorry`, no `native_decide`, and no added axioms: `#print axioms` for every headline theorem (see `ThetaSum/MainTheorems.lean`) lists only `propext`, `Classical.choice` and `Quot.sound`.

```
lake exe cache get   # download compiled Mathlib
lake build           # about 30 minutes from scratch on 4 cores
lake env lean ThetaSum/MainTheorems.lean   # prints the statements and axioms
```

## Definitions

`S'` and `S` are copied verbatim from Google DeepMind's formal-conjectures file `FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean` (in `Upper/Defs.lean` and `ThetaSum/Hypotheses.lean`; `ThetaSum.S_bridge` proves the copies equal by `rfl`):

```lean
def S' (h k : ℕ) : ℤ := ∑ j ∈ Finset.Ico 1 k, (-1 : ℤ) ^ (j + 1 + ⌊(h * j : ℚ) / k⌋₊)
def S (k : ℕ) : ℤ := ∑ h ∈ Finset.Ico 1 k, S' h k
```

## What is assumed

The headline theorem `ThetaSum.conjecture_3_3_of_BG` proves Conjecture 3.3 *from* the hypothesis **(HBG)** (`ThetaSum.HBG`, in `ThetaSum/Hypotheses.lean`). (HBG) is exactly Lemma 5.1 of the paper, in the same range: the bound of Bourgain and Garaev (Izv. Math. 78 (2014), Theorem 16) for the short Kloosterman sums Σ_{n≤N} e(bn\*/p), used only for log N ≥ ½(log p)^{9/10}. The Bourgain–Garaev bound is **not formalized**. It enters as an argument of the theorem, not as an axiom. Everything else in the proof is machine-checked.

`ThetaSum.conjecture_3_3_of_HKS` (`ThetaSum/WeakHyp.lean`) proves the same statement from the weaker hypothesis **(HKS)**: for some δ > 0, θ < 1 and C, for all large primes p, all b ≢ 0 (mod p) and all N < p with log N ≥ (log p)^θ,

  |Σ_{n=1}^{N} e(b n\*/p)| ≤ C N (log p)^{−δ}.

`ThetaSum.HKS_of_HBG` proves that (HBG) implies (HKS), with θ = 9/10 and δ = 1/4.

[`HYPOTHESES.md`](HYPOTHESES.md) states the hypotheses in full and lists where each is used.

## Main results

| Paper | Statement | Hypothesis | Lean |
|---|---|---|---|
| Conjecture 3.3 | C₁k < S(k) < C₂k^{1+ε} for all large primes k | (HBG) = Lemma 5.1 | `ThetaSum.conjecture_3_3_of_BG` |
| Conjecture 3.3 | the same | (HKS) | `ThetaSum.conjecture_3_3_of_HKS` |
| — | (HBG) implies (HKS) | — | `ThetaSum.HKS_of_HBG` |
| Theorem 1.1(a), Proposition 2.5 | \|S(p)\| ≤ (2/p)C_p(1)² ≤ (2/π²)p(log p + 2)² | — | `Arxiv.«2501.03234».theorem_A`, `Arxiv.«2501.03234».S_abs_le_cot` |
| Corollary 2.6 | upper half of Conjecture 3.3 | — | `ThetaSum.conjecture_3_3_upper` |
| Theorem 1.1(b), weak form | S(p) > Bp for every fixed B and all large primes p, i.e. S(p)/p → ∞ (not the exponent 19/20) | (HBG) | `ThetaSum.lower_half_HBweak34_HBG`; formal-conjectures form `Arxiv.«2501.03234».conjecture_4_4_of_BG` (and `conjecture_4_4_of_HKS` from (HKS)) |
| Consequences of Theorem 1.1 | Conjectures 1.1, 3.1, 3.2 for all large primes | (HBG) | `ThetaSum.conjecture_1_1_eventually_of_BG`, `conjecture_3_1_eventually_of_BG`, `conjecture_3_2_eventually_of_BG` |
| Proposition 1.2, partly | S(p) > 0, > p (p > 5), > 2p (p > 233), > 3p (p > 3119) for primes p ≤ 2·10⁴; S(233) = 440, S(3119) = 9194 | — | `ThetaSum.S_pos_upto`, `S_gt_self_upto`, `S_gt_two_mul_upto`, `S_gt_three_mul_upto`, `S_233`, `S_3119` (kernel computation) |
| Theorem 1.3 | large divisors of the terms of an arithmetic progression | — | `ThetaSum.theorem_D` |
| Theorem 4.1(i) | S(p) = Ψ(p) + T(p); Ψ(p) = (p/2)log p + c₀p + o(p) | — | `TheoremB.S_eq_Psi_Phi`, `TheoremB.Psi_asymp` |
| Theorem 4.1(ii) | for K = ⌊p^{3/4}(log p)⁴⌋, with error ≤ εp; with an unspecified constant c and error O(p) | — | `ThetaSum.theorem_B_c0`; `ThetaSum.hBweak34` |
| (2.4) | c₀ = κ₀/2 + (log 2)/6 + (3/π²)ζ′(2) | — | `ThetaSum.c0_closed_form` |
| Lemma 3.1 | reciprocity law for half-range cotangent sums | — | `Recip.reciprocity` |
| Lemma 4.2 | Kloosterman's bound \|Kl(b, ν; p)\| ≤ 2p^{3/4} | — | `ThetaSum.hK34`, `ThetaSum.kl_four_le` |
| Lemma 6.2 | Vaaler's lemma | — | `Vaaler.vaaler_lemma` |
| Lemma 9.1 | counting formula for S(p) | — | `ThetaSum.S_eq_lemma25`, `Tq_odd`, `Ffl_add`, `Ffl_recip` |

The formal-conjectures file numbers the conjectures as in the first arXiv version of arXiv:2501.03234: Conjecture 3.1 of the paper is `conjecture_4_2`, Conjecture 3.2 is `conjecture_4_3`, `conjecture_4_1` is S(k) > k for primes k > 5, and `conjecture_4_4 n` is S(k) > nk for all large primes k. `ThetaSum/FormalConjectures.lean` restates that file and records what is proved about each statement.

The formal proof follows Sections 2–8 of the paper, with some differences: some constants differ; Lemma 6.6 is formalized in an elementary version that does not use Vaaler's lemma; the reciprocity law is proved without contour integration; Kloosterman's bound is used in the form |Kl|⁴ ≤ 3p³; the Lean assembly proves S(p)/p → ∞ rather than the explicit exponent 19/20 of Theorem 1.1(b); and the cutoff K_W is rounded down to ⌊p^{3/4}(log p)⁴⌋. [`PROOF_MAP.md`](PROOF_MAP.md) lists the results of the paper section by section, with their Lean counterparts and the differences.

## Further results not used in the paper

The formalization also contains these results. The paper does not use them.

- `ThetaSum.theorem_C`, `ThetaSum.theorem_C_star` (and `theorem_C_c0`, `theorem_C_star_c0`): S(p) = (p/2)log p + O(p(log p)^{2/3+γ₀}(log log p)^{8/3}) for each γ₀ ∈ (0, 2/3), and S(p) = (p/2)log p + O(p(log p)^{2/3}(log log p)^{17/3}). Both assume **(HBGfull)** (`ThetaSum.HBGfull`), the Bourgain–Garaev bound for log N ≥ A(log p)^{2/3}(log log p)^{8/3}. This hypothesis is stronger than (HBG).
- `ThetaSum.theorem_D_star`: a variant of Theorem 1.3 with log T ≥ (log log q)³, stated for log log q ≥ 1000.
- `Arxiv.«2501.03234».S_abs_le`: |S(p)| ≤ 5p·H_p², an elementary upper bound (the Lean proof of the upper half of Conjecture 3.3 goes through this bound).
- `Arxiv.«2501.03234».Fsum_eq_sum_Gsum`, `Gsum_avg`, `Gsum_abs_le`: the decomposition F_k(n) = Σ_{d∣k, d≥3} G_d(n) of the tangent sums into sums over reduced residues, their averages over residue classes, and |G_d(n)| ≤ G_d(1).

## Layout

- `Upper/`: the definitions, the dual formula, the upper bound, the reciprocity law and the decomposition of Theorem 4.1 (namespaces `Arxiv.«2501.03234»`, `Recip`, `TheoremB`).
- `ThetaSum/`: Kloosterman's bound, the constant c₀, the heads and tails of Sections 6 and 8, Theorem 1.3, the assembly, the finite range and the headline theorems (mostly namespace `ThetaSum`; Vaaler's lemma is in namespace `Vaaler`). `ThetaSum/Headline.lean` links the two parts.
- `ThetaSum/MainTheorems.lean`: prints the statement and the axioms of every headline result.
