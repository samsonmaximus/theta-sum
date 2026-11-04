# The assumed hypothesis, in Lean and in mathematics

The headline theorems are implications. `conjecture_3_3_of_BG` proves Conjecture 3.3 *from* (HBG), which is Lemma 5.1 of [`paper/theta_sum_conj33.pdf`](../paper/theta_sum_conj33.pdf), and `conjecture_3_3_of_HKS` proves it *from* the weaker (HKS). This page shows exactly what is assumed, why the assumption is not vacuous, and where it is used. A reader of the formalization should check this page first.

## (HBG): Lemma 5.1, the Bourgain–Garaev bound in a restricted range

`ThetaSum/Hypotheses.lean`:

```lean
noncomputable def psiP (p : ℕ) (x : ZMod p) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((x.val : ℝ) / p))

def HBG : Prop :=
  ∃ C : ℝ, ∀ᶠ p : ℕ in Filter.atTop, p.Prime →
    ∀ b : ZMod p, b ≠ 0 → ∀ N : ℕ, Real.log p ^ (9 / 10 : ℝ) / 2 ≤ Real.log N → N < p →
      ‖∑ n ∈ Icc 1 N, psiP p (b * (n : ZMod p)⁻¹)‖ ≤
        C * Real.log (Real.log p) ^ 3 * Real.log p * Real.log N ^ (-(3 / 2 : ℝ)) * N
```

In mathematics: there is a constant C such that for all sufficiently large primes p, all b ≢ 0 (mod p), and all N < p with log N ≥ ½ (log p)^{9/10},

  |Σ_{1 ≤ n ≤ N} e(b n\*/p)| ≤ C (log log p)³ (log p) (log N)^{−3/2} N,

where n\* is the inverse of n modulo p and e(x) = e^{2πix}. This is the statement of Lemma 5.1 of the paper, in the same range.

**Source.** J. Bourgain and M. Z. Garaev, *Sumsets of reciprocals in prime fields and multilinear Kloosterman sums*, Izv. Math. 78 (2014), 656–707; arXiv:1211.4184, Theorem 16. The theorem is stated with no hypothesis on N, so Lemma 5.1 is a special case of it as stated. The proof of Lemma 5.1 in the paper also explains why the proof of Theorem 16 covers the range log N > C^{2/3}(log p)^{2/3}(log log p)^{8/3}, which contains the range above for all large p. Checking this against the source is the one step of the argument that is not machine-checked.

## (HKS): any power-of-log saving

`ThetaSum/WeakHyp.lean`:

```lean
def HKS : Prop :=
  ∃ δ θ C : ℝ, 0 < δ ∧ θ < 1 ∧ ∀ᶠ p : ℕ in Filter.atTop, p.Prime →
    ∀ b : ZMod p, b ≠ 0 → ∀ N : ℕ, Real.log p ^ θ ≤ Real.log N → N < p →
      ‖∑ n ∈ Icc 1 N, psiP p (b * (n : ZMod p)⁻¹)‖ ≤ C * N * Real.log p ^ (-δ)
```

`HKS_of_HBG : HBG → HKS` is proved in Lean, with θ = 9/10 and δ = 1/4. So (HKS) is weaker than (HBG), and `conjecture_3_3_of_HKS` is the stronger theorem.

## Why the hypothesis is not vacuous

If an assumed hypothesis were false, every theorem proved from it would be trivially true. Three checks show this is not the case here.

1. **It is a published theorem, restricted.** (HBG) is the published bound restricted to a smaller range, with an unspecified constant, and only for large p. It is no stronger than what Bourgain and Garaev state.
2. **It is non-trivial in its range.** When log N ≥ ½ (log p)^{9/10}, the right-hand side is at most 2^{3/2} C (log log p)³ (log p)^{−0.35} N. That is o(N), so (HBG) says something real. It does not, for example, claim cancellation for very short sums. For N = 1 the sum has absolute value 1, and N = 1 lies outside the range.
3. **The edge cases are excluded.** N = 0 is excluded, because log 0 = 0 in Mathlib while (log p)^{9/10}/2 > 0. The condition N < p makes every n in 1..N invertible modulo p.

## Where it is used

(HBG) and (HKS) are each used in exactly one lemma: `block_kloost` (`ThetaSum/HeadsBG.lean`), respectively `block_kloost_KS` (`ThetaSum/WeakHyp.lean`). That lemma is the Lean form of Corollary 5.3: it combines the reduction of Lemma 5.2 (`odd_interval_bound`) with the hypothesis, and bounds the Kloosterman sums over a dyadic block of moduli k ≥ K_*. Through Lemma 6.4 (`block_heads`) it bounds the heads of the tangent sums for K_* ≤ k < K_W, which is Step 4 of the proof of Theorem 1.1(b) in Section 8. Everything else in the dependency tree of `conjecture_3_3_of_BG` is proved; see [`PROOF_MAP.md`](PROOF_MAP.md).

## Other hypotheses defined in the Lean files

None of these is an assumption of `conjecture_3_3_of_BG` or `conjecture_3_3_of_HKS`.

| Name | File | Statement | Status |
|---|---|---|---|
| `HV` | `ThetaSum/Hypotheses.lean` | Vaaler's lemma (Lemma 6.2) in real form | Proved: `ThetaSum.hV_holds`. |
| `HK34` | `ThetaSum/Kloosterman.lean`; `TheoremB.HK34` in `Upper/TheoremB.lean` | Kloosterman's bound \|Kl(b, ν; p)\| ≤ 2p^{3/4} (Lemma 4.2) | Proved: `ThetaSum.hK34`; `HK34_bridge` gives the `TheoremB` form. |
| `HBweak34`, `HB34` | `ThetaSum/Hypotheses.lean`, `Upper/TheoremB.lean` | Theorem 4.1(ii) for K = ⌊p^{3/4}(log p)⁴⌋, with an unspecified constant c and error O(p); `HB34` is its one-sided form | Proved: `ThetaSum.hBweak34`, `HB34_of_HBweak34`. |
| `HBweak`, `HB` | `ThetaSum/Hypotheses.lean` | the same with the cutoff ⌊√p(log p)⁴⌋ | Not proved. By Remark 4.5 they would follow from Weil's bound. Used only by `conjecture_3_3` and `lower_half`, which the paper does not use. |
| `TheoremB.HW` | `Upper/TheoremB.lean` | Weil's bound for complete Kloosterman sums | Not proved and not used by any headline theorem. |
| `HBGfull` | `ThetaSum/TheoremC.lean` | the Bourgain–Garaev bound for log N ≥ A(log p)^{2/3}(log log p)^{8/3} | Not proved. Stronger than (HBG). Assumed only by `theorem_C`, `theorem_C_star`, `theorem_C_c0` and `theorem_C_star_c0`, which the paper does not use. |

## How to check

```
lake exe cache get
lake build
lake env lean ThetaSum/MainTheorems.lean   # prints each statement and its axioms
```

Each `#print axioms` should list only `propext`, `Classical.choice` and `Quot.sound`. A hypothesis such as `HBG` appears as an argument of the theorem, not as an axiom.
