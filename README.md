# Proof of a conjecture of Berndt, Bhat, Meyer, Xie and Zaharescu on a theta-function sum

Samson Fraser · samsonmfraser@gmail.com

For a prime p let

  S(p) = Σ_{h,j=1}^{p−1} (−1)^{j+1+⌊hj/p⌋}.

Berndt, Bhat, Meyer, Xie and Zaharescu ([arXiv:2501.03234](https://arxiv.org/abs/2501.03234), Results Math. 2026) conjectured that for any fixed C₁, C₂, ε > 0, C₁p < S(p) < C₂p^{1+ε} for all sufficiently large primes p (their Conjecture 3.3), and that S(p) > 0 for p > 5.

## The paper

**[`paper/theta_sum_conj33.pdf`](paper/theta_sum_conj33.pdf)** — *An asymptotic formula for a theta-function sum and a conjecture of Berndt, Bhat, Meyer, Xie and Zaharescu* (37 pp.; LaTeX source in [`paper/conj33/`](paper/conj33)).

- **Theorem 1.1.** |S(p)| ≤ (2/π²) p (log p + 2)² for every odd prime p, and S(p) = ½ p log p + O(p (log p)^{19/20}). Hence **Conjecture 3.3 holds**, and S(p) > Bp for every fixed B and all large p.
- **Theorem 1.3.** A new elementary estimate for the large divisors of the terms of an arithmetic progression, valid for progressions of every length.
- **Proposition 1.2.** For all odd primes p ≤ 6·10⁶: S(p) > 0; S(p) > 2p if p > 233; S(p) > 3p if p > 3119 (Conjectures 1.1, 3.1, 3.2 in this range), by exact computation; these thresholds are sharp. The range between 6·10⁶ and the (uncomputed, and astronomically large) threshold of Theorem 1.1 is open.
- The one deep external input is the Bourgain–Garaev bound for short Kloosterman sums (Izv. Math. 2014, Theorem 16), used only for sums of length N with log N ≥ ½(log p)^{9/10} (Section 5). Kloosterman's bound for complete sums is proved in the paper; Weil's bound enters only through the proof of the Bourgain–Garaev bound.
- **Lean 4:** the implication "Bourgain–Garaev bound in this range ⇒ Conjecture 3.3" is formally verified (`ThetaSum.conjecture_3_3_of_BG`), starting from the definition of S in DeepMind's formal-conjectures. The bound itself enters as a hypothesis and is not formalized. See Appendix A of the paper and [`lean/`](lean).

## Contents

| Folder | Contents |
|---|---|
| [`paper/`](paper) | The paper ([`theta_sum_conj33.pdf`](paper/theta_sum_conj33.pdf), LaTeX source in `conj33/`) and scripts that check its numerical claims (`checks/`) |
| [`lean/`](lean) | Lean 4 / Mathlib formalization, with a [proof map](lean/PROOF_MAP.md) from the paper to Lean |
| [`code/`](code), [`data/`](data) | Programs for S(p), and exact values of S(p) for all odd primes up to 6·10⁶ |

## Formalization

`lean/` (about 17,000 lines) proves, **assuming the Bourgain–Garaev bound as the hypothesis (HBG)**, Conjecture 3.3 for the definition of S in Google DeepMind's [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (`ThetaSum.conjecture_3_3_of_BG`) and that file's statement `conjecture_4_4` (`Arxiv.«2501.03234».conjecture_4_4_of_BG`). It also proves both from a weaker power-of-log saving (HKS), which it derives from (HBG) (`ThetaSum.HKS_of_HBG`). The Bourgain–Garaev bound itself is not formalized. There is no `sorry`, and every headline theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

The headline theorem states Conjecture 3.3 exactly, for the formal-conjectures definition of S:

```lean
theorem conjecture_3_3_of_BG (hBG : HBG) : ∀ C₁ C₂ ε : ℝ, 0 < C₁ → 0 < C₂ → 0 < ε →
    ∀ᶠ k : ℕ in Filter.atTop, k.Prime →
      C₁ * k < (S k : ℝ) ∧ (S k : ℝ) < C₂ * (k : ℝ) ^ (1 + ε)
```

```
cd lean
lake exe cache get
lake build
```

## How this was made

The research presented here is the result of human–AI interaction with Claude Opus 5.5. I chose the problem and directed the project. The AI system found the approach through a reciprocity law for half-range cotangent sums, which reduces S(p) to tangent sums that can be controlled by the Bourgain–Garaev bound for short Kloosterman sums and by a new estimate for the large divisors of the terms of an arithmetic progression; it developed the proofs and wrote the code, the Lean formalization and the text. The deduction of Conjecture 3.3 from the Bourgain–Garaev bound is checked by the Lean kernel (Appendix A). Separate AI sessions refereed each proof, checked the citations against every source that was accessible to them, and recomputed the numerical claims with independent code. The problem was not routine: the authors of the conjectures wrote that Conjecture 1.1, which Conjecture 3.3 implies for all large primes, “appears to be very difficult to prove” (Section 1). I take full responsibility for the contents and welcome detailed questions about the role of AI in this work.
