# The theta-function sum S(p) and a conjecture of Berndt, Bhat, Meyer, Xie and Zaharescu

Samson Fraser · samsonmfraser@gmail.com

For a prime p let

  S(p) = Σ_{h,j=1}^{p−1} (−1)^{j+1+⌊hj/p⌋}.

Berndt, Bhat, Meyer, Xie and Zaharescu ([arXiv:2501.03234](https://arxiv.org/abs/2501.03234), Results Math. 2026) conjectured that C₁p < S(p) < C₂p^{1+ε} for all large primes p (their Conjecture 3.3), and that S(p) > 0, S(p) > 2p for p > 233 and S(p) > 3p for p > 3119.

## Results

- **Conjecture 3.3 holds.** In fact S(p) = (p/2) log p + O(p (log p)^{2/3} (log log p)^{17/3}) (Theorem C*).
- The proof needs only a power-of-log saving for short Kloosterman sums of length exp((log p)^θ) with θ < 1 (Theorem C♭). The bound of Bourgain and Garaev (2014) provides it.
- S(p) > 0, > 2p and > 3p for all sufficiently large primes, and for all p ≤ 6·10⁶ by exact computation. The primes in between remain open.
- A new elementary estimate for large divisors of the terms of an arithmetic progression (Theorems D and D*).
- Companion paper: S(p)/p − ½ log p has a limiting distribution over the primes, with an explicit character expansion, sharp tails and extreme values of order (log log p)².

## Contents

| Folder | Contents |
|---|---|
| [`paper/`](paper) | The main paper ([`theta_sum.pdf`](paper/theta_sum.pdf)), its LaTeX source, and scripts that check its numerical claims |
| [`companion/`](companion) | The companion paper on the distribution of S(p) |
| [`lean/`](lean) | Lean 4 / Mathlib formalization, with a [proof map](lean/PROOF_MAP.md) from the paper to Lean |
| [`code/`](code), [`data/`](data) | Programs for S(p), and exact values of S(p) for all primes up to 6·10⁶ |

## Formalization

`lean/` (about 17,000 lines) proves Conjecture 3.3 in the exact statement of Google DeepMind's [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) repository (`ThetaSum.conjecture_3_3_of_HKS`). It assumes a power-of-log saving for short Kloosterman sums, and derives that saving from the Bourgain–Garaev bound (`ThetaSum.HKS_of_HBG`). The Bourgain–Garaev bound itself is the one input that is not formalized. There is no `sorry`, and every headline theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

```
cd lean
lake exe cache get
lake build
```

## How this was made

I used Claude Opus 5.5 (Anthropic) throughout this project, for the literature search, the arguments, the code, the Lean formalization and the text, and had every part checked by separate Claude sessions acting as referees. These checks do not replace expert refereeing; the papers have not yet been refereed. The full statement is at the end of the main paper. Comments and corrections are welcome by email.
