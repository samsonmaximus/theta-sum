import Mathlib

/-!
Definitions copied verbatim from the google-deepmind formal-conjectures repository:
https://raw.githubusercontent.com/google-deepmind/formal-conjectures/main/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean
(only the imports / module header were adapted so that this compiles with plain Mathlib).
-/

namespace Arxiv.«2501.03234»

section SumS

open Nat Finset BigOperators in

/--
Define the sum
$$S'(h, k) := \sum_{j=1}^{k-1}(-1)^{j + 1 + \lfloor \frac{hj}{k}\rfloor}.$$
-/
-- Using "S'" instead of "S", like it is in the paper, to avoid overloading function name.
def S' (h k : ℕ) : ℤ := ∑ j ∈ Finset.Ico 1 k, (-1 : ℤ) ^ (j + 1 + ⌊(h * j : ℚ) / k⌋₊)

/--
Define the sum
$$S(k) := \sum_{h=1}^{k-1}S'(h, k)$$
-/
def S (k : ℕ) : ℤ := ∑ h ∈ Finset.Ico 1 k, S' h k

end SumS

end Arxiv.«2501.03234»
