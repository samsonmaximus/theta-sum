import ThetaSum.Headline
import ThetaSum.FiniteRange

/-!
# The formal-conjectures file `Arxiv/2501.03234/ArithmeticSumS.lean`, answered

Every theorem statement of
https://raw.githubusercontent.com/google-deepmind/formal-conjectures/main/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean
is copied below with its name and statement text. The definitions `S'`, `S` are theirs, verbatim
(`Upper/Defs.lean`, namespace `Arxiv.«2501.03234»`; `ThetaSum.S_bridge` identifies them with
`ThetaSum.S` by `rfl`). Only the `@[category …]` attributes are dropped. The five open statements
are stated as `Prop`s under their own names (their file proves them by `sorry`), followed by what
we prove about each:

| statement | proved here |
|---|---|
| `S_fst_10` | the statement (test) |
| `conjecture_1_1` | for all `k ≤ 2·10⁴` (unconditional); for all large `k` under (HBG) |
| `conjecture_4_1` | for all `k ≤ 2·10⁴` (unconditional); for all large `k` under (HBG) |
| `conjecture_4_2` | for all `k ≤ 2·10⁴` (unconditional); for all large `k` under (HBG) |
| `conjecture_4_3` | for all `k ≤ 2·10⁴` (unconditional); for all large `k` under (HBG) |
| `conjecture_4_4 n` | the full statement, for every `n`, under (HBG) |
| `conjecture_4_4_def_0..3` | the statements (implications) |

Open: the full `∀ k` statements 1.1 and 4.1–4.3 for the primes beyond `2·10⁴` that lie below the
(ineffective) threshold of the `HBG`-conditional results, and (HBG) itself — the Bourgain–Garaev
bound for short Kloosterman sums, a published theorem not formalized here.

Small `k`: their `conjecture_1_1` has no `k > 5` condition; it is nevertheless true for the small
primes, `S 3 = 2`, `S 5 = 4`, `S 7 = 10` (`S_fst_10`), and the `k > 5` in `conjecture_4_1` is needed
there (`S 3 = 2 < 3`, `S 5 = 4 < 5`).
-/

open Filter

namespace ThetaSum

/-! ### A kernel check of `S(p) > p` for `5 < p < 234` (for Conjecture 4.1) -/

def cond41 (p : ℕ) : Bool :=
  Nat.blt (Nat.add p (Nat.mul 4 (sumLoop p ((p - 3) / 2)))) ((p - 1) ^ 3 / 4)

def check41 (lo N : ℕ) : Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun _ ih n => Bool.and
      (Bool.or (Bool.not (Bool.and (Nat.beq (Nat.mod n 2) 1) (trialK n))) (cond41 n))
      (ih (Nat.add n 1))) N lo

lemma check41_sound : ∀ N lo, check41 lo N = true →
    ∀ p, lo ≤ p → p < lo + N → p.Prime → p ≠ 2 → cond41 p = true := by
  intro N
  induction N with
  | zero => intro lo _ p h1 h2; omega
  | succ N ih =>
    intro lo h p h1 h2 hp hp2
    have h' : Bool.and
        (Bool.or (Bool.not (Bool.and (Nat.beq (Nat.mod lo 2) 1) (trialK lo))) (cond41 lo))
        (check41 (lo + 1) N) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.lt_or_ge lo p with hlt | hge
    · exact ih (lo + 1) h'.2 p (by omega) (by omega) hp hp2
    · have hpl : p = lo := by omega
      subst hpl
      have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
      have h1' := h'.1
      rw [Bool.or_eq_true] at h1'
      rcases h1' with h1' | h1'
      · exfalso
        have hb : Nat.beq (Nat.mod p 2) 1 = true := by rw [show Nat.mod p 2 = 1 from hodd]; rfl
        rw [hb, trialK_of_prime p hp] at h1'
        exact absurd h1' (by decide)
      · exact h1'

theorem check41_ok : check41 6 228 = true := by decide +kernel

theorem S_gt_self_upto (p : ℕ) (hp : p ≤ 20000) (hpr : p.Prime) (h : 5 < p) : (p : ℤ) < S p := by
  rcases Nat.lt_or_ge 233 p with h1 | h1
  · have := S_gt_two_mul_upto p hp hpr h1; omega
  · have hc := check41_sound 228 6 check41_ok p (by omega) (by omega) hpr (by omega)
    rw [← Sfast_eq p hpr (by omega), Sfast]
    unfold cond41 at hc; rw [Nat.blt_eq] at hc
    generalize ThetaSum.sumLoop p ((p - 3) / 2) = s at hc
    generalize (p - 1) ^ 3 / 4 = m at hc
    change p + 4 * s < m at hc
    omega

end ThetaSum

namespace Arxiv.«2501.03234»

/-! ### The statements of the formal-conjectures file -/

/--
Note that in Table 1 in https://arxiv.org/abs/2501.03234v1, there seems to be an error:
11 appears twice. The first 10 values of $S$.
-/
theorem S_fst_10 : List.map S (List.range 10) = [0, 0, 1, 2, 5, 4, 7, 10, 11, 8] := by
  unfold S
  decide +kernel

set_option linter.unusedVariables false

/--
**Conjecture 1.1**: For any odd prime $k$, the sum associated with the classical theta function $θ_3$,
$S(k)$ is positive. (Their `theorem conjecture_1_1 (k : ℕ) (hprim : k.Prime) (hodd : Odd k) :
0 < S k`, as a `Prop`. **Open** in general; see `conjecture_1_1_upto`,
`conjecture_1_1_eventually_of_BG`.)
-/
def conjecture_1_1 : Prop := ∀ (k : ℕ) (hprim : k.Prime) (hodd : Odd k), 0 < S k

/--
**Conjecture 4.1**: For any prime $k$ larger than $5$, $S(k) > k$. (**Open** in general.)
-/
def conjecture_4_1 : Prop := ∀ (k : ℕ) (hprim : k.Prime) (hodd : Odd k) (hgt : k > 5), k < S k

/--
**Conjecture 4.2**: For any prime $k$ larger than $233$, $S(k) > 2k$. (**Open** in general.)
-/
def conjecture_4_2 : Prop := ∀ (k : ℕ) (hprim : k.Prime) (hodd : Odd k) (hgt : k > 233), 2 * k < S k

/--
**Conjecture 4.3**: For any prime $k$ larger than $3119$, $S(k) > 3k$. (**Open** in general.)
-/
def conjecture_4_3 : Prop :=
  ∀ (k : ℕ) (hprim : k.Prime) (hodd : Odd k) (hgt : k > 3119), 3 * k < S k

/--
**Conjecture 4.4**: Given a natural number $n ∈ ℕ$, for all large enough odd prime $k$ (depending on $n$),
$nk < S(k)$. (**Proved under (HBG)**: `conjecture_4_4_of_BG`.)
-/
def conjecture_4_4 (n : ℕ) : Prop :=
  ∀ᶠ (k : ℕ) in Filter.atTop, k.Prime → Odd k → n * k < S k

/-! ### What we prove -/

/-- **Conjecture 4.4, in full, for every `n`, assuming only (HBG)** (the Bourgain–Garaev bound).
Everything else is proved: Theorem B with Kloosterman's bound, Vaaler's lemma, Theorem D, … -/
theorem conjecture_4_4_of_BG (hBG : ThetaSum.HBG) (n : ℕ) : conjecture_4_4 n := by
  unfold conjecture_4_4
  filter_upwards [ThetaSum.lower_half_HBweak34_HBG ThetaSum.hBweak34 hBG n] with k hk hp _
  rw [ThetaSum.S_bridge]; exact hk hp

/-- Conjecture 1.1 for every odd prime `k ≤ 2·10⁴` (unconditional; kernel-checked computation). -/
theorem conjecture_1_1_upto (k : ℕ) (hk : k ≤ 20000) (hprim : k.Prime) (hodd : Odd k) :
    0 < S k := by
  rw [ThetaSum.S_bridge]; exact ThetaSum.S_pos_upto k hk hprim

/-- Conjecture 4.1 for every prime `5 < k ≤ 2·10⁴` (unconditional). -/
theorem conjecture_4_1_upto (k : ℕ) (hk : k ≤ 20000) (hprim : k.Prime) (hodd : Odd k)
    (hgt : k > 5) : k < S k := by
  rw [ThetaSum.S_bridge]; exact ThetaSum.S_gt_self_upto k hk hprim hgt

/-- Conjecture 4.2 for every prime `233 < k ≤ 2·10⁴` (unconditional). -/
theorem conjecture_4_2_upto (k : ℕ) (hk : k ≤ 20000) (hprim : k.Prime) (hodd : Odd k)
    (hgt : k > 233) : 2 * k < S k := by
  rw [ThetaSum.S_bridge]; exact ThetaSum.S_gt_two_mul_upto k hk hprim hgt

/-- Conjecture 4.3 for every prime `3119 < k ≤ 2·10⁴` (unconditional). -/
theorem conjecture_4_3_upto (k : ℕ) (hk : k ≤ 20000) (hprim : k.Prime) (hodd : Odd k)
    (hgt : k > 3119) : 3 * k < S k := by
  rw [ThetaSum.S_bridge]; exact ThetaSum.S_gt_three_mul_upto k hk hprim hgt

/-- Conjecture 1.1 for all sufficiently large primes, under (HBG). -/
theorem conjecture_1_1_eventually_of_BG (hBG : ThetaSum.HBG) :
    ∀ᶠ (k : ℕ) in Filter.atTop, ∀ (hprim : k.Prime) (hodd : Odd k), 0 < S k := by
  filter_upwards [conjecture_4_4_of_BG hBG 0] with k hk hp ho
  simpa using hk hp ho

/-- Conjecture 4.1 for all sufficiently large primes, under (HBG). -/
theorem conjecture_4_1_eventually_of_BG (hBG : ThetaSum.HBG) :
    ∀ᶠ (k : ℕ) in Filter.atTop, ∀ (hprim : k.Prime) (hodd : Odd k) (hgt : k > 5), k < S k := by
  filter_upwards [conjecture_4_4_of_BG hBG 1] with k hk hp ho _
  simpa using hk hp ho

/-- Conjecture 4.2 for all sufficiently large primes, under (HBG). -/
theorem conjecture_4_2_eventually_of_BG (hBG : ThetaSum.HBG) :
    ∀ᶠ (k : ℕ) in Filter.atTop, ∀ (hprim : k.Prime) (hodd : Odd k) (hgt : k > 233),
      2 * k < S k := by
  filter_upwards [conjecture_4_4_of_BG hBG 2] with k hk hp ho _
  exact_mod_cast hk hp ho

/-- Conjecture 4.3 for all sufficiently large primes, under (HBG). -/
theorem conjecture_4_3_eventually_of_BG (hBG : ThetaSum.HBG) :
    ∀ᶠ (k : ℕ) in Filter.atTop, ∀ (hprim : k.Prime) (hodd : Odd k) (hgt : k > 3119),
      3 * k < S k := by
  filter_upwards [conjecture_4_4_of_BG hBG 3] with k hk hp ho _
  exact_mod_cast hk hp ho

/-! ### The test theorems of the file (implications), proved -/

/--
**Conjecture 1.1 → Conjecture 4.4**: If conjecture 1.1 holds true, then this implies a special
case of conjecture 4.4 where $n = 0$. In this case the lower bound for the odd prime $k$
would be $0$.
-/
theorem conjecture_4_4_def_0 (hc1_1 : conjecture_1_1) : conjecture_4_4 0 := by
  unfold conjecture_4_4
  simp only [Filter.Eventually, CharP.cast_eq_zero, zero_mul, Filter.mem_atTop_sets]
  exact ⟨0, fun b sb bprim bodd ↦ hc1_1 b bprim bodd⟩

/--
**Conjecture 4.1 → Conjecture 4.4**: If conjecture 4.1 holds true, then this implies a special
case of conjecture 4.4 where $n = 1$. In this case the lower bound would be $5$.
-/
theorem conjecture_4_4_def_1 (hc4_1 : conjecture_4_1) : conjecture_4_4 1 := by
  unfold conjecture_4_4
  simp [Filter.Eventually, Filter.mem_atTop_sets]
  exact ⟨5+1, fun b sb bprim bodd ↦ hc4_1 b bprim bodd (by linarith)⟩

/--
**Conjecture 4.2 → Conjecture 4.4**: If conjecture 4.2 holds true, then this implies a special
case of conjecture 4.4 for $n = 2$. For this scenario, the lower bound is now $233$.
-/
theorem conjecture_4_4_def_2 (hc4_2 : conjecture_4_2) : conjecture_4_4 2 := by
  unfold conjecture_4_4
  simp only [Filter.Eventually, Filter.mem_atTop_sets]
  exact ⟨233+1, fun b sb bprim bodd ↦ hc4_2 b bprim bodd (by linarith)⟩

/--
**Conjecture 4.3 → Conjecture 4.4**: If conjecture 4.3 holds true, then a special
case of conjecture 4.4 for $n = 3$ is obtained, and the lower bound is $3119$.
-/
theorem conjecture_4_4_def_3 (hc4_3 : conjecture_4_3) : conjecture_4_4 3 := by
  unfold conjecture_4_4
  simp only [Filter.Eventually, Filter.mem_atTop_sets]
  exact ⟨3119+1, fun b sb bprim bodd ↦ hc4_3 b bprim bodd (by linarith)⟩

end Arxiv.«2501.03234»
