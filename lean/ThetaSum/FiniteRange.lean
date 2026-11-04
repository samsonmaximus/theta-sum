import ThetaSum.Compute
import ThetaSum.Chunks.F0
import ThetaSum.Chunks.F1
import ThetaSum.Chunks.F2
import ThetaSum.Chunks.F3
import ThetaSum.Chunks.F4
import ThetaSum.Chunks.F5
import ThetaSum.Chunks.F6
import ThetaSum.Chunks.F7
import ThetaSum.Chunks.G00
import ThetaSum.Chunks.G01
import ThetaSum.Chunks.G02
import ThetaSum.Chunks.G03
import ThetaSum.Chunks.G04
import ThetaSum.Chunks.G05
import ThetaSum.Chunks.G06
import ThetaSum.Chunks.G07
import ThetaSum.Chunks.G08
import ThetaSum.Chunks.G09
import ThetaSum.Chunks.G10
import ThetaSum.Chunks.G11

/-!
# The finite range of Conjectures 1.1, 3.1, 3.2, machine-checked

All primes `p ≤ 20000`: `S(p) > 0`; `S(p) > 2p` for `p > 233`; `S(p) > 3p` for `p > 3119`;
and the thresholds are sharp: `S(233) = 440 < 2·233`, `S(3119) = 9194 < 3·3119`.
The computation is kernel-checked (`decide +kernel`, no `native_decide`) in the files
`ThetaSum/Chunks/F*.lean` (blocks of 100, `p < 10100`) and `ThetaSum/Chunks/G*.lean` (blocks of 50,
`10100 ≤ p < 20100`), via the verified evaluator `Sfast` (`Sfast_eq`).
-/

namespace ThetaSum

theorem checkK_10100 : checkK 0 10100 = true := by
  have h0 : checkK 0 3600 = true := checkK_F0
  have h1 : checkK 0 5000 = true := checkK_append 3600 0 1400 h0 checkK_F1
  have h2 : checkK 0 6200 = true := checkK_append 5000 0 1200 h1 checkK_F2
  have h3 : checkK 0 7100 = true := checkK_append 6200 0 900 h2 checkK_F3
  have h4 : checkK 0 8000 = true := checkK_append 7100 0 900 h3 checkK_F4
  have h5 : checkK 0 8700 = true := checkK_append 8000 0 700 h4 checkK_F5
  have h6 : checkK 0 9400 = true := checkK_append 8700 0 700 h5 checkK_F6
  have h7 : checkK 0 10100 = true := checkK_append 9400 0 700 h6 checkK_F7
  exact h7

theorem checkK_all : checkK 0 20100 = true := by
  have g0 : checkK 0 11300 = true := checkK_append 10100 0 1200 checkK_10100 checkK_G0_all
  have g1 : checkK 0 12350 = true := checkK_append 11300 0 1050 g0 checkK_G1_all
  have g2 : checkK 0 13300 = true := checkK_append 12350 0 950 g1 checkK_G2_all
  have g3 : checkK 0 14250 = true := checkK_append 13300 0 950 g2 checkK_G3_all
  have g4 : checkK 0 15100 = true := checkK_append 14250 0 850 g3 checkK_G4_all
  have g5 : checkK 0 15900 = true := checkK_append 15100 0 800 g4 checkK_G5_all
  have g6 : checkK 0 16700 = true := checkK_append 15900 0 800 g5 checkK_G6_all
  have g7 : checkK 0 17400 = true := checkK_append 16700 0 700 g6 checkK_G7_all
  have g8 : checkK 0 18100 = true := checkK_append 17400 0 700 g7 checkK_G8_all
  have g9 : checkK 0 18800 = true := checkK_append 18100 0 700 g8 checkK_G9_all
  have g10 : checkK 0 19450 = true := checkK_append 18800 0 650 g9 checkK_G10_all
  have g11 : checkK 0 20100 = true := checkK_append 19450 0 650 g10 checkK_G11_all
  exact g11

theorem condK_upto (p : ℕ) (hp : p ≤ 20000) (hpr : p.Prime) (hp2 : p ≠ 2) : condK p = true :=
  checkK_sound 20100 0 checkK_all p (Nat.zero_le _) (by omega) hpr hp2

lemma S_two : S 2 = 1 := by
  rw [S]; simp [S'_eq]

/-- Conjecture 1.1 for all primes `p ≤ 2·10⁴`: `S(p) > 0`. -/
theorem S_pos_upto (p : ℕ) (hp : p ≤ 20000) (hpr : p.Prime) : 0 < S p := by
  rcases eq_or_ne p 2 with h2 | h2
  · subst h2; rw [S_two]; norm_num
  · exact (condK_spec p hpr h2 (condK_upto p hp hpr h2)).1

/-- Conjecture 3.1 for all primes `233 < p ≤ 2·10⁴`: `S(p) > 2p`. -/
theorem S_gt_two_mul_upto (p : ℕ) (hp : p ≤ 20000) (hpr : p.Prime) (h : 233 < p) :
    2 * (p : ℤ) < S p :=
  (condK_spec p hpr (by omega) (condK_upto p hp hpr (by omega))).2.1 h

/-- Conjecture 3.2 for all primes `3119 < p ≤ 2·10⁴`: `S(p) > 3p`. -/
theorem S_gt_three_mul_upto (p : ℕ) (hp : p ≤ 20000) (hpr : p.Prime) (h : 3119 < p) :
    3 * (p : ℤ) < S p :=
  (condK_spec p hpr (by omega) (condK_upto p hp hpr (by omega))).2.2 h

/-- Sharpness of Conjecture 3.1's threshold: `S(233) = 440 < 2·233`. -/
theorem S_233 : S 233 = 440 := by
  rw [← Sfast_eq 233 (by norm_num) (by norm_num)]; decide +kernel

/-- Sharpness of Conjecture 3.2's threshold: `S(3119) = 9194 < 3·3119`. -/
theorem S_3119 : S 3119 = 9194 := by
  rw [← Sfast_eq 3119 (by norm_num) (by norm_num)]; decide +kernel

end ThetaSum

#print axioms ThetaSum.S_pos_upto
#print axioms ThetaSum.S_gt_two_mul_upto
#print axioms ThetaSum.S_gt_three_mul_upto
#print axioms ThetaSum.S_233
#print axioms ThetaSum.S_3119
#print axioms ThetaSum.Sfast_eq
#print axioms ThetaSum.S_eq_lemma25
