import ThetaSum.Hypotheses
import ThetaSum.Vaaler

/-!
# (HV) is a theorem

`hV_holds : HV`, from the formalized Vaaler lemma (`ThetaSum/Vaaler.lean`): the real form
`Vaaler.vaaler_real` with `N = H + 1` is exactly (HV) with `c_h = al (H+1) h`, and
`Vaaler.abs_al_le` gives `|c_h| ≤ 1/(π h)`. (It even holds at integer `x`.)
-/

open Finset

namespace ThetaSum

theorem hV_holds : HV := by
  intro H hH
  refine ⟨Vaaler.al (H + 1), fun h h1 h2 => Vaaler.abs_al_le h1 (by omega), fun x _ => ?_⟩
  have hv := Vaaler.vaaler_real (N := H + 1) (by omega) x
  have hI : Ico 1 (H + 1) = Icc 1 H := by ext h; simp only [mem_Ico, mem_Icc]; omega
  unfold Vaaler.psiStar Vaaler.Kh Vaaler.be at hv
  rw [hI] at hv
  refine hv.trans (le_of_eq ?_)
  push_cast
  have hH0 : (0 : ℝ) < H + 1 := by positivity
  have e : ∀ h : ℕ, 1 / ((H : ℝ) + 1) * (1 - h / ((H : ℝ) + 1)) * Real.cos (2 * Real.pi * h * x) =
      1 / (2 * H + 2) * (2 * ((1 - h / ((H : ℝ) + 1)) * Real.cos (2 * Real.pi * h * x))) := by
    intro h; field_simp
  simp_rw [e, ← mul_sum]
  ring

end ThetaSum

#print axioms ThetaSum.hV_holds
