import ThetaSum.LowerHalf
import ThetaSum.HVProof

/-!
# The lower half of Conjecture 3.3 from (HB) and (HBG) alone

(HV) is discharged by the formalized Vaaler lemma (`hV_holds`).
-/

namespace ThetaSum

/-- **The lower half of Conjecture 3.3**, conditional on (HB) and (HBG) only. -/
theorem lower_half_HB_HBG (hB : HB) (hBG : HBG) :
    ∀ n : ℕ, ∀ᶠ k in Filter.atTop, k.Prime → (n : ℤ) * k < S k :=
  lower_half hB hV_holds hBG

/-- **The lower half of Conjecture 3.3**, from the two-sided Theorem B(ii) (`HBweak`) and (HBG). -/
theorem lower_half_HBweak_HBG (hB : HBweak) (hBG : HBG) :
    ∀ n : ℕ, ∀ᶠ k in Filter.atTop, k.Prime → (n : ℤ) * k < S k :=
  lower_half_HB_HBG (HB_of_HBweak hB) hBG

/-- The lower half with the cutoff `KW34`, conditional on (HB34) and (HBG). -/
theorem lower_half_HB34_HBG (hB : HB34) (hBG : HBG) :
    ∀ n : ℕ, ∀ᶠ k in Filter.atTop, k.Prime → (n : ℤ) * k < S k :=
  lower_half34 hB hV_holds hBG

/-- The lower half from the two-sided Theorem B with cutoff `KW34` (`HBweak34`) and (HBG). -/
theorem lower_half_HBweak34_HBG (hB : HBweak34) (hBG : HBG) :
    ∀ n : ℕ, ∀ᶠ k in Filter.atTop, k.Prime → (n : ℤ) * k < S k :=
  lower_half_HB34_HBG (HB34_of_HBweak34 hB) hBG

end ThetaSum

#print axioms ThetaSum.lower_half
#print axioms ThetaSum.lower_half_HB_HBG
#print axioms ThetaSum.lower_half_HBweak_HBG
#print axioms ThetaSum.lower_half_HBweak34_HBG
