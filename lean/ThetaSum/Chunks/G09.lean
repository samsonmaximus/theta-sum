import ThetaSum.Compute

/-! Kernel checks (`decide +kernel`) of `condK p` for the odd primes `p ∈ [18100, 18800)`,
in blocks of 50. -/

set_option Elab.async false

namespace ThetaSum

theorem checkK_G18100 : checkK 18100 50 = true := by decide +kernel
theorem checkK_G18150 : checkK 18150 50 = true := by decide +kernel
theorem checkK_G18200 : checkK 18200 50 = true := by decide +kernel
theorem checkK_G18250 : checkK 18250 50 = true := by decide +kernel
theorem checkK_G18300 : checkK 18300 50 = true := by decide +kernel
theorem checkK_G18350 : checkK 18350 50 = true := by decide +kernel
theorem checkK_G18400 : checkK 18400 50 = true := by decide +kernel
theorem checkK_G18450 : checkK 18450 50 = true := by decide +kernel
theorem checkK_G18500 : checkK 18500 50 = true := by decide +kernel
theorem checkK_G18550 : checkK 18550 50 = true := by decide +kernel
theorem checkK_G18600 : checkK 18600 50 = true := by decide +kernel
theorem checkK_G18650 : checkK 18650 50 = true := by decide +kernel
theorem checkK_G18700 : checkK 18700 50 = true := by decide +kernel
theorem checkK_G18750 : checkK 18750 50 = true := by decide +kernel

theorem checkK_G9_all : checkK 18100 700 = true := by
  have h0 : checkK 18100 50 = true := checkK_G18100
  have h1 : checkK 18100 100 = true := checkK_append 50 18100 50 h0 checkK_G18150
  have h2 : checkK 18100 150 = true := checkK_append 100 18100 50 h1 checkK_G18200
  have h3 : checkK 18100 200 = true := checkK_append 150 18100 50 h2 checkK_G18250
  have h4 : checkK 18100 250 = true := checkK_append 200 18100 50 h3 checkK_G18300
  have h5 : checkK 18100 300 = true := checkK_append 250 18100 50 h4 checkK_G18350
  have h6 : checkK 18100 350 = true := checkK_append 300 18100 50 h5 checkK_G18400
  have h7 : checkK 18100 400 = true := checkK_append 350 18100 50 h6 checkK_G18450
  have h8 : checkK 18100 450 = true := checkK_append 400 18100 50 h7 checkK_G18500
  have h9 : checkK 18100 500 = true := checkK_append 450 18100 50 h8 checkK_G18550
  have h10 : checkK 18100 550 = true := checkK_append 500 18100 50 h9 checkK_G18600
  have h11 : checkK 18100 600 = true := checkK_append 550 18100 50 h10 checkK_G18650
  have h12 : checkK 18100 650 = true := checkK_append 600 18100 50 h11 checkK_G18700
  have h13 : checkK 18100 700 = true := checkK_append 650 18100 50 h12 checkK_G18750
  exact h13

end ThetaSum
