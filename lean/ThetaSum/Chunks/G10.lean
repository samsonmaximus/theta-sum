import ThetaSum.Compute

/-! Kernel checks (`decide +kernel`) of `condK p` for the odd primes `p ∈ [18800, 19450)`,
in blocks of 50. -/

set_option Elab.async false

namespace ThetaSum

theorem checkK_G18800 : checkK 18800 50 = true := by decide +kernel
theorem checkK_G18850 : checkK 18850 50 = true := by decide +kernel
theorem checkK_G18900 : checkK 18900 50 = true := by decide +kernel
theorem checkK_G18950 : checkK 18950 50 = true := by decide +kernel
theorem checkK_G19000 : checkK 19000 50 = true := by decide +kernel
theorem checkK_G19050 : checkK 19050 50 = true := by decide +kernel
theorem checkK_G19100 : checkK 19100 50 = true := by decide +kernel
theorem checkK_G19150 : checkK 19150 50 = true := by decide +kernel
theorem checkK_G19200 : checkK 19200 50 = true := by decide +kernel
theorem checkK_G19250 : checkK 19250 50 = true := by decide +kernel
theorem checkK_G19300 : checkK 19300 50 = true := by decide +kernel
theorem checkK_G19350 : checkK 19350 50 = true := by decide +kernel
theorem checkK_G19400 : checkK 19400 50 = true := by decide +kernel

theorem checkK_G10_all : checkK 18800 650 = true := by
  have h0 : checkK 18800 50 = true := checkK_G18800
  have h1 : checkK 18800 100 = true := checkK_append 50 18800 50 h0 checkK_G18850
  have h2 : checkK 18800 150 = true := checkK_append 100 18800 50 h1 checkK_G18900
  have h3 : checkK 18800 200 = true := checkK_append 150 18800 50 h2 checkK_G18950
  have h4 : checkK 18800 250 = true := checkK_append 200 18800 50 h3 checkK_G19000
  have h5 : checkK 18800 300 = true := checkK_append 250 18800 50 h4 checkK_G19050
  have h6 : checkK 18800 350 = true := checkK_append 300 18800 50 h5 checkK_G19100
  have h7 : checkK 18800 400 = true := checkK_append 350 18800 50 h6 checkK_G19150
  have h8 : checkK 18800 450 = true := checkK_append 400 18800 50 h7 checkK_G19200
  have h9 : checkK 18800 500 = true := checkK_append 450 18800 50 h8 checkK_G19250
  have h10 : checkK 18800 550 = true := checkK_append 500 18800 50 h9 checkK_G19300
  have h11 : checkK 18800 600 = true := checkK_append 550 18800 50 h10 checkK_G19350
  have h12 : checkK 18800 650 = true := checkK_append 600 18800 50 h11 checkK_G19400
  exact h12

end ThetaSum
