import ThetaSum.Compute

/-! Kernel checks (`decide +kernel`) of `condK p` for the odd primes `p ∈ [19450, 20100)`,
in blocks of 50. -/

set_option Elab.async false

namespace ThetaSum

theorem checkK_G19450 : checkK 19450 50 = true := by decide +kernel
theorem checkK_G19500 : checkK 19500 50 = true := by decide +kernel
theorem checkK_G19550 : checkK 19550 50 = true := by decide +kernel
theorem checkK_G19600 : checkK 19600 50 = true := by decide +kernel
theorem checkK_G19650 : checkK 19650 50 = true := by decide +kernel
theorem checkK_G19700 : checkK 19700 50 = true := by decide +kernel
theorem checkK_G19750 : checkK 19750 50 = true := by decide +kernel
theorem checkK_G19800 : checkK 19800 50 = true := by decide +kernel
theorem checkK_G19850 : checkK 19850 50 = true := by decide +kernel
theorem checkK_G19900 : checkK 19900 50 = true := by decide +kernel
theorem checkK_G19950 : checkK 19950 50 = true := by decide +kernel
theorem checkK_G20000 : checkK 20000 50 = true := by decide +kernel
theorem checkK_G20050 : checkK 20050 50 = true := by decide +kernel

theorem checkK_G11_all : checkK 19450 650 = true := by
  have h0 : checkK 19450 50 = true := checkK_G19450
  have h1 : checkK 19450 100 = true := checkK_append 50 19450 50 h0 checkK_G19500
  have h2 : checkK 19450 150 = true := checkK_append 100 19450 50 h1 checkK_G19550
  have h3 : checkK 19450 200 = true := checkK_append 150 19450 50 h2 checkK_G19600
  have h4 : checkK 19450 250 = true := checkK_append 200 19450 50 h3 checkK_G19650
  have h5 : checkK 19450 300 = true := checkK_append 250 19450 50 h4 checkK_G19700
  have h6 : checkK 19450 350 = true := checkK_append 300 19450 50 h5 checkK_G19750
  have h7 : checkK 19450 400 = true := checkK_append 350 19450 50 h6 checkK_G19800
  have h8 : checkK 19450 450 = true := checkK_append 400 19450 50 h7 checkK_G19850
  have h9 : checkK 19450 500 = true := checkK_append 450 19450 50 h8 checkK_G19900
  have h10 : checkK 19450 550 = true := checkK_append 500 19450 50 h9 checkK_G19950
  have h11 : checkK 19450 600 = true := checkK_append 550 19450 50 h10 checkK_G20000
  have h12 : checkK 19450 650 = true := checkK_append 600 19450 50 h11 checkK_G20050
  exact h12

end ThetaSum
