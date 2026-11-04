import ThetaSum.Compute

/-! Kernel checks (`decide +kernel`) of `condK p` for the odd primes `p ∈ [14250, 15100)`,
in blocks of 50. -/

set_option Elab.async false

namespace ThetaSum

theorem checkK_G14250 : checkK 14250 50 = true := by decide +kernel
theorem checkK_G14300 : checkK 14300 50 = true := by decide +kernel
theorem checkK_G14350 : checkK 14350 50 = true := by decide +kernel
theorem checkK_G14400 : checkK 14400 50 = true := by decide +kernel
theorem checkK_G14450 : checkK 14450 50 = true := by decide +kernel
theorem checkK_G14500 : checkK 14500 50 = true := by decide +kernel
theorem checkK_G14550 : checkK 14550 50 = true := by decide +kernel
theorem checkK_G14600 : checkK 14600 50 = true := by decide +kernel
theorem checkK_G14650 : checkK 14650 50 = true := by decide +kernel
theorem checkK_G14700 : checkK 14700 50 = true := by decide +kernel
theorem checkK_G14750 : checkK 14750 50 = true := by decide +kernel
theorem checkK_G14800 : checkK 14800 50 = true := by decide +kernel
theorem checkK_G14850 : checkK 14850 50 = true := by decide +kernel
theorem checkK_G14900 : checkK 14900 50 = true := by decide +kernel
theorem checkK_G14950 : checkK 14950 50 = true := by decide +kernel
theorem checkK_G15000 : checkK 15000 50 = true := by decide +kernel
theorem checkK_G15050 : checkK 15050 50 = true := by decide +kernel

theorem checkK_G4_all : checkK 14250 850 = true := by
  have h0 : checkK 14250 50 = true := checkK_G14250
  have h1 : checkK 14250 100 = true := checkK_append 50 14250 50 h0 checkK_G14300
  have h2 : checkK 14250 150 = true := checkK_append 100 14250 50 h1 checkK_G14350
  have h3 : checkK 14250 200 = true := checkK_append 150 14250 50 h2 checkK_G14400
  have h4 : checkK 14250 250 = true := checkK_append 200 14250 50 h3 checkK_G14450
  have h5 : checkK 14250 300 = true := checkK_append 250 14250 50 h4 checkK_G14500
  have h6 : checkK 14250 350 = true := checkK_append 300 14250 50 h5 checkK_G14550
  have h7 : checkK 14250 400 = true := checkK_append 350 14250 50 h6 checkK_G14600
  have h8 : checkK 14250 450 = true := checkK_append 400 14250 50 h7 checkK_G14650
  have h9 : checkK 14250 500 = true := checkK_append 450 14250 50 h8 checkK_G14700
  have h10 : checkK 14250 550 = true := checkK_append 500 14250 50 h9 checkK_G14750
  have h11 : checkK 14250 600 = true := checkK_append 550 14250 50 h10 checkK_G14800
  have h12 : checkK 14250 650 = true := checkK_append 600 14250 50 h11 checkK_G14850
  have h13 : checkK 14250 700 = true := checkK_append 650 14250 50 h12 checkK_G14900
  have h14 : checkK 14250 750 = true := checkK_append 700 14250 50 h13 checkK_G14950
  have h15 : checkK 14250 800 = true := checkK_append 750 14250 50 h14 checkK_G15000
  have h16 : checkK 14250 850 = true := checkK_append 800 14250 50 h15 checkK_G15050
  exact h16

end ThetaSum
