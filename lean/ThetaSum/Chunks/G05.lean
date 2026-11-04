import ThetaSum.Compute

/-! Kernel checks (`decide +kernel`) of `condK p` for the odd primes `p ∈ [15100, 15900)`,
in blocks of 50. -/

set_option Elab.async false

namespace ThetaSum

theorem checkK_G15100 : checkK 15100 50 = true := by decide +kernel
theorem checkK_G15150 : checkK 15150 50 = true := by decide +kernel
theorem checkK_G15200 : checkK 15200 50 = true := by decide +kernel
theorem checkK_G15250 : checkK 15250 50 = true := by decide +kernel
theorem checkK_G15300 : checkK 15300 50 = true := by decide +kernel
theorem checkK_G15350 : checkK 15350 50 = true := by decide +kernel
theorem checkK_G15400 : checkK 15400 50 = true := by decide +kernel
theorem checkK_G15450 : checkK 15450 50 = true := by decide +kernel
theorem checkK_G15500 : checkK 15500 50 = true := by decide +kernel
theorem checkK_G15550 : checkK 15550 50 = true := by decide +kernel
theorem checkK_G15600 : checkK 15600 50 = true := by decide +kernel
theorem checkK_G15650 : checkK 15650 50 = true := by decide +kernel
theorem checkK_G15700 : checkK 15700 50 = true := by decide +kernel
theorem checkK_G15750 : checkK 15750 50 = true := by decide +kernel
theorem checkK_G15800 : checkK 15800 50 = true := by decide +kernel
theorem checkK_G15850 : checkK 15850 50 = true := by decide +kernel

theorem checkK_G5_all : checkK 15100 800 = true := by
  have h0 : checkK 15100 50 = true := checkK_G15100
  have h1 : checkK 15100 100 = true := checkK_append 50 15100 50 h0 checkK_G15150
  have h2 : checkK 15100 150 = true := checkK_append 100 15100 50 h1 checkK_G15200
  have h3 : checkK 15100 200 = true := checkK_append 150 15100 50 h2 checkK_G15250
  have h4 : checkK 15100 250 = true := checkK_append 200 15100 50 h3 checkK_G15300
  have h5 : checkK 15100 300 = true := checkK_append 250 15100 50 h4 checkK_G15350
  have h6 : checkK 15100 350 = true := checkK_append 300 15100 50 h5 checkK_G15400
  have h7 : checkK 15100 400 = true := checkK_append 350 15100 50 h6 checkK_G15450
  have h8 : checkK 15100 450 = true := checkK_append 400 15100 50 h7 checkK_G15500
  have h9 : checkK 15100 500 = true := checkK_append 450 15100 50 h8 checkK_G15550
  have h10 : checkK 15100 550 = true := checkK_append 500 15100 50 h9 checkK_G15600
  have h11 : checkK 15100 600 = true := checkK_append 550 15100 50 h10 checkK_G15650
  have h12 : checkK 15100 650 = true := checkK_append 600 15100 50 h11 checkK_G15700
  have h13 : checkK 15100 700 = true := checkK_append 650 15100 50 h12 checkK_G15750
  have h14 : checkK 15100 750 = true := checkK_append 700 15100 50 h13 checkK_G15800
  have h15 : checkK 15100 800 = true := checkK_append 750 15100 50 h14 checkK_G15850
  exact h15

end ThetaSum
