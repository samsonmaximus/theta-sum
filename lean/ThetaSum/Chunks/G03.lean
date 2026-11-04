import ThetaSum.Compute

/-! Kernel checks (`decide +kernel`) of `condK p` for the odd primes `p ∈ [13300, 14250)`,
in blocks of 50. -/

set_option Elab.async false

namespace ThetaSum

theorem checkK_G13300 : checkK 13300 50 = true := by decide +kernel
theorem checkK_G13350 : checkK 13350 50 = true := by decide +kernel
theorem checkK_G13400 : checkK 13400 50 = true := by decide +kernel
theorem checkK_G13450 : checkK 13450 50 = true := by decide +kernel
theorem checkK_G13500 : checkK 13500 50 = true := by decide +kernel
theorem checkK_G13550 : checkK 13550 50 = true := by decide +kernel
theorem checkK_G13600 : checkK 13600 50 = true := by decide +kernel
theorem checkK_G13650 : checkK 13650 50 = true := by decide +kernel
theorem checkK_G13700 : checkK 13700 50 = true := by decide +kernel
theorem checkK_G13750 : checkK 13750 50 = true := by decide +kernel
theorem checkK_G13800 : checkK 13800 50 = true := by decide +kernel
theorem checkK_G13850 : checkK 13850 50 = true := by decide +kernel
theorem checkK_G13900 : checkK 13900 50 = true := by decide +kernel
theorem checkK_G13950 : checkK 13950 50 = true := by decide +kernel
theorem checkK_G14000 : checkK 14000 50 = true := by decide +kernel
theorem checkK_G14050 : checkK 14050 50 = true := by decide +kernel
theorem checkK_G14100 : checkK 14100 50 = true := by decide +kernel
theorem checkK_G14150 : checkK 14150 50 = true := by decide +kernel
theorem checkK_G14200 : checkK 14200 50 = true := by decide +kernel

theorem checkK_G3_all : checkK 13300 950 = true := by
  have h0 : checkK 13300 50 = true := checkK_G13300
  have h1 : checkK 13300 100 = true := checkK_append 50 13300 50 h0 checkK_G13350
  have h2 : checkK 13300 150 = true := checkK_append 100 13300 50 h1 checkK_G13400
  have h3 : checkK 13300 200 = true := checkK_append 150 13300 50 h2 checkK_G13450
  have h4 : checkK 13300 250 = true := checkK_append 200 13300 50 h3 checkK_G13500
  have h5 : checkK 13300 300 = true := checkK_append 250 13300 50 h4 checkK_G13550
  have h6 : checkK 13300 350 = true := checkK_append 300 13300 50 h5 checkK_G13600
  have h7 : checkK 13300 400 = true := checkK_append 350 13300 50 h6 checkK_G13650
  have h8 : checkK 13300 450 = true := checkK_append 400 13300 50 h7 checkK_G13700
  have h9 : checkK 13300 500 = true := checkK_append 450 13300 50 h8 checkK_G13750
  have h10 : checkK 13300 550 = true := checkK_append 500 13300 50 h9 checkK_G13800
  have h11 : checkK 13300 600 = true := checkK_append 550 13300 50 h10 checkK_G13850
  have h12 : checkK 13300 650 = true := checkK_append 600 13300 50 h11 checkK_G13900
  have h13 : checkK 13300 700 = true := checkK_append 650 13300 50 h12 checkK_G13950
  have h14 : checkK 13300 750 = true := checkK_append 700 13300 50 h13 checkK_G14000
  have h15 : checkK 13300 800 = true := checkK_append 750 13300 50 h14 checkK_G14050
  have h16 : checkK 13300 850 = true := checkK_append 800 13300 50 h15 checkK_G14100
  have h17 : checkK 13300 900 = true := checkK_append 850 13300 50 h16 checkK_G14150
  have h18 : checkK 13300 950 = true := checkK_append 900 13300 50 h17 checkK_G14200
  exact h18

end ThetaSum
