import ThetaSum.Compute

/-! Kernel checks (`decide +kernel`) of `condK p` for the odd primes `p ∈ [12350, 13300)`,
in blocks of 50. -/

set_option Elab.async false

namespace ThetaSum

theorem checkK_G12350 : checkK 12350 50 = true := by decide +kernel
theorem checkK_G12400 : checkK 12400 50 = true := by decide +kernel
theorem checkK_G12450 : checkK 12450 50 = true := by decide +kernel
theorem checkK_G12500 : checkK 12500 50 = true := by decide +kernel
theorem checkK_G12550 : checkK 12550 50 = true := by decide +kernel
theorem checkK_G12600 : checkK 12600 50 = true := by decide +kernel
theorem checkK_G12650 : checkK 12650 50 = true := by decide +kernel
theorem checkK_G12700 : checkK 12700 50 = true := by decide +kernel
theorem checkK_G12750 : checkK 12750 50 = true := by decide +kernel
theorem checkK_G12800 : checkK 12800 50 = true := by decide +kernel
theorem checkK_G12850 : checkK 12850 50 = true := by decide +kernel
theorem checkK_G12900 : checkK 12900 50 = true := by decide +kernel
theorem checkK_G12950 : checkK 12950 50 = true := by decide +kernel
theorem checkK_G13000 : checkK 13000 50 = true := by decide +kernel
theorem checkK_G13050 : checkK 13050 50 = true := by decide +kernel
theorem checkK_G13100 : checkK 13100 50 = true := by decide +kernel
theorem checkK_G13150 : checkK 13150 50 = true := by decide +kernel
theorem checkK_G13200 : checkK 13200 50 = true := by decide +kernel
theorem checkK_G13250 : checkK 13250 50 = true := by decide +kernel

theorem checkK_G2_all : checkK 12350 950 = true := by
  have h0 : checkK 12350 50 = true := checkK_G12350
  have h1 : checkK 12350 100 = true := checkK_append 50 12350 50 h0 checkK_G12400
  have h2 : checkK 12350 150 = true := checkK_append 100 12350 50 h1 checkK_G12450
  have h3 : checkK 12350 200 = true := checkK_append 150 12350 50 h2 checkK_G12500
  have h4 : checkK 12350 250 = true := checkK_append 200 12350 50 h3 checkK_G12550
  have h5 : checkK 12350 300 = true := checkK_append 250 12350 50 h4 checkK_G12600
  have h6 : checkK 12350 350 = true := checkK_append 300 12350 50 h5 checkK_G12650
  have h7 : checkK 12350 400 = true := checkK_append 350 12350 50 h6 checkK_G12700
  have h8 : checkK 12350 450 = true := checkK_append 400 12350 50 h7 checkK_G12750
  have h9 : checkK 12350 500 = true := checkK_append 450 12350 50 h8 checkK_G12800
  have h10 : checkK 12350 550 = true := checkK_append 500 12350 50 h9 checkK_G12850
  have h11 : checkK 12350 600 = true := checkK_append 550 12350 50 h10 checkK_G12900
  have h12 : checkK 12350 650 = true := checkK_append 600 12350 50 h11 checkK_G12950
  have h13 : checkK 12350 700 = true := checkK_append 650 12350 50 h12 checkK_G13000
  have h14 : checkK 12350 750 = true := checkK_append 700 12350 50 h13 checkK_G13050
  have h15 : checkK 12350 800 = true := checkK_append 750 12350 50 h14 checkK_G13100
  have h16 : checkK 12350 850 = true := checkK_append 800 12350 50 h15 checkK_G13150
  have h17 : checkK 12350 900 = true := checkK_append 850 12350 50 h16 checkK_G13200
  have h18 : checkK 12350 950 = true := checkK_append 900 12350 50 h17 checkK_G13250
  exact h18

end ThetaSum
