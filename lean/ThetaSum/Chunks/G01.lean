import ThetaSum.Compute

/-! Kernel checks (`decide +kernel`) of `condK p` for the odd primes `p ∈ [11300, 12350)`,
in blocks of 50. -/

set_option Elab.async false

namespace ThetaSum

theorem checkK_G11300 : checkK 11300 50 = true := by decide +kernel
theorem checkK_G11350 : checkK 11350 50 = true := by decide +kernel
theorem checkK_G11400 : checkK 11400 50 = true := by decide +kernel
theorem checkK_G11450 : checkK 11450 50 = true := by decide +kernel
theorem checkK_G11500 : checkK 11500 50 = true := by decide +kernel
theorem checkK_G11550 : checkK 11550 50 = true := by decide +kernel
theorem checkK_G11600 : checkK 11600 50 = true := by decide +kernel
theorem checkK_G11650 : checkK 11650 50 = true := by decide +kernel
theorem checkK_G11700 : checkK 11700 50 = true := by decide +kernel
theorem checkK_G11750 : checkK 11750 50 = true := by decide +kernel
theorem checkK_G11800 : checkK 11800 50 = true := by decide +kernel
theorem checkK_G11850 : checkK 11850 50 = true := by decide +kernel
theorem checkK_G11900 : checkK 11900 50 = true := by decide +kernel
theorem checkK_G11950 : checkK 11950 50 = true := by decide +kernel
theorem checkK_G12000 : checkK 12000 50 = true := by decide +kernel
theorem checkK_G12050 : checkK 12050 50 = true := by decide +kernel
theorem checkK_G12100 : checkK 12100 50 = true := by decide +kernel
theorem checkK_G12150 : checkK 12150 50 = true := by decide +kernel
theorem checkK_G12200 : checkK 12200 50 = true := by decide +kernel
theorem checkK_G12250 : checkK 12250 50 = true := by decide +kernel
theorem checkK_G12300 : checkK 12300 50 = true := by decide +kernel

theorem checkK_G1_all : checkK 11300 1050 = true := by
  have h0 : checkK 11300 50 = true := checkK_G11300
  have h1 : checkK 11300 100 = true := checkK_append 50 11300 50 h0 checkK_G11350
  have h2 : checkK 11300 150 = true := checkK_append 100 11300 50 h1 checkK_G11400
  have h3 : checkK 11300 200 = true := checkK_append 150 11300 50 h2 checkK_G11450
  have h4 : checkK 11300 250 = true := checkK_append 200 11300 50 h3 checkK_G11500
  have h5 : checkK 11300 300 = true := checkK_append 250 11300 50 h4 checkK_G11550
  have h6 : checkK 11300 350 = true := checkK_append 300 11300 50 h5 checkK_G11600
  have h7 : checkK 11300 400 = true := checkK_append 350 11300 50 h6 checkK_G11650
  have h8 : checkK 11300 450 = true := checkK_append 400 11300 50 h7 checkK_G11700
  have h9 : checkK 11300 500 = true := checkK_append 450 11300 50 h8 checkK_G11750
  have h10 : checkK 11300 550 = true := checkK_append 500 11300 50 h9 checkK_G11800
  have h11 : checkK 11300 600 = true := checkK_append 550 11300 50 h10 checkK_G11850
  have h12 : checkK 11300 650 = true := checkK_append 600 11300 50 h11 checkK_G11900
  have h13 : checkK 11300 700 = true := checkK_append 650 11300 50 h12 checkK_G11950
  have h14 : checkK 11300 750 = true := checkK_append 700 11300 50 h13 checkK_G12000
  have h15 : checkK 11300 800 = true := checkK_append 750 11300 50 h14 checkK_G12050
  have h16 : checkK 11300 850 = true := checkK_append 800 11300 50 h15 checkK_G12100
  have h17 : checkK 11300 900 = true := checkK_append 850 11300 50 h16 checkK_G12150
  have h18 : checkK 11300 950 = true := checkK_append 900 11300 50 h17 checkK_G12200
  have h19 : checkK 11300 1000 = true := checkK_append 950 11300 50 h18 checkK_G12250
  have h20 : checkK 11300 1050 = true := checkK_append 1000 11300 50 h19 checkK_G12300
  exact h20

end ThetaSum
