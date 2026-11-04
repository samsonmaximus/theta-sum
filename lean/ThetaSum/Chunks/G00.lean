import ThetaSum.Compute

/-! Kernel checks (`decide +kernel`) of `condK p` for the odd primes `p ∈ [10100, 11300)`,
in blocks of 50. -/

set_option Elab.async false

namespace ThetaSum

theorem checkK_G10100 : checkK 10100 50 = true := by decide +kernel
theorem checkK_G10150 : checkK 10150 50 = true := by decide +kernel
theorem checkK_G10200 : checkK 10200 50 = true := by decide +kernel
theorem checkK_G10250 : checkK 10250 50 = true := by decide +kernel
theorem checkK_G10300 : checkK 10300 50 = true := by decide +kernel
theorem checkK_G10350 : checkK 10350 50 = true := by decide +kernel
theorem checkK_G10400 : checkK 10400 50 = true := by decide +kernel
theorem checkK_G10450 : checkK 10450 50 = true := by decide +kernel
theorem checkK_G10500 : checkK 10500 50 = true := by decide +kernel
theorem checkK_G10550 : checkK 10550 50 = true := by decide +kernel
theorem checkK_G10600 : checkK 10600 50 = true := by decide +kernel
theorem checkK_G10650 : checkK 10650 50 = true := by decide +kernel
theorem checkK_G10700 : checkK 10700 50 = true := by decide +kernel
theorem checkK_G10750 : checkK 10750 50 = true := by decide +kernel
theorem checkK_G10800 : checkK 10800 50 = true := by decide +kernel
theorem checkK_G10850 : checkK 10850 50 = true := by decide +kernel
theorem checkK_G10900 : checkK 10900 50 = true := by decide +kernel
theorem checkK_G10950 : checkK 10950 50 = true := by decide +kernel
theorem checkK_G11000 : checkK 11000 50 = true := by decide +kernel
theorem checkK_G11050 : checkK 11050 50 = true := by decide +kernel
theorem checkK_G11100 : checkK 11100 50 = true := by decide +kernel
theorem checkK_G11150 : checkK 11150 50 = true := by decide +kernel
theorem checkK_G11200 : checkK 11200 50 = true := by decide +kernel
theorem checkK_G11250 : checkK 11250 50 = true := by decide +kernel

theorem checkK_G0_all : checkK 10100 1200 = true := by
  have h0 : checkK 10100 50 = true := checkK_G10100
  have h1 : checkK 10100 100 = true := checkK_append 50 10100 50 h0 checkK_G10150
  have h2 : checkK 10100 150 = true := checkK_append 100 10100 50 h1 checkK_G10200
  have h3 : checkK 10100 200 = true := checkK_append 150 10100 50 h2 checkK_G10250
  have h4 : checkK 10100 250 = true := checkK_append 200 10100 50 h3 checkK_G10300
  have h5 : checkK 10100 300 = true := checkK_append 250 10100 50 h4 checkK_G10350
  have h6 : checkK 10100 350 = true := checkK_append 300 10100 50 h5 checkK_G10400
  have h7 : checkK 10100 400 = true := checkK_append 350 10100 50 h6 checkK_G10450
  have h8 : checkK 10100 450 = true := checkK_append 400 10100 50 h7 checkK_G10500
  have h9 : checkK 10100 500 = true := checkK_append 450 10100 50 h8 checkK_G10550
  have h10 : checkK 10100 550 = true := checkK_append 500 10100 50 h9 checkK_G10600
  have h11 : checkK 10100 600 = true := checkK_append 550 10100 50 h10 checkK_G10650
  have h12 : checkK 10100 650 = true := checkK_append 600 10100 50 h11 checkK_G10700
  have h13 : checkK 10100 700 = true := checkK_append 650 10100 50 h12 checkK_G10750
  have h14 : checkK 10100 750 = true := checkK_append 700 10100 50 h13 checkK_G10800
  have h15 : checkK 10100 800 = true := checkK_append 750 10100 50 h14 checkK_G10850
  have h16 : checkK 10100 850 = true := checkK_append 800 10100 50 h15 checkK_G10900
  have h17 : checkK 10100 900 = true := checkK_append 850 10100 50 h16 checkK_G10950
  have h18 : checkK 10100 950 = true := checkK_append 900 10100 50 h17 checkK_G11000
  have h19 : checkK 10100 1000 = true := checkK_append 950 10100 50 h18 checkK_G11050
  have h20 : checkK 10100 1050 = true := checkK_append 1000 10100 50 h19 checkK_G11100
  have h21 : checkK 10100 1100 = true := checkK_append 1050 10100 50 h20 checkK_G11150
  have h22 : checkK 10100 1150 = true := checkK_append 1100 10100 50 h21 checkK_G11200
  have h23 : checkK 10100 1200 = true := checkK_append 1150 10100 50 h22 checkK_G11250
  exact h23

end ThetaSum
