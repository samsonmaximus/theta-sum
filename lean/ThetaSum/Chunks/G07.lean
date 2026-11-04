import ThetaSum.Compute

/-! Kernel checks (`decide +kernel`) of `condK p` for the odd primes `p ∈ [16700, 17400)`,
in blocks of 50. -/

set_option Elab.async false

namespace ThetaSum

theorem checkK_G16700 : checkK 16700 50 = true := by decide +kernel
theorem checkK_G16750 : checkK 16750 50 = true := by decide +kernel
theorem checkK_G16800 : checkK 16800 50 = true := by decide +kernel
theorem checkK_G16850 : checkK 16850 50 = true := by decide +kernel
theorem checkK_G16900 : checkK 16900 50 = true := by decide +kernel
theorem checkK_G16950 : checkK 16950 50 = true := by decide +kernel
theorem checkK_G17000 : checkK 17000 50 = true := by decide +kernel
theorem checkK_G17050 : checkK 17050 50 = true := by decide +kernel
theorem checkK_G17100 : checkK 17100 50 = true := by decide +kernel
theorem checkK_G17150 : checkK 17150 50 = true := by decide +kernel
theorem checkK_G17200 : checkK 17200 50 = true := by decide +kernel
theorem checkK_G17250 : checkK 17250 50 = true := by decide +kernel
theorem checkK_G17300 : checkK 17300 50 = true := by decide +kernel
theorem checkK_G17350 : checkK 17350 50 = true := by decide +kernel

theorem checkK_G7_all : checkK 16700 700 = true := by
  have h0 : checkK 16700 50 = true := checkK_G16700
  have h1 : checkK 16700 100 = true := checkK_append 50 16700 50 h0 checkK_G16750
  have h2 : checkK 16700 150 = true := checkK_append 100 16700 50 h1 checkK_G16800
  have h3 : checkK 16700 200 = true := checkK_append 150 16700 50 h2 checkK_G16850
  have h4 : checkK 16700 250 = true := checkK_append 200 16700 50 h3 checkK_G16900
  have h5 : checkK 16700 300 = true := checkK_append 250 16700 50 h4 checkK_G16950
  have h6 : checkK 16700 350 = true := checkK_append 300 16700 50 h5 checkK_G17000
  have h7 : checkK 16700 400 = true := checkK_append 350 16700 50 h6 checkK_G17050
  have h8 : checkK 16700 450 = true := checkK_append 400 16700 50 h7 checkK_G17100
  have h9 : checkK 16700 500 = true := checkK_append 450 16700 50 h8 checkK_G17150
  have h10 : checkK 16700 550 = true := checkK_append 500 16700 50 h9 checkK_G17200
  have h11 : checkK 16700 600 = true := checkK_append 550 16700 50 h10 checkK_G17250
  have h12 : checkK 16700 650 = true := checkK_append 600 16700 50 h11 checkK_G17300
  have h13 : checkK 16700 700 = true := checkK_append 650 16700 50 h12 checkK_G17350
  exact h13

end ThetaSum
