import ThetaSum.Compute

/-! Kernel checks (`decide +kernel`) of `condK p` for the odd primes `p ∈ [17400, 18100)`,
in blocks of 50. -/

set_option Elab.async false

namespace ThetaSum

theorem checkK_G17400 : checkK 17400 50 = true := by decide +kernel
theorem checkK_G17450 : checkK 17450 50 = true := by decide +kernel
theorem checkK_G17500 : checkK 17500 50 = true := by decide +kernel
theorem checkK_G17550 : checkK 17550 50 = true := by decide +kernel
theorem checkK_G17600 : checkK 17600 50 = true := by decide +kernel
theorem checkK_G17650 : checkK 17650 50 = true := by decide +kernel
theorem checkK_G17700 : checkK 17700 50 = true := by decide +kernel
theorem checkK_G17750 : checkK 17750 50 = true := by decide +kernel
theorem checkK_G17800 : checkK 17800 50 = true := by decide +kernel
theorem checkK_G17850 : checkK 17850 50 = true := by decide +kernel
theorem checkK_G17900 : checkK 17900 50 = true := by decide +kernel
theorem checkK_G17950 : checkK 17950 50 = true := by decide +kernel
theorem checkK_G18000 : checkK 18000 50 = true := by decide +kernel
theorem checkK_G18050 : checkK 18050 50 = true := by decide +kernel

theorem checkK_G8_all : checkK 17400 700 = true := by
  have h0 : checkK 17400 50 = true := checkK_G17400
  have h1 : checkK 17400 100 = true := checkK_append 50 17400 50 h0 checkK_G17450
  have h2 : checkK 17400 150 = true := checkK_append 100 17400 50 h1 checkK_G17500
  have h3 : checkK 17400 200 = true := checkK_append 150 17400 50 h2 checkK_G17550
  have h4 : checkK 17400 250 = true := checkK_append 200 17400 50 h3 checkK_G17600
  have h5 : checkK 17400 300 = true := checkK_append 250 17400 50 h4 checkK_G17650
  have h6 : checkK 17400 350 = true := checkK_append 300 17400 50 h5 checkK_G17700
  have h7 : checkK 17400 400 = true := checkK_append 350 17400 50 h6 checkK_G17750
  have h8 : checkK 17400 450 = true := checkK_append 400 17400 50 h7 checkK_G17800
  have h9 : checkK 17400 500 = true := checkK_append 450 17400 50 h8 checkK_G17850
  have h10 : checkK 17400 550 = true := checkK_append 500 17400 50 h9 checkK_G17900
  have h11 : checkK 17400 600 = true := checkK_append 550 17400 50 h10 checkK_G17950
  have h12 : checkK 17400 650 = true := checkK_append 600 17400 50 h11 checkK_G18000
  have h13 : checkK 17400 700 = true := checkK_append 650 17400 50 h12 checkK_G18050
  exact h13

end ThetaSum
