import ThetaSum.Compute

/-! Kernel checks (`decide +kernel`) of `condK p` for the odd primes `p ∈ [5000, 6200)`,
in blocks of 100. -/

set_option Elab.async false

namespace ThetaSum

theorem checkK_B050 : checkK 5000 100 = true := by decide +kernel
theorem checkK_B051 : checkK 5100 100 = true := by decide +kernel
theorem checkK_B052 : checkK 5200 100 = true := by decide +kernel
theorem checkK_B053 : checkK 5300 100 = true := by decide +kernel
theorem checkK_B054 : checkK 5400 100 = true := by decide +kernel
theorem checkK_B055 : checkK 5500 100 = true := by decide +kernel
theorem checkK_B056 : checkK 5600 100 = true := by decide +kernel
theorem checkK_B057 : checkK 5700 100 = true := by decide +kernel
theorem checkK_B058 : checkK 5800 100 = true := by decide +kernel
theorem checkK_B059 : checkK 5900 100 = true := by decide +kernel
theorem checkK_B060 : checkK 6000 100 = true := by decide +kernel
theorem checkK_B061 : checkK 6100 100 = true := by decide +kernel

theorem checkK_F2 : checkK 5000 1200 = true := by
  have h50 : checkK 5000 100 = true := checkK_B050
  have h51 : checkK 5000 200 = true := checkK_append 100 5000 100 h50 checkK_B051
  have h52 : checkK 5000 300 = true := checkK_append 200 5000 100 h51 checkK_B052
  have h53 : checkK 5000 400 = true := checkK_append 300 5000 100 h52 checkK_B053
  have h54 : checkK 5000 500 = true := checkK_append 400 5000 100 h53 checkK_B054
  have h55 : checkK 5000 600 = true := checkK_append 500 5000 100 h54 checkK_B055
  have h56 : checkK 5000 700 = true := checkK_append 600 5000 100 h55 checkK_B056
  have h57 : checkK 5000 800 = true := checkK_append 700 5000 100 h56 checkK_B057
  have h58 : checkK 5000 900 = true := checkK_append 800 5000 100 h57 checkK_B058
  have h59 : checkK 5000 1000 = true := checkK_append 900 5000 100 h58 checkK_B059
  have h60 : checkK 5000 1100 = true := checkK_append 1000 5000 100 h59 checkK_B060
  have h61 : checkK 5000 1200 = true := checkK_append 1100 5000 100 h60 checkK_B061
  exact h61

end ThetaSum
