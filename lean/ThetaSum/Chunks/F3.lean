import ThetaSum.Compute

/-! Kernel checks (`decide +kernel`) of `condK p` for the odd primes `p ∈ [6200, 7100)`,
in blocks of 100. -/

set_option Elab.async false

namespace ThetaSum

theorem checkK_B062 : checkK 6200 100 = true := by decide +kernel
theorem checkK_B063 : checkK 6300 100 = true := by decide +kernel
theorem checkK_B064 : checkK 6400 100 = true := by decide +kernel
theorem checkK_B065 : checkK 6500 100 = true := by decide +kernel
theorem checkK_B066 : checkK 6600 100 = true := by decide +kernel
theorem checkK_B067 : checkK 6700 100 = true := by decide +kernel
theorem checkK_B068 : checkK 6800 100 = true := by decide +kernel
theorem checkK_B069 : checkK 6900 100 = true := by decide +kernel
theorem checkK_B070 : checkK 7000 100 = true := by decide +kernel

theorem checkK_F3 : checkK 6200 900 = true := by
  have h62 : checkK 6200 100 = true := checkK_B062
  have h63 : checkK 6200 200 = true := checkK_append 100 6200 100 h62 checkK_B063
  have h64 : checkK 6200 300 = true := checkK_append 200 6200 100 h63 checkK_B064
  have h65 : checkK 6200 400 = true := checkK_append 300 6200 100 h64 checkK_B065
  have h66 : checkK 6200 500 = true := checkK_append 400 6200 100 h65 checkK_B066
  have h67 : checkK 6200 600 = true := checkK_append 500 6200 100 h66 checkK_B067
  have h68 : checkK 6200 700 = true := checkK_append 600 6200 100 h67 checkK_B068
  have h69 : checkK 6200 800 = true := checkK_append 700 6200 100 h68 checkK_B069
  have h70 : checkK 6200 900 = true := checkK_append 800 6200 100 h69 checkK_B070
  exact h70

end ThetaSum
