import ThetaSum.Compute

/-! Kernel checks (`decide +kernel`) of `condK p` for the odd primes `p ∈ [9400, 10100)`,
in blocks of 100. -/

set_option Elab.async false

namespace ThetaSum

theorem checkK_B094 : checkK 9400 100 = true := by decide +kernel
theorem checkK_B095 : checkK 9500 100 = true := by decide +kernel
theorem checkK_B096 : checkK 9600 100 = true := by decide +kernel
theorem checkK_B097 : checkK 9700 100 = true := by decide +kernel
theorem checkK_B098 : checkK 9800 100 = true := by decide +kernel
theorem checkK_B099 : checkK 9900 100 = true := by decide +kernel
theorem checkK_B100 : checkK 10000 100 = true := by decide +kernel

theorem checkK_F7 : checkK 9400 700 = true := by
  have h94 : checkK 9400 100 = true := checkK_B094
  have h95 : checkK 9400 200 = true := checkK_append 100 9400 100 h94 checkK_B095
  have h96 : checkK 9400 300 = true := checkK_append 200 9400 100 h95 checkK_B096
  have h97 : checkK 9400 400 = true := checkK_append 300 9400 100 h96 checkK_B097
  have h98 : checkK 9400 500 = true := checkK_append 400 9400 100 h97 checkK_B098
  have h99 : checkK 9400 600 = true := checkK_append 500 9400 100 h98 checkK_B099
  have h100 : checkK 9400 700 = true := checkK_append 600 9400 100 h99 checkK_B100
  exact h100

end ThetaSum
