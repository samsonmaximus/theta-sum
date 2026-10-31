import ThetaSum.Compute

/-! Kernel checks (`decide +kernel`) of `condK p` for the odd primes `p ∈ [7100, 8000)`,
in blocks of 100. -/

set_option Elab.async false

namespace ThetaSum

theorem checkK_B071 : checkK 7100 100 = true := by decide +kernel
theorem checkK_B072 : checkK 7200 100 = true := by decide +kernel
theorem checkK_B073 : checkK 7300 100 = true := by decide +kernel
theorem checkK_B074 : checkK 7400 100 = true := by decide +kernel
theorem checkK_B075 : checkK 7500 100 = true := by decide +kernel
theorem checkK_B076 : checkK 7600 100 = true := by decide +kernel
theorem checkK_B077 : checkK 7700 100 = true := by decide +kernel
theorem checkK_B078 : checkK 7800 100 = true := by decide +kernel
theorem checkK_B079 : checkK 7900 100 = true := by decide +kernel

theorem checkK_F4 : checkK 7100 900 = true := by
  have h71 : checkK 7100 100 = true := checkK_B071
  have h72 : checkK 7100 200 = true := checkK_append 100 7100 100 h71 checkK_B072
  have h73 : checkK 7100 300 = true := checkK_append 200 7100 100 h72 checkK_B073
  have h74 : checkK 7100 400 = true := checkK_append 300 7100 100 h73 checkK_B074
  have h75 : checkK 7100 500 = true := checkK_append 400 7100 100 h74 checkK_B075
  have h76 : checkK 7100 600 = true := checkK_append 500 7100 100 h75 checkK_B076
  have h77 : checkK 7100 700 = true := checkK_append 600 7100 100 h76 checkK_B077
  have h78 : checkK 7100 800 = true := checkK_append 700 7100 100 h77 checkK_B078
  have h79 : checkK 7100 900 = true := checkK_append 800 7100 100 h78 checkK_B079
  exact h79

end ThetaSum
