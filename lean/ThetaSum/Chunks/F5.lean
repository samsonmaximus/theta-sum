import ThetaSum.Compute

/-! Kernel checks (`decide +kernel`) of `condK p` for the odd primes `p ∈ [8000, 8700)`,
in blocks of 100. -/

set_option Elab.async false

namespace ThetaSum

theorem checkK_B080 : checkK 8000 100 = true := by decide +kernel
theorem checkK_B081 : checkK 8100 100 = true := by decide +kernel
theorem checkK_B082 : checkK 8200 100 = true := by decide +kernel
theorem checkK_B083 : checkK 8300 100 = true := by decide +kernel
theorem checkK_B084 : checkK 8400 100 = true := by decide +kernel
theorem checkK_B085 : checkK 8500 100 = true := by decide +kernel
theorem checkK_B086 : checkK 8600 100 = true := by decide +kernel

theorem checkK_F5 : checkK 8000 700 = true := by
  have h80 : checkK 8000 100 = true := checkK_B080
  have h81 : checkK 8000 200 = true := checkK_append 100 8000 100 h80 checkK_B081
  have h82 : checkK 8000 300 = true := checkK_append 200 8000 100 h81 checkK_B082
  have h83 : checkK 8000 400 = true := checkK_append 300 8000 100 h82 checkK_B083
  have h84 : checkK 8000 500 = true := checkK_append 400 8000 100 h83 checkK_B084
  have h85 : checkK 8000 600 = true := checkK_append 500 8000 100 h84 checkK_B085
  have h86 : checkK 8000 700 = true := checkK_append 600 8000 100 h85 checkK_B086
  exact h86

end ThetaSum
