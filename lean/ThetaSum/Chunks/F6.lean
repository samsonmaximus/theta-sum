import ThetaSum.Compute

/-! Kernel checks (`decide +kernel`) of `condK p` for the odd primes `p ∈ [8700, 9400)`,
in blocks of 100. -/

set_option Elab.async false

namespace ThetaSum

theorem checkK_B087 : checkK 8700 100 = true := by decide +kernel
theorem checkK_B088 : checkK 8800 100 = true := by decide +kernel
theorem checkK_B089 : checkK 8900 100 = true := by decide +kernel
theorem checkK_B090 : checkK 9000 100 = true := by decide +kernel
theorem checkK_B091 : checkK 9100 100 = true := by decide +kernel
theorem checkK_B092 : checkK 9200 100 = true := by decide +kernel
theorem checkK_B093 : checkK 9300 100 = true := by decide +kernel

theorem checkK_F6 : checkK 8700 700 = true := by
  have h87 : checkK 8700 100 = true := checkK_B087
  have h88 : checkK 8700 200 = true := checkK_append 100 8700 100 h87 checkK_B088
  have h89 : checkK 8700 300 = true := checkK_append 200 8700 100 h88 checkK_B089
  have h90 : checkK 8700 400 = true := checkK_append 300 8700 100 h89 checkK_B090
  have h91 : checkK 8700 500 = true := checkK_append 400 8700 100 h90 checkK_B091
  have h92 : checkK 8700 600 = true := checkK_append 500 8700 100 h91 checkK_B092
  have h93 : checkK 8700 700 = true := checkK_append 600 8700 100 h92 checkK_B093
  exact h93

end ThetaSum
