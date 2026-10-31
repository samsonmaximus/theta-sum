import ThetaSum.Compute

/-! Kernel checks (`decide +kernel`) of `condK p` for the odd primes `p ∈ [3600, 5000)`,
in blocks of 100. -/

set_option Elab.async false

namespace ThetaSum

theorem checkK_B036 : checkK 3600 100 = true := by decide +kernel
theorem checkK_B037 : checkK 3700 100 = true := by decide +kernel
theorem checkK_B038 : checkK 3800 100 = true := by decide +kernel
theorem checkK_B039 : checkK 3900 100 = true := by decide +kernel
theorem checkK_B040 : checkK 4000 100 = true := by decide +kernel
theorem checkK_B041 : checkK 4100 100 = true := by decide +kernel
theorem checkK_B042 : checkK 4200 100 = true := by decide +kernel
theorem checkK_B043 : checkK 4300 100 = true := by decide +kernel
theorem checkK_B044 : checkK 4400 100 = true := by decide +kernel
theorem checkK_B045 : checkK 4500 100 = true := by decide +kernel
theorem checkK_B046 : checkK 4600 100 = true := by decide +kernel
theorem checkK_B047 : checkK 4700 100 = true := by decide +kernel
theorem checkK_B048 : checkK 4800 100 = true := by decide +kernel
theorem checkK_B049 : checkK 4900 100 = true := by decide +kernel

theorem checkK_F1 : checkK 3600 1400 = true := by
  have h36 : checkK 3600 100 = true := checkK_B036
  have h37 : checkK 3600 200 = true := checkK_append 100 3600 100 h36 checkK_B037
  have h38 : checkK 3600 300 = true := checkK_append 200 3600 100 h37 checkK_B038
  have h39 : checkK 3600 400 = true := checkK_append 300 3600 100 h38 checkK_B039
  have h40 : checkK 3600 500 = true := checkK_append 400 3600 100 h39 checkK_B040
  have h41 : checkK 3600 600 = true := checkK_append 500 3600 100 h40 checkK_B041
  have h42 : checkK 3600 700 = true := checkK_append 600 3600 100 h41 checkK_B042
  have h43 : checkK 3600 800 = true := checkK_append 700 3600 100 h42 checkK_B043
  have h44 : checkK 3600 900 = true := checkK_append 800 3600 100 h43 checkK_B044
  have h45 : checkK 3600 1000 = true := checkK_append 900 3600 100 h44 checkK_B045
  have h46 : checkK 3600 1100 = true := checkK_append 1000 3600 100 h45 checkK_B046
  have h47 : checkK 3600 1200 = true := checkK_append 1100 3600 100 h46 checkK_B047
  have h48 : checkK 3600 1300 = true := checkK_append 1200 3600 100 h47 checkK_B048
  have h49 : checkK 3600 1400 = true := checkK_append 1300 3600 100 h48 checkK_B049
  exact h49

end ThetaSum
