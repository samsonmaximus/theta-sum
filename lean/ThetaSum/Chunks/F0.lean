import ThetaSum.Compute

/-! Kernel checks (`decide +kernel`) of `condK p` for the odd primes `p ∈ [0, 3600)`,
in blocks of 100. -/

set_option Elab.async false

namespace ThetaSum

theorem checkK_B000 : checkK 0 100 = true := by decide +kernel
theorem checkK_B001 : checkK 100 100 = true := by decide +kernel
theorem checkK_B002 : checkK 200 100 = true := by decide +kernel
theorem checkK_B003 : checkK 300 100 = true := by decide +kernel
theorem checkK_B004 : checkK 400 100 = true := by decide +kernel
theorem checkK_B005 : checkK 500 100 = true := by decide +kernel
theorem checkK_B006 : checkK 600 100 = true := by decide +kernel
theorem checkK_B007 : checkK 700 100 = true := by decide +kernel
theorem checkK_B008 : checkK 800 100 = true := by decide +kernel
theorem checkK_B009 : checkK 900 100 = true := by decide +kernel
theorem checkK_B010 : checkK 1000 100 = true := by decide +kernel
theorem checkK_B011 : checkK 1100 100 = true := by decide +kernel
theorem checkK_B012 : checkK 1200 100 = true := by decide +kernel
theorem checkK_B013 : checkK 1300 100 = true := by decide +kernel
theorem checkK_B014 : checkK 1400 100 = true := by decide +kernel
theorem checkK_B015 : checkK 1500 100 = true := by decide +kernel
theorem checkK_B016 : checkK 1600 100 = true := by decide +kernel
theorem checkK_B017 : checkK 1700 100 = true := by decide +kernel
theorem checkK_B018 : checkK 1800 100 = true := by decide +kernel
theorem checkK_B019 : checkK 1900 100 = true := by decide +kernel
theorem checkK_B020 : checkK 2000 100 = true := by decide +kernel
theorem checkK_B021 : checkK 2100 100 = true := by decide +kernel
theorem checkK_B022 : checkK 2200 100 = true := by decide +kernel
theorem checkK_B023 : checkK 2300 100 = true := by decide +kernel
theorem checkK_B024 : checkK 2400 100 = true := by decide +kernel
theorem checkK_B025 : checkK 2500 100 = true := by decide +kernel
theorem checkK_B026 : checkK 2600 100 = true := by decide +kernel
theorem checkK_B027 : checkK 2700 100 = true := by decide +kernel
theorem checkK_B028 : checkK 2800 100 = true := by decide +kernel
theorem checkK_B029 : checkK 2900 100 = true := by decide +kernel
theorem checkK_B030 : checkK 3000 100 = true := by decide +kernel
theorem checkK_B031 : checkK 3100 100 = true := by decide +kernel
theorem checkK_B032 : checkK 3200 100 = true := by decide +kernel
theorem checkK_B033 : checkK 3300 100 = true := by decide +kernel
theorem checkK_B034 : checkK 3400 100 = true := by decide +kernel
theorem checkK_B035 : checkK 3500 100 = true := by decide +kernel

theorem checkK_F0 : checkK 0 3600 = true := by
  have h0 : checkK 0 100 = true := checkK_B000
  have h1 : checkK 0 200 = true := checkK_append 100 0 100 h0 checkK_B001
  have h2 : checkK 0 300 = true := checkK_append 200 0 100 h1 checkK_B002
  have h3 : checkK 0 400 = true := checkK_append 300 0 100 h2 checkK_B003
  have h4 : checkK 0 500 = true := checkK_append 400 0 100 h3 checkK_B004
  have h5 : checkK 0 600 = true := checkK_append 500 0 100 h4 checkK_B005
  have h6 : checkK 0 700 = true := checkK_append 600 0 100 h5 checkK_B006
  have h7 : checkK 0 800 = true := checkK_append 700 0 100 h6 checkK_B007
  have h8 : checkK 0 900 = true := checkK_append 800 0 100 h7 checkK_B008
  have h9 : checkK 0 1000 = true := checkK_append 900 0 100 h8 checkK_B009
  have h10 : checkK 0 1100 = true := checkK_append 1000 0 100 h9 checkK_B010
  have h11 : checkK 0 1200 = true := checkK_append 1100 0 100 h10 checkK_B011
  have h12 : checkK 0 1300 = true := checkK_append 1200 0 100 h11 checkK_B012
  have h13 : checkK 0 1400 = true := checkK_append 1300 0 100 h12 checkK_B013
  have h14 : checkK 0 1500 = true := checkK_append 1400 0 100 h13 checkK_B014
  have h15 : checkK 0 1600 = true := checkK_append 1500 0 100 h14 checkK_B015
  have h16 : checkK 0 1700 = true := checkK_append 1600 0 100 h15 checkK_B016
  have h17 : checkK 0 1800 = true := checkK_append 1700 0 100 h16 checkK_B017
  have h18 : checkK 0 1900 = true := checkK_append 1800 0 100 h17 checkK_B018
  have h19 : checkK 0 2000 = true := checkK_append 1900 0 100 h18 checkK_B019
  have h20 : checkK 0 2100 = true := checkK_append 2000 0 100 h19 checkK_B020
  have h21 : checkK 0 2200 = true := checkK_append 2100 0 100 h20 checkK_B021
  have h22 : checkK 0 2300 = true := checkK_append 2200 0 100 h21 checkK_B022
  have h23 : checkK 0 2400 = true := checkK_append 2300 0 100 h22 checkK_B023
  have h24 : checkK 0 2500 = true := checkK_append 2400 0 100 h23 checkK_B024
  have h25 : checkK 0 2600 = true := checkK_append 2500 0 100 h24 checkK_B025
  have h26 : checkK 0 2700 = true := checkK_append 2600 0 100 h25 checkK_B026
  have h27 : checkK 0 2800 = true := checkK_append 2700 0 100 h26 checkK_B027
  have h28 : checkK 0 2900 = true := checkK_append 2800 0 100 h27 checkK_B028
  have h29 : checkK 0 3000 = true := checkK_append 2900 0 100 h28 checkK_B029
  have h30 : checkK 0 3100 = true := checkK_append 3000 0 100 h29 checkK_B030
  have h31 : checkK 0 3200 = true := checkK_append 3100 0 100 h30 checkK_B031
  have h32 : checkK 0 3300 = true := checkK_append 3200 0 100 h31 checkK_B032
  have h33 : checkK 0 3400 = true := checkK_append 3300 0 100 h32 checkK_B033
  have h34 : checkK 0 3500 = true := checkK_append 3400 0 100 h33 checkK_B034
  have h35 : checkK 0 3600 = true := checkK_append 3500 0 100 h34 checkK_B035
  exact h35

end ThetaSum
