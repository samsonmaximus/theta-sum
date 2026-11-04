import ThetaSum.Compute

/-! Kernel checks (`decide +kernel`) of `condK p` for the odd primes `p ∈ [15900, 16700)`,
in blocks of 50. -/

set_option Elab.async false

namespace ThetaSum

theorem checkK_G15900 : checkK 15900 50 = true := by decide +kernel
theorem checkK_G15950 : checkK 15950 50 = true := by decide +kernel
theorem checkK_G16000 : checkK 16000 50 = true := by decide +kernel
theorem checkK_G16050 : checkK 16050 50 = true := by decide +kernel
theorem checkK_G16100 : checkK 16100 50 = true := by decide +kernel
theorem checkK_G16150 : checkK 16150 50 = true := by decide +kernel
theorem checkK_G16200 : checkK 16200 50 = true := by decide +kernel
theorem checkK_G16250 : checkK 16250 50 = true := by decide +kernel
theorem checkK_G16300 : checkK 16300 50 = true := by decide +kernel
theorem checkK_G16350 : checkK 16350 50 = true := by decide +kernel
theorem checkK_G16400 : checkK 16400 50 = true := by decide +kernel
theorem checkK_G16450 : checkK 16450 50 = true := by decide +kernel
theorem checkK_G16500 : checkK 16500 50 = true := by decide +kernel
theorem checkK_G16550 : checkK 16550 50 = true := by decide +kernel
theorem checkK_G16600 : checkK 16600 50 = true := by decide +kernel
theorem checkK_G16650 : checkK 16650 50 = true := by decide +kernel

theorem checkK_G6_all : checkK 15900 800 = true := by
  have h0 : checkK 15900 50 = true := checkK_G15900
  have h1 : checkK 15900 100 = true := checkK_append 50 15900 50 h0 checkK_G15950
  have h2 : checkK 15900 150 = true := checkK_append 100 15900 50 h1 checkK_G16000
  have h3 : checkK 15900 200 = true := checkK_append 150 15900 50 h2 checkK_G16050
  have h4 : checkK 15900 250 = true := checkK_append 200 15900 50 h3 checkK_G16100
  have h5 : checkK 15900 300 = true := checkK_append 250 15900 50 h4 checkK_G16150
  have h6 : checkK 15900 350 = true := checkK_append 300 15900 50 h5 checkK_G16200
  have h7 : checkK 15900 400 = true := checkK_append 350 15900 50 h6 checkK_G16250
  have h8 : checkK 15900 450 = true := checkK_append 400 15900 50 h7 checkK_G16300
  have h9 : checkK 15900 500 = true := checkK_append 450 15900 50 h8 checkK_G16350
  have h10 : checkK 15900 550 = true := checkK_append 500 15900 50 h9 checkK_G16400
  have h11 : checkK 15900 600 = true := checkK_append 550 15900 50 h10 checkK_G16450
  have h12 : checkK 15900 650 = true := checkK_append 600 15900 50 h11 checkK_G16500
  have h13 : checkK 15900 700 = true := checkK_append 650 15900 50 h12 checkK_G16550
  have h14 : checkK 15900 750 = true := checkK_append 700 15900 50 h13 checkK_G16600
  have h15 : checkK 15900 800 = true := checkK_append 750 15900 50 h14 checkK_G16650
  exact h15

end ThetaSum
