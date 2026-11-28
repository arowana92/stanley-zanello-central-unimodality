module

public import CentralUnimodality.SpatialMomentProducts

/-! Exact polynomial integration rows for both spatial derivatives. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

set_option maxRecDepth 4000 in
theorem spatial_row_eq {r : ℕ} (hr : r≤2) :
    tabulatedRow r 1024 spatialMoments=integratedRow r 1024 trialPower := by
  apply tabulated_row_exact
  intro i hi
  have length : trialPower.length=421 := by rw [trialPower,unpackCheb,centeredDigits_length]; decide
  have den : momentDivisor (momentTop r 1024 trialPower)=common4000 := by
    have top : momentTop r 1024 trialPower≤4000 := by unfold momentTop; rw [length]; omega
    simp [momentDivisor,top]
  rw [den,spatial_weights_eq,spatial_moment_at (by omega)]
  rfl

end CentralUnimodality.PolynomialTrial
