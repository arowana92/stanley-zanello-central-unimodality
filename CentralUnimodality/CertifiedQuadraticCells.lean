module

public import CentralUnimodality.QuadraticCellChecks

/-! Both dyadic prefixes satisfy the interval caps throughout the frequency
range where the quadratic correction is used. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open ReturnSplit

set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option Elab.async false

check_quadratic_cells all_quadratic_cells 0 57

theorem residual_from_checked_cells {σ i : ℕ} (hs : σ≤1) (hi : i<228)
    (eq : quadraticChebRow σ=dyadicQuadratic σ) {v : ℝ} (hv : v∈halfInterval i) :
    |secondCurveResidual (value candidate) (correctedValue σ) σ v|≤
      (cellQuadraticNum (i/4):ℝ)/10^30+303/10^9 := by
  apply (quadratic_residual_from_prefix hs hi eq hv).trans
  have h : twoUnitMax (i/4)≤cellQuadraticNum (i/4) := by
    simpa only [Nat.zero_add] using all_quadratic_cells (i/4) (by omega)
  have p : twoUnitNum (powerQuadratic σ) (i/4)≤cellQuadraticNum (i/4) := by
    by_cases e : σ=0
    · simp only [powerQuadratic,ite_eq_left e]
      exact (le_max_left ..).trans h
    · simp only [powerQuadratic,ite_eq_right e]
      exact (le_max_right ..).trans h
  exact add_le_add (div_le_div_of_nonneg_right (by exact_mod_cast p) (by positivity)) le_rfl

end CentralUnimodality.PolynomialTrial
