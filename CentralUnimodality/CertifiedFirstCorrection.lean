module

public import CentralUnimodality.FirstPackedCertificate
public import CentralUnimodality.FirstResidualBound

/-! First residual of the actual corrected lattices on the full retained
interval, with both parity-dependent Chebyshev products certified. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Set ReturnSplit

theorem first_polynomial_bound {σ : ℕ} (hs : σ≤1) {v : ℝ} (hv : v∈Icc (0:ℝ) 144) :
    |(firstPoly σ).eval v|≤2852/10^15 := by
  obtain ⟨pos,mass,small,input⟩ := first_residual_inputs hs
  exact first_bound_of_packing σ (first_packing_verified hs) pos mass small input hv

theorem certified_first_correction {σ : ℕ} (hs : σ≤1) {v : ℝ} (hv : v∈Icc (0:ℝ) 144) :
    |firstCurveResidual (value candidate) (correctedValue σ) σ v|≤3/10^12 := by
  have tr := first_residual_transfer hs hv
  have poly := first_polynomial_bound hs hv
  have h := abs_add_le (firstCurveResidual (value candidate) (correctedValue σ) σ v-(firstPoly σ).eval v)
    ((firstPoly σ).eval v)
  rw [sub_add_cancel] at h
  linarith only [tr,poly,h]

end CentralUnimodality.PolynomialTrial
