module

public import CentralUnimodality.SpatialMomentValues
public import CentralUnimodality.SpatialWindowArithmetic

/-! The three spatial margins for the actual compact Taylor integrals. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Set

theorem compact_window_margins :
    (∀ x∈Icc (0.1359:ℝ) 0.339, 1/5 ≤ integratedTaylor 1 1024 trialPower x) ∧
    (∀ x∈Icc (0.333:ℝ) 0.404, integratedTaylor 2 1024 trialPower x≤ -160) ∧
    (∀ x∈Icc (0.398:ℝ) 0.631, integratedTaylor 1 1024 trialPower x≤ -2) := by
  have r₁ := (spatial_row_eq (by decide : 1≤2)).symm.trans first_trial_coefficients
  have r₂ := (spatial_row_eq (by decide : 2≤2)).symm.trans second_trial_coefficients
  have d₁ := trial_row_den (by decide : 1≤2)
  have d₂ := trial_row_den (by decide : 2≤2)
  have c₁ : spatialCapacity 1 := by simpa only [spatialCapacity,r₁,d₁] using first_trial_capacity
  have c₂ : spatialCapacity 2 := by simpa only [spatialCapacity,r₂,d₂] using second_trial_capacity
  refine ⟨fun x hx => ?_,fun x hx => ?_,fun x hx => ?_⟩
  · have S := left_trial_sign
    rw [spatialSign_exact,← r₁,← d₁] at S
    have h := spatial_margin _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)
      c₁ S (x:=x) (by norm_num at hx ⊢; exact hx)
    norm_num at h; linarith only [h]
  · have S := middle_trial_sign
    rw [spatialSign_exact,← r₂,← d₂] at S
    have h := spatial_margin _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)
      c₂ S (x:=x) (by norm_num at hx ⊢; exact hx)
    norm_num at h; linarith only [h]
  · have S := right_trial_sign
    rw [spatialSign_exact,← r₁,← d₁] at S
    have h := spatial_margin _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)
      c₁ S (x:=x) (by norm_num at hx ⊢; exact hx)
    norm_num at h; linarith only [h]

end CentralUnimodality.PolynomialTrial
