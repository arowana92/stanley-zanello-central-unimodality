module

public import CentralUnimodality.SpatialTrialTransfer
public import CentralUnimodality.IntegralPeakWindow
public import CentralUnimodality.FiniteBase196

/-! Three rational margins for the integrated trial imply the
unbounded peak comparison required by the induction. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

open Set Witness

theorem peak_of_trial_margins
    (left : ∀ x∈Icc (0.1359:ℝ) 0.339, 1/8 ≤ integratedTaylor 1 1024 trialPower x)
    (middle : ∀ x∈Icc (0.333:ℝ) 0.404, integratedTaylor 2 1024 trialPower x≤ -128)
    (right : ∀ x∈Icc (0.398:ℝ) 0.631, integratedTaylor 1 1024 trialPower x≤ -2)
    {n δ : ℕ} (hs : δ≤1) (hn : 10^54≤n+δ) : ThreeFifthsPeak n δ := by
  apply threeFifths_of_integral_signs (by omega) hs
  · intro x hx
    have H := abs_le.mp (full_period_error hs hn (by decide : 1≤2) (x:=x)
      (abs_le.mpr ⟨by linarith only [hx.1],by linarith only [hx.2]⟩))
    linarith only [H.1,left x hx]
  · intro x hx
    have H := abs_le.mp (full_period_error hs hn (by decide : 2≤2) (x:=x)
      (abs_le.mpr ⟨by linarith only [hx.1],by linarith only [hx.2]⟩))
    linarith only [H.2,middle x hx]
  · intro x hx
    have H := abs_le.mp (full_period_error hs hn (by decide : 1≤2) (x:=x)
      (abs_le.mpr ⟨by linarith only [hx.1],by linarith only [hx.2]⟩))
    linarith only [H.2,right x hx]

end CentralUnimodality.PolynomialTrial
