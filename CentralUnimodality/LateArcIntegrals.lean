module

public import CentralUnimodality.TiltedOuterFrequencies
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact integrals for the weighted two-thirds-power envelope and the
four finite outer frequency intervals. Each order uses its own arc volume. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real MeasureTheory Set

noncomputable def lateInnerKernel (b : ℝ) (r : ℕ) (θ : ℝ) :=
  |θ|^r * exp (-b*|θ|^(2/3:ℝ))

noncomputable def lateOuterKernel (s : Fin 4) (r : ℕ) (θ : ℝ) :=
  (Icc (outerLo s) (outerHi s)).indicator (fun x : ℝ => x^r) |θ|

theorem late_inner_integral {b : ℝ} (hb : 0<b) (r : ℕ) :
    Integrable (lateInnerKernel b r) ∧
    (∫ θ, lateInnerKernel b r θ) = 3*b^(-3*((r:ℝ)+1)/2)*Gamma (3*((r:ℝ)+1)/2) := by
  have he : (∫ θ, lateInnerKernel b r θ) = 3*b^(-3*((r:ℝ)+1)/2)*Gamma (3*((r:ℝ)+1)/2) := by
    rw [show lateInnerKernel b r = fun θ : ℝ => (fun x : ℝ => x^r*exp (-b*x^(2/3:ℝ))) |θ| from rfl,
      integral_comp_abs]
    have H := integral_rpow_mul_exp_neg_mul_rpow (p:=2/3) (q:=(r:ℝ)) (by norm_num)
      (by have := Nat.cast_nonneg (α:=ℝ) r; linarith) hb
    simp only [rpow_natCast,show -((r:ℝ)+1)/(2/3) = -3*(r+1)/2 by ring,
      show ((r:ℝ)+1)/(2/3) = 3*(r+1)/2 by ring] at H
    rw [H]; ring
  refine ⟨Integrable.of_integral_ne_zero (he.trans_ne (ne_of_gt ?_)),he⟩
  have hg := Gamma_pos_of_pos (show 0<3*((r:ℝ)+1)/2 by positivity)
  positivity

theorem late_outer_integral (s : Fin 4) (r : ℕ) :
    Integrable (lateOuterKernel s r) ∧
    (∫ θ, lateOuterKernel s r θ) =
      2*((outerHi s)^(r+1)-(outerLo s)^(r+1))/((r:ℝ)+1) := by
  have ha : 0 < outerLo s := by fin_cases s <;> norm_num [outerLo]
  have hab : outerLo s < outerHi s := by fin_cases s <;> norm_num [outerLo,outerHi]; linarith only [pi_gt_three]
  have he : (∫ θ, lateOuterKernel s r θ) =
      2*((outerHi s)^(r+1)-(outerLo s)^(r+1))/((r:ℝ)+1) := by
    rw [show lateOuterKernel s r = fun θ : ℝ => ((Icc (outerLo s) (outerHi s)).indicator (fun x : ℝ => x^r)) |θ| from rfl,
      integral_comp_abs,setIntegral_indicator measurableSet_Icc,
      inter_eq_right.mpr (show Icc (outerLo s) (outerHi s) ⊆ Ioi 0 from fun _ h => ha.trans_le h.1),
      integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab.le,integral_pow]
    ring
  refine ⟨Integrable.of_integral_ne_zero (he.trans_ne (ne_of_gt ?_)),he⟩
  have hp := pow_lt_pow_left₀ hab ha.le (Nat.succ_ne_zero r)
  positivity

end CentralUnimodality.MarkedExcursion
