module

public import CentralUnimodality.FirstReturnArea
public import CentralUnimodality.FourierInputs
public import CentralUnimodality.SurvivalBounds
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic.FieldSimp

/-! Inverting the last-return convolution can exploit cancellation against
its zero-frequency value. The exact first area moment gives a uniform
Lipschitz bound for every positive return time. -/
@[expose] public section

namespace CentralUnimodality
open PowerSeries

noncomputable def returnMass (j : ℕ) : ℝ := (firstReturns (2*j)).card / (2:ℝ)^(2*j)

@[simp] theorem returnMass_zero : returnMass 0=0 := by
  have emp : firstReturns 0=∅ := by decide +kernel
  simp [returnMass,emp]

theorem returnMass_succ (j : ℕ) : returnMass (j+1)=survival j-survival (j+1) := by
  rw [returnMass,firstReturn_probability,survival_succ]
  field_simp
  ring

theorem returnMass_sum (N : ℕ) :
    (∑ j ∈ Finset.range (N+1), returnMass j) = 1-survival N := by
  induction N with
  | zero => simp [survival]
  | succ N ih => rw [Finset.sum_range_succ,ih,returnMass_succ]; ring

theorem returnMass_time_sum (N : ℕ) :
    (∑ j ∈ Finset.range (N+1), (j:ℝ)*returnMass j) = N*survival N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,returnMass_succ,survival_succ]
    push_cast
    field_simp
    ring

theorem areaCharacter_dist_one (ω : ℝ) (a : ℤ) :
    ‖areaCharacter ω a-1‖ ≤ |ω| * |(a:ℝ)| := by
  have H := (lipschitzWith_circleMap 0 1).dist_le_mul (ω*(a:ℝ)) 0
  simpa [circleMap,areaCharacter,dist_eq_norm,Real.norm_eq_abs,abs_mul] using H

theorem returnCharacter_dist (ω : ℝ) (d : ℕ) :
    ‖coeff (2*(d+1)) (fairSeries (areaCharacter ω) firstReturns) - (returnMass (d+1):ℂ)‖ ≤ |ω|/2 := by
  let t := 2*(d+1)
  let S := firstReturns t
  have val : (returnMass (d+1):ℂ)=((2:ℂ)⁻¹)^t*∑ _w ∈ S, (1:ℂ) := by
    simp [returnMass,S,t,div_eq_inv_mul]
  rw [val,coeff_walkSeries]
  change ‖(2:ℂ)⁻¹^t*(∑ w ∈ S, areaCharacter ω (walkArea w))-
      (2:ℂ)⁻¹^t*(∑ _w ∈ S, (1:ℂ))‖≤_
  rw [← mul_sub,← Finset.sum_sub_distrib,norm_mul]
  have sumBound := (norm_sum_le S (fun w => areaCharacter ω (walkArea w)-1)).trans
    (Finset.sum_le_sum (fun w _ => areaCharacter_dist_one ω (walkArea w)))
  rw [← Finset.mul_sum] at sumBound
  have area : (∑ w ∈ S, |(walkArea w:ℝ)|) / 2^t=1/2 :=
    MarkedExcursion.firstReturn_absolute_area d
  have scale : ‖(2:ℂ)⁻¹^t‖=(2^t:ℝ)⁻¹ := by simp
  rw [scale]
  apply (mul_le_mul_of_nonneg_left sumBound (by positivity)).trans_eq
  rw [mul_left_comm,← div_eq_inv_mul,area]
  ring

end CentralUnimodality
