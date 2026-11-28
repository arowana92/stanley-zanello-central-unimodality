module

public import CentralUnimodality.StoppedPrefixVariance
import CentralUnimodality.CenteredCosh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! The conditional prefix bound (2) in the staircase rank tilt. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

private theorem drift_ratio (u : ℝ) : (1+tanh u)*exp (-2*u)=1-tanh u := by
  have hu : 1+tanh u = 2*upChance u := by linarith only [up_total u,up_drift u]
  have hd : 1-tanh u = 2*upChance (-u) := by linarith only [up_total u,up_drift u]
  rw [hu,hd,up_ratio]; ring

/-- If all the prefix parameters are between (1-f)u and u, the smallest
drift is at least (1-f) times the initial drift. -/
theorem drift_cost {u f : ℝ} (hu : 0 < u) (hf : 0 ≤ f) (hf' : f < 1) :
    2*(1-f)*tanh u ≤ (1+tanh u)*(1-exp (-2*((1-f)*u))) ∧
    exp (-2*((1-f)*u))-exp (-2*u) ≤ 2*f*tanh u := by
  let v := (1-f)*u
  have hv : 0 < v := mul_pos (by linarith) hu
  have hvu : v ≤ u := by dsimp [v]; nlinarith only [mul_nonneg hf hu.le]
  have hvd : 0 < tanh v := by rw [tanh_eq_sinh_div_cosh]; exact div_pos (sinh_pos_iff.mpr hv) (cosh_pos _)
  have hd : 0 < tanh u := by rw [tanh_eq_sinh_div_cosh]; exact div_pos (sinh_pos_iff.mpr hu) (cosh_pos _)
  have hch : (1-f)*tanh u ≤ tanh v := tanh_chord hu.le (by linarith) (by linarith)
  have rv : exp (-2*v) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have ru : exp (-2*u) ≤ exp (-2*v) := exp_le_exp.mpr (by linarith)
  have hmon : tanh v ≤ tanh u := by
    have H := drift_ratio u
    have H' := drift_ratio v
    have ha := mul_le_mul_of_nonneg_left ru (show 0 ≤ 1+tanh v by linarith)
    by_contra! hlt
    nlinarith only [ha,H,H',mul_pos (sub_pos.mpr hlt) (exp_pos (-2*u)),hlt]
  change _ ≤ (1+tanh u)*(1-exp (-2*v)) ∧ exp (-2*v)-exp (-2*u) ≤ _
  constructor
  · nlinarith only [hch,drift_ratio v,mul_nonneg (sub_nonneg.mpr hmon) (sub_nonneg.mpr rv)]
  · have he : (1+tanh v)*(exp (-2*v)-exp (-2*u)) =
        (tanh u-tanh v)*(1+exp (-2*u)) := by nlinarith only [drift_ratio v,drift_ratio u]
    have hb := mul_le_mul (show tanh u-tanh v ≤ f*tanh u by linarith only [hch])
      (show 1+exp (-2*u) ≤ 2 by linarith only [ru,rv])
      (by positivity : 0 ≤ 1+exp (-2*u)) (mul_nonneg hf hd.le)
    nlinarith only [he,hb,mul_nonneg hvd.le (sub_nonneg.mpr ru)]

/-- Equation (2), with the scaling written as m³/σ². The numerator is the
second moment around the unrestricted mean on surviving prefixes, and the
denominator includes their actual probability. -/
theorem conditional_prefix_variance {m L : ℕ} (hm : 0 < m) {c f σ : ℝ} (hc : 0 < c)
    (hf : 0 ≤ f) (hf' : f < 1) (hL : (L:ℝ) ≤ f*m) (hσ : 0 < σ) :
    let u := c*m
    let d := tanh u
    (∑ w ∈ ballots L, signMass c u w*(centeredRank c u m w)^2)/(live c u L 1*σ^2) ≤
      ((m:ℝ)^3/(4*σ^2))*(f+(1+d)/(1-f)*(f^2+1/(2*m*d^2))) := by
  dsimp only
  let u := c*m
  let d := tanh u
  let v := (1-f)*u
  let P := live c u L 1
  let E := ∑ w ∈ ballots L, signMass c u w*(centeredRank c u m w)^2
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hu : 0 < u := mul_pos hc hm'
  have hd : 0 < d := by dsimp [d]; rw [tanh_eq_sinh_div_cosh]; exact div_pos (sinh_pos_iff.mpr hu) (cosh_pos _)
  have ht : L ≤ m := by
    have : (L:ℝ) ≤ m := by nlinarith only [hL,mul_nonneg (sub_nonneg.mpr hf'.le) hm'.le]
    exact_mod_cast this
  have hv (i : ℕ) (hi : i < L) : v ≤ u-c*i := by
    have hil : (i:ℝ) ≤ L := by exact_mod_cast hi.le
    dsimp only [u,v]; nlinarith only [mul_le_mul_of_nonneg_left (hil.trans hL) hc.le]
  obtain ⟨hprob,hdiff⟩ := drift_cost hu hf hf'
  have hlower := live_lower c u v L 1 hv
  simp only [pow_one] at hlower
  have hden : 2*(1-f)*d ≤ (1+d)*P :=
    hprob.trans (mul_le_mul_of_nonneg_left hlower (by positivity))
  have hP : 0 < P := pos_of_mul_pos_right (lt_of_lt_of_le (by positivity) hden) (by positivity)
  have hmass := prefix_second_moment ht hc.le hd hv
  change E ≤ (m:ℝ)^2/4*(P*L+(L*(exp (-2*v)-exp (-2*u))+exp (-2*u)/d)) at hmass
  have hcost : L*(exp (-2*v)-exp (-2*u))+exp (-2*u)/d ≤ 2*(L:ℝ)*f*d+1/d := by
    have he := div_le_div_of_nonneg_right (exp_le_one_iff.mpr (by linarith : -2*u ≤ 0)) hd.le
    nlinarith only [he,mul_le_mul_of_nonneg_left hdiff (Nat.cast_nonneg (α := ℝ) L)]
  let B := (1+d)/(1-f)*((m:ℝ)*f^2+1/(2*d^2))
  have hB : 2*(L:ℝ)*f*d+1/d ≤ P*B := by
    let C := ((m:ℝ)*f^2+1/(2*d^2))/(1-f)
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have lhs : 2*(1-f)*d*C = 2*(m:ℝ)*f^2*d+1/d := by
      dsimp [C]; field_simp [hd.ne',sub_ne_zero.mpr hf'.ne']
    have rhs : (1+d)*P*C = P*B := by dsimp [B,C]; ring
    have he := mul_le_mul_of_nonneg_right hden hC
    rw [lhs,rhs] at he
    nlinarith only [he,mul_le_mul_of_nonneg_right hL (mul_nonneg hf hd.le)]
  have hE : E ≤ P*((m:ℝ)^2/4)*(f*m+B) := by
    have h' := add_le_add (mul_le_mul_of_nonneg_left hL hP.le) (hcost.trans hB)
    nlinarith only [hmass,mul_le_mul_of_nonneg_left h' (by positivity : 0 ≤ (m:ℝ)^2/4)]
  change E/(P*σ^2) ≤ ((m:ℝ)^3/(4*σ^2))*(f+(1+d)/(1-f)*(f^2+1/(2*m*d^2)))
  apply (div_le_iff₀ (mul_pos hP (sq_pos_of_pos hσ))).mpr
  apply hE.trans_eq
  dsimp only [B]
  field_simp [hd.ne',hm'.ne',hσ.ne',sub_ne_zero.mpr hf'.ne']

end CentralUnimodality.MarkedExcursion
