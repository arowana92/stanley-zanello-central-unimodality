module

public import CentralUnimodality.SuffixDifferenceInversion
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Real.Pi.Bounds

/-! Absolute Gaussian moments and rational envelopes for the independent
suffix of at least 3685 labels in the right-flank calculation. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real MeasureTheory

noncomputable def momentKernel (b : ℝ) (r : ℕ) (x : ℝ) := |x|^r*exp (-b*x^2)
noncomputable def absoluteGaussianMoment (b : ℝ) (r : ℕ) := ∫ x, momentKernel b r x

theorem momentKernel_integrable {b : ℝ} (hb : 0 < b) (r : ℕ) : Integrable (momentKernel b r) := by
  have H := (integrable_rpow_mul_exp_neg_mul_sq hb (s := (r:ℝ))
    (by have := Nat.cast_nonneg (α := ℝ) r; linarith)).norm
  change Integrable (fun x : ℝ => |x|^r*exp (-b*x^2))
  simpa only [Real.norm_eq_abs,Real.rpow_natCast,abs_mul,abs_pow,abs_of_pos (exp_pos _)] using H

theorem absoluteGaussianMoment_eq {b : ℝ} (hb : 0 < b) (r : ℕ) :
    absoluteGaussianMoment b r = b^(-((r:ℝ)+1)/2)*Gamma (((r:ℝ)+1)/2) := by
  let g (x : ℝ) := x^r*exp (-b*x^2)
  have hg (x : ℝ) : momentKernel b r x = g |x| := by simp [momentKernel,g]
  rw [absoluteGaussianMoment]; simp_rw [hg]
  rw [integral_comp_abs]
  have H := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (r:ℝ)) (by norm_num)
    (by have := Nat.cast_nonneg (α := ℝ) r; linarith) hb
  simp only [Real.rpow_natCast,Real.rpow_two] at H
  dsimp only [g]; rw [H]; ring

private theorem moment_zero (b : ℝ) : absoluteGaussianMoment b 0 = √(π/b) := by
  simpa [absoluteGaussianMoment,momentKernel] using integral_gaussian b

private theorem moment_one {b : ℝ} (hb : 0 < b) : absoluteGaussianMoment b 1 = 1/b := by
  rw [absoluteGaussianMoment_eq hb]
  norm_num [one_div,Real.rpow_neg_one]

theorem absoluteGaussianMoment_succ_two {b : ℝ} (hb : 0 < b) (r : ℕ) :
    absoluteGaussianMoment b (r+2) = ((r:ℝ)+1)/(2*b)*absoluteGaussianMoment b r := by
  let a := ((r:ℝ)+1)/2
  have ha : 0 < a := by dsimp [a]; positivity
  rw [absoluteGaussianMoment_eq hb,absoluteGaussianMoment_eq hb]
  push_cast
  rw [show ((r:ℝ)+2+1)/2=a+1 by dsimp [a]; ring,
    show -((r:ℝ)+2+1)/2=(-a)+(-1) by dsimp [a]; ring,
    rpow_add hb,Real.rpow_neg_one,Real.Gamma_add_one ha.ne']
  dsimp [a]; ring

/-- Inner-arc integrals for the three difference multipliers alone. -/
theorem inner_gaussian_low_moments :
    absoluteGaussianMoment (9/20) 0 ≤ 8/3 ∧ absoluteGaussianMoment (9/20) 1 ≤ 20/9 ∧
    absoluteGaussianMoment (9/20) 2 ≤ 80/27 := by
  have h₀ : absoluteGaussianMoment (9/20) 0 ≤ 8/3 := by
    rw [moment_zero]
    exact Real.sqrt_le_iff.mpr ⟨by norm_num,by linarith only [pi_lt_d2]⟩
  have h₁ := moment_one (b := 9/20) (by norm_num)
  have h₂ := absoluteGaussianMoment_succ_two (b := 9/20) (by norm_num) 0
  norm_num at h₁ h₂
  refine ⟨h₀,?_,?_⟩ <;> linarith only [h₀,h₁,h₂]

/-- Whole-line bounds used at powers r+3 and r+4 of the inner-arc error. -/
theorem inner_gaussian_moments :
    absoluteGaussianMoment (9/20) 3 ≤ 5 ∧ absoluteGaussianMoment (9/20) 4 ≤ 10 ∧
    absoluteGaussianMoment (9/20) 5 ≤ 22 ∧ absoluteGaussianMoment (9/20) 6 ≤ 55 := by
  let b : ℝ := 9/20
  have hb : 0 < b := by norm_num [b]
  have h₀ : absoluteGaussianMoment b 0 ≤ 8/3 := inner_gaussian_low_moments.1
  have h₁ := moment_one hb
  have R := absoluteGaussianMoment_succ_two hb
  have h₂ := R 0
  have h₃ := R 1
  have h₄ := R 2
  have h₅ := R 3
  have h₆ := R 4
  norm_num [b] at h₀ h₁ h₂ h₃ h₄ h₅ h₆
  refine ⟨?_,?_,?_,?_⟩ <;> linarith only [h₀,h₁,h₂,h₃,h₄,h₅,h₆]

theorem tail_gaussian_moments (r : ℕ) (hr : r ≤ 2) : absoluteGaussianMoment (1/10) r ≤ 30 := by
  have h₀ : absoluteGaussianMoment (1/10) 0 ≤ 6 := by
    rw [moment_zero]; apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · linarith only [pi_lt_d2]
  have h₁ := moment_one (b := 1/10) (by norm_num)
  have h₂ := absoluteGaussianMoment_succ_two (b := 1/10) (by norm_num) 0
  norm_num at h₁ h₂
  interval_cases r <;> linarith only [h₀,h₁,h₂]

/-- Enough decay on the last arc even after multiplying by the bandwidth
and two finite-difference multipliers. -/
theorem outer_exponential_budget {M σ : ℝ} (hM : 3685 ≤ M) (hσ : 0 ≤ σ)
    (hu : σ ≤ M^2) (r : ℕ) (hr : r ≤ 2) : σ*(π*σ)^r*exp (-(3*M/25)) ≤ 1/1000000 := by
  have hM' : 1 ≤ M := by linarith
  have hp : 0 ≤ M/200 := by linarith
  have hs : (π*σ)^r ≤ (4*M^2)^2 := (pow_le_pow_left₀ (by positivity)
    (mul_le_mul pi_lt_four.le hu hσ (by norm_num)) r).trans
    (pow_le_pow_right₀ (by nlinarith only [one_le_pow₀ hM' (n := 2)] : 1 ≤ 4*M^2) hr)
  have hx : (M/200)^24 ≤ exp (3*M/25) := by
    have h : M/200 ≤ exp (M/200) := by linarith only [Real.add_one_le_exp (M/200)]
    have H := pow_le_pow_left₀ hp h 24
    rw [← Real.exp_nat_mul] at H
    convert H using 2; norm_num; ring
  have hl := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3685) hM 18
  have hm : 0 ≤ M^6 := by positivity
  have H : 16*M^6 ≤ 1/1000000*(M/200)^24 := by
    have L := mul_le_mul_of_nonneg_right hl hm
    norm_num at L
    nlinarith only [L,hm]
  rw [exp_neg,← div_eq_mul_inv,div_le_iff₀ (exp_pos _)]
  calc
    _ ≤ M^2*(4*M^2)^2 := mul_le_mul hu hs (by positivity) (by positivity)
    _ = 16*M^6 := by ring
    _ ≤ _ := H.trans (mul_le_mul_of_nonneg_left hx (by norm_num))

end CentralUnimodality.MarkedExcursion
