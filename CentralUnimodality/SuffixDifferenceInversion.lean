module

public import CentralUnimodality.NormalRankReference
public import CentralUnimodality.LatticeDifference
public import CentralUnimodality.PrefixDifferenceBounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Transfer weighted integrals of the Fourier error to the mass, forward
difference and centered second difference at every integer rank. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real Set MeasureTheory

noncomputable def bandTransform (c : ℝ) (m : ℕ) : ℝ → ℂ :=
  (Ioc (-π) π).indicator (fun θ => suffixTransform c θ m)

noncomputable def suffixSpectralError (c σ : ℝ) (m : ℕ) (θ : ℝ) : ℂ :=
  bandTransform c m θ - (exp (-(σ^2*θ^2/2)):ℂ)

theorem suffixSpectralError_inside {θ : ℝ} (hθ : θ ∈ Ioc (-π) π) (c σ : ℝ) (m : ℕ) :
    suffixSpectralError c σ m θ = suffixTransform c θ m - (exp (-(σ^2*θ^2/2)):ℂ) := by
  simp [suffixSpectralError,bandTransform,hθ]

theorem suffixSpectralError_outside {θ : ℝ} (hθ : θ ∉ Ioc (-π) π) (c σ : ℝ) (m : ℕ) :
    ‖suffixSpectralError c σ m θ‖ = exp (-(σ^2*θ^2/2)) := by
  simp only [suffixSpectralError,bandTransform,indicator_of_notMem hθ,zero_sub,norm_neg,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (exp_pos _)]

/-- Integral of the absolute spectral error, weighted for a difference of order r. -/
noncomputable def spectralMoment (c σ : ℝ) (m r : ℕ) :=
  ∫ θ : ℝ, ‖suffixSpectralError c σ m θ‖*|θ|^r

private theorem transform_continuous (c : ℝ) (m : ℕ) : Continuous (fun θ => suffixTransform c θ m) := by
  unfold suffixTransform bernoulliFactor; fun_prop

private theorem band_mul (c : ℝ) (m : ℕ) (g : ℝ → ℂ) :
    (fun θ => bandTransform c m θ*g θ) = (Ioc (-π) π).indicator (fun θ => suffixTransform c θ m*g θ) := by
  funext θ; by_cases h : θ ∈ Ioc (-π) π <;> simp [bandTransform,h]

theorem band_integrable (c : ℝ) (m : ℕ) {g : ℝ → ℂ} (hg : Continuous g) :
    Integrable (fun θ => bandTransform c m θ*g θ) := by
  rw [band_mul,integrable_indicator_iff measurableSet_Ioc]
  exact ((transform_continuous c m).mul hg).integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem band_inverse (c : ℝ) (m : ℕ) (k : ℤ) :
    (∫ θ, bandTransform c m θ*phase (-θ*((k:ℝ)-meanRank c m))) =
      (((2*π)*freeRankMass c m k:ℝ):ℂ) := by
  rw [band_mul,integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by linarith only [pi_pos] : -π ≤ π),suffix_rank_inversion]
  push_cast; rfl

private theorem weighted_normal {σ : ℝ} (hσ : 0 < σ) (r : ℕ) :
    Integrable (fun θ : ℝ => exp (-(σ^2*θ^2/2))*|θ|^r) := by
  have H := (integrable_rpow_mul_exp_neg_mul_sq (b := σ^2/2) (by positivity) (s := (r:ℝ))
    (by have := Nat.cast_nonneg (α := ℝ) r; linarith)).norm
  simpa only [Real.norm_eq_abs,abs_mul,abs_of_pos (exp_pos _),Real.rpow_natCast,abs_pow,
    show ∀ θ : ℝ, -(σ^2/2)*θ^2 = -(σ^2*θ^2/2) by intro θ; ring,mul_comm] using H

theorem spectralMoment_integrable (c : ℝ) {σ : ℝ} (hσ : 0 < σ) (m r : ℕ) :
    Integrable (fun θ : ℝ => ‖suffixSpectralError c σ m θ‖*|θ|^r) := by
  have h₁ := band_integrable c m (g := fun θ => (θ:ℂ)^r) (by fun_prop)
  have h₂ := weighted_normal hσ r
  have hm : Measurable (bandTransform c m) := (transform_continuous c m).measurable.indicator measurableSet_Ioc
  apply (h₁.norm.add h₂).mono'
  · apply Measurable.aestronglyMeasurable
    unfold suffixSpectralError
    fun_prop
  · apply Filter.Eventually.of_forall
    intro θ
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    have H := norm_sub_le (bandTransform c m θ) ((exp (-(σ^2*θ^2/2)):ℝ):ℂ)
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (exp_pos _)] at H
    exact (mul_le_mul_of_nonneg_right H (by positivity)).trans_eq (add_mul ..)

private noncomputable def siteError (c σ : ℝ) (m : ℕ) (k : ℤ) :=
  (2*π)*(freeRankMass c m k-normalDensity (((k:ℝ)-meanRank c m)/σ)/σ)

private noncomputable def siteIntegrand (c σ : ℝ) (m : ℕ) (k : ℤ) (θ : ℝ) :=
  suffixSpectralError c σ m θ*phase (-θ*((k:ℝ)-meanRank c m))

private theorem site_integrable (c : ℝ) {σ : ℝ} (hσ : 0 < σ) (m : ℕ) (k : ℤ) :
    Integrable (siteIntegrand c σ m k) := by
  have hm : Measurable (bandTransform c m) := (transform_continuous c m).measurable.indicator measurableSet_Ioc
  apply (spectralMoment_integrable c hσ m 0).mono'
  · apply Measurable.aestronglyMeasurable
    unfold siteIntegrand suffixSpectralError phase
    fun_prop
  · exact Filter.Eventually.of_forall (fun θ => by simp [siteIntegrand])

private theorem site_inverse (c : ℝ) {σ : ℝ} (hσ : 0 < σ) (m : ℕ) (k : ℤ) :
    (∫ θ, siteIntegrand c σ m k θ) = (siteError c σ m k:ℂ) := by
  let s := (k:ℝ)-meanRank c m
  let g := fun θ : ℝ => phase (-θ*s)
  have hg : Continuous g := by dsimp [g,phase]; fun_prop
  have hn : Integrable (fun θ : ℝ => (exp (-(σ^2*θ^2/2)):ℂ)*g θ) := by
    apply (weighted_normal hσ 0).mono'
    · exact (Continuous.mul (by fun_prop) hg).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun θ => by simp only [g,norm_mul,phase_norm,mul_one,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos (exp_pos _),pow_zero,le_refl])
  simp only [siteIntegrand,suffixSpectralError,sub_mul]
  rw [integral_sub (band_integrable c m hg) hn,band_inverse,normal_rank_inverse hσ]
  unfold siteError; push_cast; ring


/-- All three estimates use the same spectral residual, including the full
Gaussian tail beyond the lattice integration interval. -/
theorem suffix_difference_inversion (c : ℝ) {σ : ℝ} (hσ : 0 < σ) (m : ℕ) (k : ℤ) :
    let E := fun j : ℤ => (2*π)*(freeRankMass c m j-normalDensity (((j:ℝ)-meanRank c m)/σ)/σ)
    |E k| ≤ spectralMoment c σ m 0 ∧
    |E (k+1)-E k| ≤ spectralMoment c σ m 1 ∧
    |E (k-1)+E (k+1)-2*E k| ≤ spectralMoment c σ m 2 := by
  have H (r : Fin 3) := lattice_difference_integral (suffixSpectralError c σ m) (meanRank c m)
    (siteError c σ m) (site_integrable c hσ m) (site_inverse c hσ m) r k
    (spectralMoment_integrable c hσ m r.val) (fun _ => le_rfl)
  exact ⟨H 0,H 1,H 2⟩

/-- Scaled integral error, before replacing Gaussian lattice differences by derivatives. -/
noncomputable def scaledSpectralMoment (c σ : ℝ) (m r : ℕ) :=
  σ^(r+1)/(2*π)*spectralMoment c σ m r

/-- Three scalar integrals suffice for the uniform rank estimates used in
the prefix variance argument. The derivative allowances use the actual σ. -/
theorem free_suffix_of_spectral_allowances {ε₀ ε₁ ε₂ : ℝ} (c : ℝ) {σ : ℝ} (hσ : 0 < σ) (m : ℕ)
    (h₀ : scaledSpectralMoment c σ m 0 ≤ ε₀)
    (h₁ : scaledSpectralMoment c σ m 1+1/σ ≤ ε₁)
    (h₂ : scaledSpectralMoment c σ m 2+1/σ^2 ≤ ε₂) : FreeSuffixApproximation c m σ ε₀ ε₁ ε₂ := by
  intro k
  let y (j : ℤ) := ((j:ℝ)-meanRank c m)/σ
  let N (j : ℤ) := normalDensity (y j)
  let A := freeRankMass c m
  let B (j : ℤ) := σ*A j-N j
  let E (j : ℤ) := (2*π)*(A j-N j/σ)
  have HE (j : ℤ) : E j = (2*π/σ)*B j := by dsimp [E,B]; field_simp
  obtain ⟨M₀,M₁,M₂⟩ := suffix_difference_inversion c hσ m k
  change |E k| ≤ _ at M₀
  change |E (k+1)-E k| ≤ _ at M₁
  change |E (k-1)+E (k+1)-2*E k| ≤ _ at M₂
  have scale (r : ℕ) (b : ℝ) (h : |(2*π/σ)*b| ≤ spectralMoment c σ m r) :
      |σ^r*b| ≤ scaledSpectralMoment c σ m r := by
    have hr : 0 ≤ σ^(r+1)/(2*π) := by positivity
    have H := mul_le_mul_of_nonneg_left h hr
    rw [abs_mul,abs_of_pos (by positivity : 0 < 2*π/σ)] at H
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ σ^r)]
    apply le_trans _ H
    rw [pow_succ]; apply le_of_eq; field_simp
  rw [HE] at M₀
  simp only [HE,← mul_sub] at M₁
  rw [HE,HE,HE,← mul_add,show 2*(2*π/σ*B k)=2*π/σ*(2*B k) by ring,← mul_sub] at M₂
  have F₀ := scale 0 _ M₀
  have F₁ := scale 1 _ M₁
  have F₂ := scale 2 _ M₂
  simp only [pow_zero,one_mul] at F₀
  simp only [pow_one] at F₁
  have yup : y (k+1)=y k+1/σ := by dsimp [y]; push_cast; ring
  have ydn : y (k-1)=y k-1/σ := by dsimp [y]; push_cast; ring
  have G₁ := normal_forward_error hσ (y k)
  have G₂ := normal_curvature_error hσ (y k)
  rw [← yup] at G₁
  rw [← yup,← ydn] at G₂
  change |σ*(N (k+1)-N k)+y k*N k| ≤ _ at G₁
  change |σ^2*(N (k-1)+N (k+1)-2*N k)-((y k)^2-1)*N k| ≤ _ at G₂
  dsimp only
  change |B k| ≤ _ ∧ |σ^2*(A (k+1)-A k)+normalHeight*y k*bell (y k)| ≤ _ ∧
    |σ^3*(A (k-1)+A (k+1)-2*A k)-normalHeight*((y k)^2-1)*bell (y k)| ≤ _
  refine ⟨F₀.trans h₀,?_,?_⟩
  · apply le_trans _ ((add_le_add F₁ G₁).trans h₁)
    apply le_trans _ (abs_add_le _ _)
    apply le_of_eq; congr 1; dsimp [B,N,normalDensity]; ring
  · apply le_trans _ ((add_le_add F₂ G₂).trans h₂)
    apply le_trans _ (abs_add_le _ _)
    apply le_of_eq; congr 1; dsimp [B,N,normalDensity]; ring

theorem free_suffix_of_spectral_moments (c : ℝ) {σ : ℝ} (hσ : 0 < σ) (m : ℕ)
    (h₀ : scaledSpectralMoment c σ m 0 ≤ 5/1000)
    (h₁ : scaledSpectralMoment c σ m 1+1/σ ≤ 7/1000)
    (h₂ : scaledSpectralMoment c σ m 2+1/σ^2 ≤ 10/1000) : FreeSuffixApproximation c m σ :=
  free_suffix_of_spectral_allowances c hσ m h₀ h₁ h₂

end CentralUnimodality.MarkedExcursion
