module

public import CentralUnimodality.UniformSuffixEnvelope
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-! Integrate the parametric Fourier envelope against the three lattice
difference multipliers with the variance of the actual suffix law. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real MeasureTheory Set

theorem band_term_integrable (p M σ : ℝ) (r : ℕ) : Integrable (bandTerm p M σ r) := by
  unfold bandTerm
  rw [integrable_indicator_iff measurableSet_Ioc]
  exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)

theorem band_term_integral (p M : ℝ) {σ : ℝ} (hσ : 0 < σ) (r : ℕ) :
    (∫ x, bandTerm p M σ r x)=2*π*σ*(π*σ)^r*exp (-(p*M/2)) := by
  simp only [bandTerm,integral_indicator_const _ measurableSet_Ioc,
    Real.volume_real_Ioc_of_le (by nlinarith only [mul_pos pi_pos hσ] : -π*σ ≤ π*σ),smul_eq_mul]
  ring

theorem uniform_envelope_integral (a D p ε M : ℝ) {σ : ℝ} (hσ : 0 < σ) (r : ℕ) :
    Integrable (uniformEnvelope a D p ε M σ r) ∧
    (∫ x, uniformEnvelope a D p ε M σ r x) =
      cubicFactor a D*absoluteGaussianMoment (9/20) (r+3)+quarticFactor a*absoluteGaussianMoment (9/20) (r+4)+
      (2*ε)*absoluteGaussianMoment (1/10) r+2*π*σ*(π*σ)^r*exp (-(p*M/2)) := by
  have h₀ := (momentKernel_integrable (b := 9/20) (by norm_num) (r+3)).const_mul (cubicFactor a D)
  have h₁ := (momentKernel_integrable (b := 9/20) (by norm_num) (r+4)).const_mul (quarticFactor a)
  have h₂ := (momentKernel_integrable (b := 1/10) (by norm_num) r).const_mul (2*ε)
  have h₃ := band_term_integrable p M σ r
  refine ⟨((h₀.add h₁).add h₂).add h₃,?_⟩
  unfold uniformEnvelope
  rw [integral_add (f := fun x => _+_+_) ((h₀.add h₁).add h₂) h₃,
    integral_add (f := fun x => _+_) (h₀.add h₁) h₂,integral_add h₀ h₁]
  simp only [integral_const_mul,absoluteGaussianMoment,band_term_integral _ _ hσ]

theorem normalized_spectral_moment (c : ℝ) {σ : ℝ} (hσ : 0 < σ) (M r : ℕ) :
    scaledSpectralMoment c σ M r =
      (∫ x : ℝ, ‖suffixSpectralError c σ M (x/σ)‖*|x|^r)/(2*π) := by
  let g := fun θ => ‖suffixSpectralError c σ M θ‖*|θ|^r
  have he (x : ℝ) : ‖suffixSpectralError c σ M (x/σ)‖*|x|^r=σ^r*g (σ⁻¹*x) := by
    dsimp [g]
    rw [show σ⁻¹*x=x/σ by ring,abs_div,abs_of_pos hσ,div_pow]
    field_simp
  simp_rw [he]
  rw [integral_const_mul,Measure.integral_comp_inv_mul_left,abs_of_pos hσ,smul_eq_mul]
  change σ^(r+1)/(2*π)*spectralMoment c σ M r = σ^r*(σ*spectralMoment c σ M r)/(2*π)
  rw [pow_succ]; ring

theorem uniform_spectral_budget {a D p ε : ℝ} (ha : 0<a) (hD : 0 ≤ D) (hp : 0 ≤ p)
    (hε : exp (-(a^2/10)) ≤ ε) (c : ℝ) (M : ℕ) {σ : ℝ} (hσ : 0 < σ) (hs : a*(M:ℝ) ≤ σ)
    (hM : 0 < M) (hV : suffixVariance c M=σ^2)
    (hlabels : ∀ i ∈ Finset.range M, |1-2*upChance (-(c*(i+1)))| ≤ D ∧
      p ≤ labelVariance c (i+1)) {r : ℕ} (hr : r ≤ 2) {A B : ℝ}
    (hA : absoluteGaussianMoment (9/20) (r+3) ≤ A) (hB : absoluteGaussianMoment (9/20) (r+4) ≤ B) :
    scaledSpectralMoment c σ M r ≤ (cubicFactor a D*A+quarticFactor a*B+(2*ε)*30)/6+
      σ*(π*σ)^r*exp (-(p*M/2)) := by
  have H := uniform_suffix_envelope ha hD hp hε c M hσ hs hM hV hlabels r
  obtain ⟨hint,he⟩ := uniform_envelope_integral a D p ε (M:ℝ) hσ r
  have hi := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x : ℝ => by positivity :
    ∀ x : ℝ, 0 ≤ ‖suffixSpectralError c σ M (x/σ)‖*|x|^r)) hint (Filter.Eventually.of_forall H)
  rw [he] at hi
  rw [normalized_spectral_moment c hσ]
  apply (div_le_div_of_nonneg_right hi (by positivity)).trans
  rw [add_div,show 2*π*σ*(π*σ)^r*exp (-(p*M/2))/(2*π)=σ*(π*σ)^r*exp (-(p*M/2)) by field_simp]
  apply add_le_add _ le_rfl
  have hε₀ := (exp_pos _).le.trans hε
  have hC : 0 ≤ cubicFactor a D := by dsimp [cubicFactor]; positivity
  have hQ : 0 ≤ quarticFactor a := by dsimp [quarticFactor]; positivity
  have hmon := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hA hC)
    (mul_le_mul_of_nonneg_left hB hQ)) (mul_le_mul_of_nonneg_left (tail_gaussian_moments r hr) (by positivity : 0 ≤ 2*ε))
  have hn (b : ℝ) (k : ℕ) : 0 ≤ absoluteGaussianMoment b k :=
    integral_nonneg (fun x => by dsimp [momentKernel]; positivity)
  apply (div_le_div_of_nonneg_right hmon (by positivity)).trans
  apply div_le_div_of_nonneg_left _ (by norm_num) (by linarith only [pi_gt_three])
  exact (add_nonneg (add_nonneg (mul_nonneg hC (hn ..)) (mul_nonneg hQ (hn ..)))
    (mul_nonneg (by positivity) (hn ..))).trans hmon

end CentralUnimodality.MarkedExcursion
