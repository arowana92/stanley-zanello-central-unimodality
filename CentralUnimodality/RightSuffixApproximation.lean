module

public import CentralUnimodality.SuffixSpectralEnvelope
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-! Numerical local normal approximation for every independent suffix in
the right-flank range, and its use for the surviving prefix. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real MeasureTheory Set

private theorem last_integrable (M σ : ℝ) (r : ℕ) : Integrable (lastArc M σ r) := by
  unfold lastArc
  rw [integrable_indicator_iff measurableSet_Ioc]
  exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)

private theorem envelope_integral (M : ℝ) {σ : ℝ} (hσ : 0 < σ) (r : ℕ) :
    Integrable (suffixEnvelope M σ r) ∧
    (∫ x, suffixEnvelope M σ r x) =
      innerCubic*absoluteGaussianMoment (9/20) (r+3)+innerQuartic*absoluteGaussianMoment (9/20) (r+4)+
      2/1000000*absoluteGaussianMoment (1/10) r+2*π*σ*(π*σ)^r*exp (-(3*M/25)) := by
  have h₀ := (momentKernel_integrable (b := 9/20) (by norm_num) (r+3)).const_mul innerCubic
  have h₁ := (momentKernel_integrable (b := 9/20) (by norm_num) (r+4)).const_mul innerQuartic
  have h₂ := (momentKernel_integrable (b := 1/10) (by norm_num) r).const_mul (2/1000000)
  have h₃ := last_integrable M σ r
  refine ⟨((h₀.add h₁).add h₂).add h₃,?_⟩
  unfold suffixEnvelope
  rw [integral_add (f := fun x => _+_+_) ((h₀.add h₁).add h₂) h₃,
    integral_add (f := fun x => _+_) (h₀.add h₁) h₂,integral_add h₀ h₁]
  simp only [integral_const_mul,absoluteGaussianMoment,lastArc,integral_indicator_const _ measurableSet_Ioc,
    Real.volume_real_Ioc_of_le (by nlinarith only [mul_pos pi_pos hσ] : -π*σ ≤ π*σ),smul_eq_mul]
  ring

private theorem scaled_moment_integral (c : ℝ) {σ : ℝ} (hσ : 0 < σ) (M r : ℕ) :
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

/-- The three signed errors at every integer site for the actual modeled
suffix. No limiting argument or finite enumeration of rank sites is used. -/
theorem right_free_suffix {m M : ℕ} (hm : 4096 ≤ m) (hM : 3685 ≤ M) (hMm : M ≤ m)
    {c σ : ℝ} (hc : 0 ≤ c) (hs : 2*c*((m:ℝ)*√m) ≤ 25)
    (hσ : 0 < σ) (hV : suffixVariance c M=σ^2) : FreeSuffixApproximation c M σ := by
  obtain ⟨hp,hl,hu⟩ := suffix_saddle_parameters hm hMm hc hs
  rw [hV] at hl hu
  obtain ⟨hlo,hhi⟩ := right_suffix_scale hM hσ hl hu
  have hM' : (3685:ℝ) ≤ M := by exact_mod_cast hM
  have hs' : 10000 ≤ σ := by linarith only [hM',hlo]
  have hs₁ : 1/σ ≤ 1/10000 := one_div_le_one_div_of_le (by norm_num) hs'
  have hs₂ : 1/σ^2 ≤ 1/10000 := one_div_le_one_div_of_le (by norm_num)
    (by nlinarith only [hs',sq_nonneg (σ-1)])
  have H (r : ℕ) (hr : r ≤ 2) {a b : ℝ}
      (ha : absoluteGaussianMoment (9/20) (r+3) ≤ a) (hb : absoluteGaussianMoment (9/20) (r+4) ≤ b) :
      scaledSpectralMoment c σ M r ≤ (innerCubic*a+innerQuartic*b+2/1000000*30)/6+1/1000000 := by
    have I := right_suffix_envelope c M hσ hlo (by omega) hV hp r
    obtain ⟨hg,hgi⟩ := envelope_integral (M:ℝ) hσ r
    have hi := integral_mono_of_nonneg (Filter.Eventually.of_forall
      (fun x : ℝ => by positivity : ∀ x : ℝ, 0 ≤ ‖suffixSpectralError c σ M (x/σ)‖*|x|^r)) hg
      (Filter.Eventually.of_forall I)
    rw [hgi] at hi
    rw [scaled_moment_integral c hσ]
    apply (div_le_div_of_nonneg_right hi (by positivity)).trans
    rw [add_div,show 2*π*σ*(π*σ)^r*exp (-(3*(M:ℝ)/25))/(2*π) =
        σ*(π*σ)^r*exp (-(3*M/25)) by field_simp]
    apply add_le_add _ (outer_exponential_budget hM' hσ.le hhi r hr)
    have h₁ : 0 ≤ innerCubic := by norm_num [innerCubic]
    have h₂ : 0 ≤ innerQuartic := by norm_num [innerQuartic]
    have hmon := add_le_add (add_le_add (mul_le_mul_of_nonneg_left ha h₁) (mul_le_mul_of_nonneg_left hb h₂))
      (mul_le_mul_of_nonneg_left (tail_gaussian_moments r hr) (by norm_num : (0:ℝ) ≤ 2/1000000))
    have hn : 0 ≤ innerCubic*absoluteGaussianMoment (9/20) (r+3)+innerQuartic*absoluteGaussianMoment (9/20) (r+4)+
        2/1000000*absoluteGaussianMoment (1/10) r := by
      have pos (d : ℝ) (k : ℕ) : 0 ≤ absoluteGaussianMoment d k :=
        integral_nonneg (fun x => by dsimp [momentKernel]; positivity)
      exact add_nonneg (add_nonneg (mul_nonneg h₁ (pos ..)) (mul_nonneg h₂ (pos ..)))
        (mul_nonneg (by norm_num) (pos ..))
    apply (div_le_div_of_nonneg_right hmon (by positivity)).trans
    exact div_le_div_of_nonneg_left (hn.trans hmon) (by norm_num) (by linarith only [pi_gt_three])
  obtain ⟨u,v,w,z⟩ := inner_gaussian_moments
  have h₀ := H 0 (by decide) u v
  have h₁ := H 1 (by decide) v w
  have h₂ := H 2 (by decide) w z
  norm_num [innerCubic,innerQuartic] at h₀ h₁ h₂
  apply free_suffix_of_spectral_moments c hσ M
  · linarith only [h₀]
  · linarith only [h₁,hs₁]
  · linarith only [h₂,hs₂]

/-- Equation (3) for the surviving original prefix at an exact saddle.
The scale is the positive standard deviation of the actual remaining labels. -/
theorem right_prefix_differences {m L : ℕ} (hm : 4096 ≤ m) (hM : 3685 ≤ m-L)
    {c f : ℝ} (hc : 0 < c) (hs : 2*c*((m:ℝ)*√m) ≤ 25)
    (hf : 0 ≤ f) (hf' : f < 1) (hL : (L:ℝ) ≤ f*m) {j : ℤ} (hj : meanRank c m=j) :
    let σ := √(suffixVariance c (m-L))
    let P := live c (c*m) L 1
    let A := fun k => prefixSiteMass c m L k/P
    let B := varianceLimit m c f σ
    3989/10000*exp (-B/2)-5/1000 ≤ σ*A j ∧ |σ^2*(A (j+1)-A j)| < 1/4 ∧
      σ^3*(A (j-1)+A (j+1)-2*A j) ≤ normalHeight*(B/(1+B/2)-exp (-B/2))+10/1000 := by
  let M := m-L
  have hm' : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < m-L)
  have hl := (suffix_saddle_parameters hm (Nat.sub_le m L) hc.le hs).2.1
  have hv : 0 < suffixVariance c M := (by positivity : 0 < 2/25*(M:ℝ)^3).trans_le hl
  exact conditional_prefix_differences (by omega) hc hf hf' hL (Real.sqrt_pos.mpr hv)
    (right_free_suffix hm hM (Nat.sub_le m L) hc.le hs (Real.sqrt_pos.mpr hv) (Real.sq_sqrt hv.le).symm) hj

/-- The ceiling cuts used for (3) both leave enough labels. -/
theorem right_prefix_cut_lengths {m : ℕ} (hm : 4096 ≤ m) :
    3685 ≤ m-(m+9)/10 ∧ 3685 ≤ m-(m+13)/14 := by omega

end CentralUnimodality.MarkedExcursion
