module

public import CentralUnimodality.SuffixSpectralEnvelope
public import CentralUnimodality.UniformSuffixMoments

/-! Numerical local normal approximation for every independent suffix in
the right-flank range, and its use for the surviving prefix. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real MeasureTheory Set

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
    have H := uniform_spectral_budget (by norm_num) (by norm_num) (by norm_num) right_gaussian_tail c M hσ hlo
      (by omega) hV hp hr ha hb
    have ht := outer_exponential_budget hM' hσ.le hhi r hr
    rw [show (6/25)*(M:ℝ)/2 = 3*M/25 by ring] at H
    dsimp only [cubicFactor,quarticFactor] at H
    unfold innerCubic innerQuartic; linarith only [H,ht]
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
