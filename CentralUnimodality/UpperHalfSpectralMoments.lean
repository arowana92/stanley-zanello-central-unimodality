module

public import CentralUnimodality.UniformSuffixMoments
public import CentralUnimodality.UpperHalfVariance
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Numerical spectral errors for the full range of upper-half saddles,
including original tilts beyond the bounded parameter window. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

private theorem gaussian_tail_eleven : exp (-((11:ℝ)^2/10)) ≤ 1/100000 := by
  have h : (27/10:ℝ) ≤ exp 1 := by linarith only [exp_one_gt_d9]
  have H := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 27/10) h 12
  rw [← exp_nat_mul] at H
  norm_num at H
  have hh := (exp_le_exp.mpr (by norm_num : (12:ℝ) ≤ 11^2/10))
  rw [exp_neg,← one_div]
  exact one_div_le_one_div_of_le (by norm_num) (by linarith only [H,hh])

theorem upper_half_band_budget {M σ : ℝ} (hM : 2048 ≤ M) (hσ : 0 ≤ σ) (hu : σ ≤ M^2)
    (r : ℕ) (hr : r ≤ 2) : σ*(π*σ)^r*exp (-((13/125)*M/2)) ≤ 1/1000000 := by
  have hp : 0 ≤ M/640 := by linarith
  have hm : 1 ≤ M := by linarith
  have hs : (π*σ)^r ≤ (4*M^2)^2 := (pow_le_pow_left₀ (by positivity)
    (mul_le_mul pi_lt_four.le hu hσ (by norm_num)) r).trans
    (pow_le_pow_right₀ (by nlinarith only [one_le_pow₀ hm (n:=2)] : 1 ≤ 4*M^2) hr)
  have he : M/240 ≤ exp (M/640) := by
    have H := mul_le_mul (by linarith only [exp_one_gt_d9] : (8/3:ℝ) ≤ exp 1)
      (show M/640 ≤ exp (M/640-1) by linarith only [add_one_le_exp (M/640-1)]) hp (exp_pos _).le
    rw [← exp_add,show 1+(M/640-1)=M/640 by ring] at H
    linarith only [H]
  have HE := pow_le_pow_left₀ (by linarith only [hp] : 0 ≤ M/240) he 32
  rw [← exp_nat_mul] at HE
  have hlarge := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2048) hM 26)
    (pow_nonneg (by linarith only [hm] : 0 ≤ M) 6)
  have hpoly : 16*M^6 ≤ 1/1000000*(M/240)^32 := by
    norm_num at hlarge; nlinarith only [hlarge,pow_nonneg (by linarith only [hm] : 0 ≤ M) 6]
  rw [exp_neg,← div_eq_mul_inv,div_le_iff₀ (exp_pos _)]
  calc
    _ ≤ M^2*(4*M^2)^2 := mul_le_mul hu hs (by positivity) (by positivity)
    _ = 16*M^6 := by ring
    _ ≤ _ := hpoly.trans (mul_le_mul_of_nonneg_left (HE.trans (exp_le_exp.mpr (by norm_num; linarith only [hm]))) (by norm_num))

/-- The bounds include the normal reference's lattice correction at
orders one and two. Here M can be any suffix of at least 3685 labels. -/
theorem upper_half_spectral_moments {m M : ℕ} (hM : 3685 ≤ M) (hMm : M ≤ m)
    {c σ : ℝ} (hc : 0 ≤ c) (hcm : c*m ≤ 1) (hσ : 0<σ) (hV : suffixVariance c M=σ^2) :
    scaledSpectralMoment c σ M 0 ≤ 16/1000 ∧ scaledSpectralMoment c σ M 1+1/σ ≤ 32/1000 ∧
      scaledSpectralMoment c σ M 2+1/σ^2 ≤ 69/1000 := by
  have hM' : (3685:ℝ) ≤ M := by exact_mod_cast hM
  have hm' : 1 ≤ (M:ℝ) := by linarith
  have per := upper_half_suffix_labels hMm hc hcm
  have ⟨hl,hu⟩ := suffix_variance_bounds c M (by norm_num : (0:ℝ) ≤ 13/125)
    (fun i hi => ⟨(per i hi).1,(per i hi).2.1⟩)
  rw [hV] at hl hu
  have hs : 11*(M:ℝ) ≤ σ := by
    apply (sq_le_sq₀ (by positivity) hσ.le).mp
    nlinarith only [hl,mul_le_mul_of_nonneg_right hM' (sq_nonneg (M:ℝ)),sq_nonneg (M:ℝ)]
  have hhi : σ ≤ (M:ℝ)^2 := by
    apply (sq_le_sq₀ hσ.le (sq_nonneg _)).mp
    have H := pow_le_pow_left₀ (by positivity : 0 ≤ (M:ℝ)+1) (by linarith only [hm'] : (M:ℝ)+1 ≤ 2*M) 3
    have ht := pow_le_pow_right₀ hm' (by norm_num : 3 ≤ 4)
    nlinarith only [hu,H,ht,pow_nonneg (Nat.cast_nonneg (α:=ℝ) M) 3]
  have hlabels (i : ℕ) (hi : i ∈ Finset.range M) :
      |1-2*upChance (-(c*(i+1)))| ≤ 1 ∧ 13/125 ≤ labelVariance c (i+1) := by
    have H := up_total (c*(i+1))
    have hn (u : ℝ) : 0 ≤ upChance u := by dsimp only [upChance]; positivity
    exact ⟨abs_le.mpr ⟨by linarith only [H,hn (c*(i+1))],by linarith only [hn (-(c*(i+1)))]⟩,(per i hi).1⟩
  have bounded (r : ℕ) (hr : r ≤ 2) {A B : ℝ} (hA : absoluteGaussianMoment (9/20) (r+3) ≤ A)
      (hB : absoluteGaussianMoment (9/20) (r+4) ≤ B) :
      scaledSpectralMoment c σ M r ≤ (cubicFactor 11 1*A+quarticFactor 11*B+(2/100000)*30)/6+1/1000000 :=
    (uniform_spectral_budget (by norm_num) (by norm_num) (by norm_num) gaussian_tail_eleven c M hσ hs
      (by omega) hV hlabels hr hA hB).trans (by
        have H := upper_half_band_budget (by linarith only [hM'] : (2048:ℝ)≤M) hσ.le hhi r hr
        linarith only [H])
  obtain ⟨h₃,h₄,h₅,h₆⟩ := inner_gaussian_moments
  have H₀ := bounded 0 (by decide) h₃ h₄
  have H₁ := bounded 1 (by decide) h₄ h₅
  have H₂ := bounded 2 (by decide) h₅ h₆
  have hlσ : 10000 ≤ σ := by linarith only [hs,hM']
  have h₁ := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<10000) hlσ
  have h₂ := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<10000)
    (show (10000:ℝ) ≤ σ^2 by nlinarith only [hlσ,sq_nonneg (σ-1)])
  norm_num [cubicFactor,quarticFactor] at H₀ H₁ H₂
  exact ⟨by linarith only [H₀],by linarith only [H₁,h₁],by linarith only [H₂,h₂]⟩

end CentralUnimodality.MarkedExcursion
