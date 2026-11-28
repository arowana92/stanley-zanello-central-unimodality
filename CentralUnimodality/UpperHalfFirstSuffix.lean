module

public import CentralUnimodality.UpperHalfSpectralMoments
public import CentralUnimodality.ShortSuffixRanks
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Real.Pi.Bounds

/-! A uniform mass and forward-difference allowance for the independent
suffix left at any first crossing before the fifteen-sixteenths cut. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real Set MeasureTheory

private theorem low_moment_five (r : Fin 3) (hr : r.val ≤ 1) : absoluteGaussianMoment (1/5) r.val ≤ 5 := by
  fin_cases r
  · have H : absoluteGaussianMoment (1/5) 0=√(π/(1/5)) := by
      simpa [absoluteGaussianMoment,momentKernel] using integral_gaussian (1/5:ℝ)
    change absoluteGaussianMoment (1/5) 0 ≤ 5
    rw [H]
    apply (sqrt_le_left (by norm_num)).mpr; linarith only [pi_lt_four]
  · rw [absoluteGaussianMoment_eq (by norm_num)]
    norm_num [Real.rpow_neg_one]
  · exact False.elim (by norm_num at hr)

private theorem long_first_suffix {m B : ℕ} (hB : 2048 ≤ B) (hBm : B ≤ m) {c σ : ℝ}
    (hc : 0 ≤ c) (hcm : c*m ≤ 1) (hσ : 0<σ) (hV : suffixVariance c B=σ^2)
    (r : Fin 3) (hr : r.val ≤ 1) (k : ℤ) :
    σ^(r.val+1)*|rankDifference r k (freeRankMass c B)| ≤ 1 := by
  let G := momentKernel (1/5) r.val
  let F := bandTerm (13/125) B σ r.val
  have hper := upper_half_suffix_labels hBm hc hcm
  have hB' : (2048:ℝ) ≤ B := by exact_mod_cast hB
  have hb : 1 ≤ (B:ℝ) := by linarith
  have hu := (suffix_variance_bounds c B (by norm_num : (0:ℝ) ≤ 13/125)
    (fun i hi => ⟨(hper i hi).1,(hper i hi).2.1⟩)).2
  rw [hV] at hu
  have hhi : σ ≤ (B:ℝ)^2 := by
    apply (sq_le_sq₀ hσ.le (sq_nonneg _)).mp
    have H := pow_le_pow_left₀ (by positivity : 0 ≤ (B:ℝ)+1) (by linarith only [hb] : (B:ℝ)+1 ≤ 2*B) 3
    nlinarith only [hu,H,pow_le_pow_right₀ hb (by norm_num : 3 ≤ 4),pow_nonneg (Nat.cast_nonneg (α:=ℝ) B) 3]
  have hG := momentKernel_integrable (b:=1/5) (by norm_num) r.val
  have hF := band_term_integrable (13/125) (B:ℝ) σ r.val
  have H := free_difference_of_envelope c B hσ r (hG.add hF) (fun x => ?_) k
  · apply H.trans
    change (∫ x, momentKernel (1/5) r.val x+bandTerm (13/125) B σ r.val x)/(2*π) ≤ 1
    rw [integral_add hG hF,add_div,band_term_integral _ _ hσ]
    rw [show 2*π*σ*(π*σ)^r.val*exp (-(13/125*B/2))/(2*π)=σ*(π*σ)^r.val*exp (-(13/125*B/2)) by field_simp]
    have a := low_moment_five r hr
    have b := upper_half_band_budget hB' hσ.le hhi r.val (by omega)
    have g : (∫ x, momentKernel (1/5) r.val x)/(2*π) ≤ 5/6 :=
      (div_le_div_of_nonneg_right a (by positivity)).trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith only [pi_gt_three]))
    linarith only [g,b]
  let θ := x/σ
  have h₀ : 0 ≤ G x := by dsimp only [G,momentKernel]; positivity
  have h₁ : 0 ≤ F x := by dsimp only [F,bandTerm]; apply indicator_nonneg; intro _ _; positivity
  change ‖bandTransform c B θ‖*|x|^r.val ≤ G x+F x
  by_cases hbθ : θ ∈ Ioc (-π) π
  · have hpos : ‖bandTransform c B θ‖=‖suffixTransform c |θ| B‖ := by
      rw [bandTransform,indicator_of_mem hbθ]
      rcases le_total 0 θ with hz|hz
      · rw [abs_of_nonneg hz]
      · rw [abs_of_nonpos hz,suffix_norm_even]
    rw [hpos]
    have hv : suffixVariance c B*|θ|^2=x^2 := by rw [sq_abs,hV]; dsimp only [θ]; field_simp
    by_cases hcut : B*|θ| ≤ π
    · have H := (suffix_middle_arcs c (abs_nonneg θ) B).2 hcut
      rw [mul_assoc,hv] at H
      have hπ : (1/5:ℝ) ≤ 2/π^2 := (le_div_iff₀ (by positivity)).mpr (by
        nlinarith only [pow_le_pow_left₀ pi_pos.le pi_lt_d2.le 2])
      have HH : ‖suffixTransform c |θ| B‖ ≤ exp (-(1/5)*x^2) :=
        H.trans (exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_right hπ (sq_nonneg x)]))
      dsimp only [G,momentKernel]; linarith only [mul_le_mul_of_nonneg_right HH (pow_nonneg (abs_nonneg x) r.val),h₁]
    · have hπ : |θ| ≤ π := abs_le.mpr ⟨hbθ.1.le,hbθ.2⟩
      have HH := (suffix_outer_arcs c (abs_nonneg θ) hπ B (p:=13/125) (by norm_num) (fun i hi => (hper i hi).1)).1 (le_of_not_ge hcut)
      have hx : x ∈ Ioc (-π*σ) (π*σ) := ⟨(lt_div_iff₀ hσ).mp hbθ.1,(div_le_iff₀ hσ).mp hbθ.2⟩
      have hpow := pow_le_pow_left₀ (abs_nonneg x) (abs_le.mpr (show -(π*σ) ≤ x ∧ x ≤ π*σ by
        exact ⟨by linarith only [hx.1],hx.2⟩)) r.val
      dsimp only [F,bandTerm]; rw [indicator_of_mem hx]
      linarith only [mul_le_mul HH hpow (pow_nonneg (abs_nonneg x) r.val) (exp_pos _).le,h₀]
  · rw [bandTransform,indicator_of_notMem hbθ,norm_zero,zero_mul]; exact add_nonneg h₀ h₁

theorem upper_half_first_suffix {m B : ℕ} (hm : 4096 ≤ m) (hB : 255 ≤ B) (hBm : B ≤ m)
    {c σ : ℝ} (hc : 0 ≤ c) (hcm : c*m ≤ 1) (hσ : 0<σ) (hV : suffixVariance c B=σ^2)
    (r : Fin 3) (hr : r.val ≤ 1) (k : ℤ) :
    σ^(r.val+1)*|rankDifference r k (freeRankMass c B)| ≤ 1 := by
  by_cases h : 2048 ≤ B
  · exact long_first_suffix h hBm hc hcm hσ hV r hr k
  · have hp := upper_half_suffix_labels hBm hc hcm
    have H := short_free_differences hB hσ hV (fun i hi => ⟨(hp i hi).2.2.1 (by omega),(hp i hi).2.1⟩) r k
    have HH := (le_div_iff₀ (pow_pos hσ _)).mp H
    rw [mul_comm] at HH
    exact HH.trans (by fin_cases r <;> norm_num [shortSuffixLimit])

end CentralUnimodality.MarkedExcursion
