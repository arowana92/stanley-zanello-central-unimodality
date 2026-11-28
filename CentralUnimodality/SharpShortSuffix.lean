module

public import CentralUnimodality.ShortSuffixRanks
import Mathlib.Analysis.Real.Pi.Bounds

/-! Outside the central frequency band, a bound for the second moment
gains a factor of at least 4 for each power of frequency removed. This
sharpens the mass and first-difference bounds for every short suffix. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real MeasureTheory Set

noncomputable def shortTail (B x : ℝ) :=
  16/250*laplaceShoulders 4 x + 64/100000*laplaceShoulders 8 x +
    frequencyBox (32*B/15) (exp (-(49/500)*B)) 2 x + frequencyBox (4*B^2) (exp (-(147/800)*B)) 2 x

private theorem tail_nonneg (B x : ℝ) : 0≤shortTail B x := by
  have H (T C : ℝ) (hC : 0≤C) : 0≤frequencyBox T C 2 x :=
    indicator_nonneg (fun _ _ => mul_nonneg (sq_nonneg T) hC) x
  dsimp only [shortTail]
  have h₁ := (laplaceShoulders_pos 4 x).le
  have h₂ := (laplaceShoulders_pos 8 x).le
  linarith only [h₁,h₂,H (32*B/15) _ (exp_pos (-(49/500)*B)).le,H (4*B^2) _ (exp_pos (-(147/800)*B)).le]

private theorem tail_integral {B : ℝ} (hB : 255≤B) :
    Integrable (shortTail B) ∧ (∫ x, shortTail B x)≤146/1000 := by
  have box {T : ℝ} (hT : 0≤T) (C : ℝ) : Integrable (frequencyBox T C 2) ∧
      (∫ x, frequencyBox T C 2 x)=2*T^3*C := by
    unfold frequencyBox; constructor
    · rw [integrable_indicator_iff measurableSet_Icc]
      exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    · rw [integral_indicator_const _ measurableSet_Icc,Real.volume_real_Icc_of_le (by linarith),smul_eq_mul]; ring
  obtain ⟨t₁,e₁⟩ := laplaceShoulders_integral 4
  obtain ⟨t₂,e₂⟩ := laplaceShoulders_integral 8
  obtain ⟨t₃,e₃⟩ := box (by linarith only [hB] : 0≤32*B/15) (exp (-(49/500)*B))
  obtain ⟨t₄,e₄⟩ := box (by positivity : 0≤4*B^2) (exp (-(147/800)*B))
  have h₁ := t₁.const_mul (16/250)
  have h₂ := t₂.const_mul (64/100000)
  refine ⟨(((h₁.add h₂).add t₃).add t₄),?_⟩
  unfold shortTail
  rw [integral_add (f:=fun x => _+_+_) ((h₁.add h₂).add t₃) t₄,
    integral_add (f:=fun x => _+_) (h₁.add h₂) t₃,integral_add h₁ h₂,integral_const_mul,integral_const_mul,e₁,e₂,e₃,e₄]
  obtain ⟨H,K⟩ := short_outer_budgets hB 2 le_rfl
  linarith only [H,K]

noncomputable def shortMajorant (B : ℝ) (r : ℕ) (x : ℝ) :=
  momentKernel (9/20) r x+(1/(4:ℝ)^(2-r))*shortTail B x

private theorem majorant_bound (c : ℝ) {B : ℕ} (hB : 255≤B) {σ : ℝ} (hσ : 0<σ) (hV : suffixVariance c B=σ^2)
    (hp : ∀ i∈Finset.range B, 49/250≤labelVariance c (i+1) ∧ labelVariance c (i+1)≤1/4) (r : Fin 3) (x : ℝ) :
    ‖bandTransform c B (x/σ)‖*|x|^r.val ≤ shortMajorant B r x := by
  have hN := tail_nonneg B x
  by_cases h : |x|≤4
  · apply le_trans _ (le_add_of_nonneg_right (mul_nonneg (by positivity) hN))
    have hscale := (short_suffix_scale hB hσ hV hp).1
    have hx : (B:ℝ)*|x/σ|≤1 := by
      rw [abs_div,abs_of_pos hσ,← mul_div_assoc,div_le_one hσ]
      linarith only [mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (α:=ℝ) B),hscale]
    by_cases hband : x/σ∈Ioc (-π) π
    · rw [bandTransform,indicator_of_mem hband]
      have H := suffix_inner_modulus c (x/σ) B hx
      rw [hV,div_pow,show 9/20*σ^2*(x^2/σ^2)=9/20*x^2 by field_simp] at H
      rw [momentKernel,mul_comm (|x|^r.val),neg_mul]
      exact mul_le_mul_of_nonneg_right H (pow_nonneg (abs_nonneg x) _)
    · rw [bandTransform,indicator_of_notMem hband,norm_zero,zero_mul]; dsimp [momentKernel]; positivity
  · have H := short_suffix_envelope B hB hσ hV hp 2 le_rfl x
    have he : shortEnvelope B 2 x=momentKernel (9/20) 2 x+shortTail B x := by
      dsimp only [shortEnvelope,shortTail]; ring
    rw [he] at H
    have hpos : 0 < |x| := by linarith only [le_of_not_ge h]
    have hp₄ := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤4) (le_of_not_ge h) (2-r.val)
    have hd : |x|^r.val*|x|^(2-r.val)=|x|^2 := by
      rw [← pow_add,show r.val+(2-r.val)=2 by omega]
    apply le_of_mul_le_mul_right (a:=|x|^(2-r.val)) _ (pow_pos hpos _)
    rw [mul_assoc,hd,shortMajorant,add_mul,momentKernel,
      show |x|^r.val*exp (-(9/20)*x^2)*|x|^(2-r.val)=momentKernel (9/20) 2 x by
        dsimp only [momentKernel]; rw [mul_right_comm,hd]]
    apply H.trans (add_le_add (le_refl _) _)
    have hx := mul_le_mul_of_nonneg_left hp₄ (div_nonneg hN (by positivity : 0≤(4:ℝ)^(2-r.val)))
    field_simp at hx ⊢
    linarith only [hx]

def shortSharpLimit (r : Fin 3) : ℚ := if r=0 then 43/100 else if r=1 then 9/25 else 1/2

theorem sharp_free_differences {c σ : ℝ} {B : ℕ} (hB : 255≤B) (hσ : 0<σ) (hV : suffixVariance c B=σ^2)
    (hp : ∀ i∈Finset.range B, 49/250≤labelVariance c (i+1) ∧ labelVariance c (i+1)≤1/4)
    (r : Fin 3) (j : ℤ) : σ^(r.val+1)*|rankDifference r j (freeRankMass c B)|≤(shortSharpLimit r:ℝ) := by
  have H := tail_integral (by exact_mod_cast hB : (255:ℝ)≤B)
  have h₁ := momentKernel_integrable (b:=9/20) (by norm_num) r.val
  have h₂ := H.1.const_mul (1/(4:ℝ)^(2-r.val))
  apply (free_difference_of_envelope c B hσ r (h₁.add h₂) (majorant_bound c hB hσ hV hp r) j).trans
  apply (div_le_iff₀ (by positivity)).mpr
  simp only [Pi.add_apply]
  rw [integral_add h₁ h₂,integral_const_mul]
  obtain ⟨G₀,G₁,G₂⟩ := inner_gaussian_low_moments
  have HE := mul_le_mul_of_nonneg_left H.2 (by positivity : 0≤1/(4:ℝ)^(2-r.val))
  change absoluteGaussianMoment (9/20) r.val+_≤_
  fin_cases r <;> norm_num [shortSharpLimit] at HE ⊢ <;> linarith only [HE,G₀,G₁,G₂,pi_gt_d2]

end CentralUnimodality.MarkedExcursion
