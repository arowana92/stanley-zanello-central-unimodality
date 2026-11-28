module

public import CentralUnimodality.UpperHalfHitDecay
public import CentralUnimodality.UpperHalfTimeBins

/-! Cancel the length and the survival normalization before comparing
a first-hit contribution with the rational cost of its time interval. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic
open Real

theorem far_hit_scale {M P S B t R E C F W γ g δ X Q : ℝ} (n : ℕ)
    (hM : 0<M) (hP : 0<P) (hS : 0≤S) (hB : 0<B) (hR : 0<R) (hrt : R≤t)
    (hg : 0<g) (hγ : g≤γ) (hδ : 0<δ) (hE : 0≤E) (hF : 0≤F)
    (hpeak : F≤γ*W) (hden : δ*γ≤P*√M) (hdec : E*γ≤g*C) (hratio : (S/B)^n≤Q)
    (H : X≤E*(F^2/(t*(M*√M)))*(1/B^n)) :
    S^n/(P/M)*X ≤ (g/δ)*W^2/R*C*Q := by
  have hγp := hg.trans_le hγ
  have hden' := mul_le_mul hrt hden (mul_pos hδ hγp).le (hR.le.trans hrt)
  have hf := pow_le_pow_left₀ hF hpeak 2
  have hq := div_le_div₀ (sq_nonneg _) hf (mul_pos hR (mul_pos hδ hγp)) hden'
  have heq : (γ*W)^2/(R*(δ*γ))=γ*(W^2/(R*δ)) := by field_simp
  rw [heq] at hq
  have hcost : E*(F^2/(t*(P*√M))) ≤ (g/δ)*W^2/R*C := calc
    _ ≤ E*(γ*(W^2/(R*δ))) := mul_le_mul_of_nonneg_left hq hE
    _ = (E*γ)*(W^2/(R*δ)) := by ring
    _ ≤ (g*C)*(W^2/(R*δ)) := mul_le_mul_of_nonneg_right hdec (by positivity)
    _ = _ := by ring
  have hz : 0 ≤ E*(F^2/(t*(P*√M))) := mul_nonneg hE (div_nonneg (sq_nonneg _)
    (mul_nonneg (hR.le.trans hrt) (mul_nonneg hP.le (sqrt_nonneg _))))
  apply (mul_le_mul_of_nonneg_left H (by positivity : 0≤S^n/(P/M))).trans
  apply le_trans _ (mul_le_mul hcost hratio (pow_nonneg (div_nonneg hS hB.le) _) (hz.trans hcost))
  apply le_of_eq
  rw [div_pow]; field_simp

theorem far_first_width {γ g t R e : ℝ} (hg : 0<g) (hγ : g≤γ) (hR : 0<R) (ht : R≤t) :
    γ*e/2+(4/5)/t ≤ γ*(e/2+(4/5)/(R*g)) := by
  have h₁ := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤4/5) hR ht
  have h₂ := mul_le_mul_of_nonneg_right hγ (by positivity : 0 ≤ (4/5)/(R*g))
  have H : g*((4/5)/(R*g))=(4/5)/R := by field_simp
  rw [H] at h₂
  linarith only [h₁,h₂]

end CentralUnimodality.MarkedExcursion.BinArithmetic
