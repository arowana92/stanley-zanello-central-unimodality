module

public import CentralUnimodality.BridgeProduct
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Real logarithmic error bounds in the elementary free and bridge
products. They apply uniformly whenever the individual angles are at
most one in absolute value. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit
open Real

private theorem log_loss {t v : ℝ} (ht : 0<t) (hs : (1-t)^2≤t*v) :
    t-1-v ≤ log t := by
  apply le_trans _ (one_sub_inv_le_log_of_pos ht)
  apply (mul_le_mul_iff_of_pos_left ht).mp
  rw [mul_sub t 1 t⁻¹,mul_one,mul_inv_cancel₀ ht.ne']
  nlinarith only [hs]

theorem log_cos_quadratic {x : ℝ} (hx : |x|≤1) :
    |log (cos x)+x^2/2| ≤ 3/4*x^4 := by
  have H := abs_le.mp (cos_bound hx)
  rw [show |x|^4=x^4 by rw [← abs_pow,abs_of_nonneg (by positivity : 0≤x^4)]] at H
  have x₂ : x^2≤1 := by simpa using (sq_le_sq₀ (abs_nonneg x) zero_le_one).mpr hx
  have x₄ : x^4≤x^2 := by nlinarith only [mul_le_mul_of_nonneg_right x₂ (sq_nonneg x)]
  have ht : (43/96:ℝ)≤cos x := by linarith only [H.1,x₂,x₄]
  have v : 1-cos x≤(53/96)*x^2 := by linarith only [H.1,x₄]
  have sqv := (sq_le_sq₀ (sub_nonneg.mpr (cos_le_one x)) (by positivity)).mpr v
  have lower := log_loss (v:=(69/100)*x^4) (cos_pos_of_le_one hx) (by
    nlinarith only [sqv,mul_le_mul_of_nonneg_right ht (by positivity : 0≤(69/100)*x^4),
      show 0≤x^4 by positivity])
  rw [abs_le]
  constructor <;> nlinarith only [lower,H.1,H.2,log_le_sub_one_of_pos (cos_pos_of_le_one hx),
    show 0≤x^4 by positivity]

private theorem sinc_quadratic {x : ℝ} (hx : |x|≤1) :
    |sinc x-(1-x^2/6)|≤x^4/100 := by
  by_cases hz : x=0
  · simp [hz]
  apply (mul_le_mul_iff_of_pos_right (abs_pos.mpr hz)).mp
  rw [← abs_mul,sinc_of_ne_zero hz,sub_mul,div_mul_cancel₀ _ hz]
  have H := sin_bound hx
  rw [show (1-x^2/6)*x=x-x^3/6 by ring]
  apply H.trans_eq
  rw [show |x|^5=|x|^4*|x| by ring,← abs_pow,abs_of_nonneg (by positivity : 0≤x^4)]
  ring

theorem log_sinc_quadratic {x : ℝ} (hx : |x|≤1) :
    |log (sinc x)+x^2/6| ≤ x^4/20 := by
  have H := abs_le.mp (sinc_quadratic hx)
  have x₂ : x^2≤1 := by simpa using (sq_le_sq₀ (abs_nonneg x) zero_le_one).mpr hx
  have x₄ : x^4≤x^2 := by nlinarith only [mul_le_mul_of_nonneg_right x₂ (sq_nonneg x)]
  have ht : 82/100≤sinc x := by linarith only [H.1,x₂,x₄]
  have pos : 0<sinc x := by linarith
  have v : 1-sinc x≤(18/100)*x^2 := by linarith only [H.1,x₄,sq_nonneg x]
  have sqv := (sq_le_sq₀ (sub_nonneg.mpr (sinc_le_one x)) (by positivity)).mpr v
  have lower := log_loss (v:=(4/100)*x^4) pos (by
    nlinarith only [sqv,mul_le_mul_of_nonneg_right ht (by positivity : 0≤(4/100)*x^4),
      show 0≤x^4 by positivity])
  rw [abs_le]
  constructor <;> linarith only [lower,H.1,H.2,log_le_sub_one_of_pos pos,show 0≤x^4 by positivity]

end CentralUnimodality.ReturnSplit
