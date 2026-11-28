module

public import CentralUnimodality.RankBinScales
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! The original prefix normalizer and variance allowance in a saddle
bin. The probability and standard deviation are those of the actual law. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

theorem bin_prefix_survival {m L : ℕ} (hm : 4096 ≤ m) {c g G f : ℝ} (hc : 0<c)
    (hg : 0 ≤ g) (hlo : g ≤ 2*c*((m:ℝ)*√m)) (hhi : 2*c*((m:ℝ)*√m) ≤ G)
    (hf : 0 ≤ f) (hf' : f<1) (hL : (L:ℝ) ≤ f*m) :
    let d := tanh (c*m)
    let κ := g/2*(1-g^2/(12*4096))
    let P := live c (c*m) L 1
    d ≤ G/128 ∧ κ ≤ √m*d ∧ 2*κ*(1-f)/(1+G/128) ≤ P*√m ∧ 0<P := by
  let u := c*m
  let d := tanh u
  let κ := g/2*(1-g^2/(12*4096))
  let P := live c u L 1
  have hm' : (4096:ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0<(m:ℝ) := by linarith
  have hr : (64:ℝ) ≤ √m := (le_sqrt (by norm_num) hp.le).mpr (by linarith)
  have hu : 0<u := mul_pos hc hp
  have hd : 0<d := by dsimp [d]; rw [tanh_eq_sinh_div_cosh]; exact div_pos (sinh_pos_iff.mpr hu) (cosh_pos _)
  have hdu : d ≤ G/128 := by
    have h := mul_le_mul_of_nonneg_left hr hu.le
    dsimp [u] at h
    linarith only [h,hhi,tanh_le_linear hu.le]
  have hk : κ ≤ √m*d := bin_drift_lower hm hg hlo
  have hpars (i : ℕ) (hi : i<L) : (1-f)*u ≤ u-c*i := by
    have hil : (i:ℝ) ≤ L := by exact_mod_cast hi.le
    dsimp [u]; linarith only [mul_le_mul_of_nonneg_left (hil.trans hL) hc.le]
  have hlive := live_lower c u ((1-f)*u) L 1 hpars
  rw [pow_one] at hlive
  have hden : 2*(1-f)*d ≤ (1+d)*P :=
    (drift_cost hu hf hf').1.trans (mul_le_mul_of_nonneg_left hlive (by positivity))
  have hP : 0<P := pos_of_mul_pos_right ((by positivity : 0<2*(1-f)*d).trans_le hden) (by positivity)
  refine ⟨hdu,hk,?_,hP⟩
  have htop := (mul_le_mul_of_nonneg_right (add_le_add (le_refl 1) hdu) hP.le)
  have h := mul_le_mul_of_nonneg_right (hden.trans htop) (sqrt_nonneg (m:ℝ))
  apply (div_le_iff₀ (by linarith only [hd,hdu] : 0<1+G/128)).mpr
  change 2*κ*(1-f) ≤ P*√m*(1+G/128)
  nlinarith only [h,mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hf'.le)]

/-- Substitute the lower scaled deviation and drift and the upper drift
in (2). No loss is taken in the rank normalization. -/
theorem bin_prefix_variance {m : ℕ} {c f σ z κ U : ℝ} (hm : 0<(m:ℝ)) (hf : 0 ≤ f)
    (hf' : f<1) (hz : 0<z) (hκ : 0<κ) (hd : 0<tanh (c*m)) (hd' : tanh (c*m) ≤ U)
    (hσ : (m:ℝ)*√m*z ≤ σ) (hlo : κ ≤ √m*tanh (c*m)) :
    varianceLimit m c f σ ≤ (f+(1+U)/(1-f)*(f^2+1/(2*κ^2)))/(4*z^2) := by
  let d := tanh (c*m)
  have hr : 0<√(m:ℝ) := sqrt_pos.mpr hm
  have hσp : 0<σ := lt_of_lt_of_le (by positivity) hσ
  have hκsq := pow_le_pow_left₀ hκ.le hlo 2
  rw [mul_pow,sq_sqrt hm.le] at hκsq
  have hσsq := pow_le_pow_left₀ (by positivity) hσ 2
  rw [mul_pow,mul_pow,sq_sqrt hm.le] at hσsq
  have hweight : (m:ℝ)^3/(4*σ^2) ≤ 1/(4*z^2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    linarith only [hσsq]
  have hterm : 1/(2*(m:ℝ)*d^2) ≤ 1/(2*κ^2) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    dsimp [d]; linarith only [hκsq]
  have hfac : (1+d)/(1-f) ≤ (1+U)/(1-f) := div_le_div_of_nonneg_right (by linarith only [hd']) (by linarith)
  have hprod := mul_le_mul hfac (add_le_add (le_refl (f^2)) hterm)
    (by dsimp [d]; positivity) (by apply div_nonneg _ (by linarith); linarith only [hd,hd'])
  have H := mul_le_mul hweight (add_le_add (le_refl f) hprod) (by dsimp [d]; positivity) (by positivity)
  unfold varianceLimit
  simpa only [div_eq_mul_inv,one_mul,mul_comm] using H

end CentralUnimodality.MarkedExcursion
