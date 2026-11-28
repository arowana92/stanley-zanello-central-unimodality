module

public import CentralUnimodality.RankLossBins
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Uniform standard deviations of the original and first-hit suffix
rank laws in the dimensionless time bins. All scales refer to the exact
variance of the independent labeled word. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

/-- Lower and upper scale bounds for any suffix between αm and βm labels.
The lower drift bound uses only the surviving range of labels. -/
theorem bin_suffix_scale {m B : ℕ} (hM : 4096 ≤ m) {c C α β : ℝ} (hc : 0 ≤ c)
    (hC : 2*c*((m:ℝ)*√m) ≤ C) (ha : 0 ≤ α) (hb : 0 ≤ β)
    (hlo : α*m ≤ B) (hhi : (B:ℝ) ≤ β*m) (hcap : C*β ≤ 128) :
    let s := (m:ℝ)*√m
    s*√((1-(C*β/128)^2)*α^3/12) ≤ √(suffixVariance c B) ∧
      √(suffixVariance c B) ≤ s*√((β+1/4096)^3/12) := by
  let M := (m:ℝ)
  let s := M*√M
  let cap := C*β/128
  have hM' : 4096 ≤ M := by dsimp [M]; exact_mod_cast hM
  have hMpos : 0<M := by linarith
  have hr : 64 ≤ √M := (le_sqrt (by norm_num) hMpos.le).mpr (by linarith)
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hs2 : s^2=M^3 := by dsimp [s]; rw [mul_pow,sq_sqrt hMpos.le]; ring
  have hCM : c*M ≤ C/128 := by
    have h := mul_le_mul_of_nonneg_left hr (mul_nonneg hc hMpos.le)
    change 2*c*(M*√M) ≤ C at hC
    linarith only [h,hC]
  have hCpos : 0 ≤ C := (by positivity : 0 ≤ 2*c*((m:ℝ)*√m)) |>.trans hC
  have hnon : 0 ≤ cap := by dsimp [cap]; positivity
  have hcap' : cap ≤ 1 := by dsimp [cap]; linarith only [hcap]
  have hpos : 0 ≤ 1-cap^2 := by nlinarith only [pow_le_pow_left₀ hnon hcap' 2]
  have H := suffix_variance_bounds c B (div_nonneg hpos (by norm_num : (0:ℝ) ≤ 4)) (by
    intro i hi
    let x := c*((i:ℝ)+1)
    have hx : 0 ≤ x := by dsimp [x]; positivity
    have hi' : (i:ℝ)+1 ≤ B := by exact_mod_cast (Finset.mem_range.mp hi)
    have hbound : x ≤ cap := by
      have h := mul_le_mul_of_nonneg_left (hi'.trans hhi) hc
      have hh := mul_le_mul_of_nonneg_right hCM hb
      dsimp [x,cap,M] at *; linarith only [h,hh]
    have hd : 0 ≤ tanh x := by rw [tanh_eq_sinh_div_cosh]; exact div_nonneg (sinh_nonneg_iff.mpr hx) (cosh_pos _).le
    have he := pow_le_pow_left₀ hd ((tanh_le_linear hx).trans hbound) 2
    have hp : upChance (-x)=(1-tanh x)/2 := by linarith only [up_total x,up_drift x]
    have hp' : upChance x=(1+tanh x)/2 := by linarith only [up_total x,up_drift x]
    change _ ≤ upChance (-x)*upChance x ∧ upChance (-x)*upChance x ≤ _
    rw [hp,hp']; constructor <;> nlinarith only [he,sq_nonneg (tanh x)])
  have hvar : 0 ≤ suffixVariance c B := (by positivity : 0 ≤ (1-cap^2)/4/3*(B:ℝ)^3).trans H.1
  have hα : 0 ≤ (1-cap^2)*α^3/12 := by positivity
  have hβ : 0 ≤ (β+1/4096)^3/12 := by positivity
  constructor
  · apply (sq_le_sq₀ (mul_nonneg hs (sqrt_nonneg _)) (sqrt_nonneg _)).mp
    change (s*√((1-cap^2)*α^3/12))^2 ≤ _
    rw [mul_pow,hs2,sq_sqrt hα,sq_sqrt hvar]
    have h := pow_le_pow_left₀ (mul_nonneg ha hMpos.le) hlo 3
    have hh := mul_le_mul_of_nonneg_left h hpos
    dsimp only [M] at *; linarith only [hh,H.1]
  · apply (sq_le_sq₀ (sqrt_nonneg _) (mul_nonneg hs (sqrt_nonneg _))).mp
    change _ ≤ (s*√((β+1/4096)^3/12))^2
    rw [mul_pow,hs2,sq_sqrt hβ,sq_sqrt hvar]
    have h : (B:ℝ)+1 ≤ (β+1/4096)*M := by dsimp only [M] at *; linarith only [hhi,hM']
    have H' := pow_le_pow_left₀ (by positivity) h 3
    linarith only [H.2,H']

end CentralUnimodality.MarkedExcursion
