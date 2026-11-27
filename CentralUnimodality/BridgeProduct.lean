module

public import CentralUnimodality.EndpointTransforms
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! The signed-area bridge input at successive even lengths. Cross multiplying
the sine factor gives an identity at every real frequency, including zeros. -/
@[expose] public section

namespace CentralUnimodality

private theorem eliminateEndpoint {U B P a b c u v : ℂ}
    (h₁ : U = a*B+b*P) (h₂ : U = c*(B+P)) (hp : u*b = v*c) :
    (u-v)*U = u*(a-b)*B := by
  linear_combination u*h₁-v*h₂+(B+P)*hp

private theorem bridge_step_char (ω : ℝ) (j : ℕ) :
    let χ := areaCharacter ω
    let u := χ (j+1)
    let v := χ (-(j+1:ℤ))
    let a := χ (2*j+1)
    let b := χ (-(2*j+1:ℤ))
    (u-v)*endpointTransform ω (2*j+2) 0 = (u+v)*(a-b)*endpointTransform ω (2*j) 0 := by
  dsimp only
  let χ := areaCharacter ω
  have phase (x y x' y' : ℤ) (h : x+y=x'+y') : χ x*χ y = χ x'*χ y' := by
    simpa only [χ,← areaCharacter_add] using congrArg χ h
  have pp := endpoint_prepend ω (2*j) 1
  have ap := endpoint_append ω (2*j) 1
  have pm := endpoint_prepend ω (2*j) (-1)
  have am := endpoint_append ω (2*j) (-1)
  norm_num only [Nat.cast_mul,Nat.cast_ofNat,Int.reduceAdd,Int.reduceSub] at pp ap pm am
  have plus := eliminateEndpoint pp ap (phase (j+1) (-(2*j+1)) (-(j+1)) 1 (by omega))
  rw [add_comm (areaCharacter _ _ * _) (areaCharacter _ _ * _)] at pm
  rw [add_comm (endpointTransform _ _ _)] at am
  have minus := eliminateEndpoint pm am (phase (-(j+1)) (2*j+1) (j+1) (-1) (by omega))
  have hb := endpoint_append ω (2*j+1) 0
  simp only [areaCharacter_zero,one_mul,zero_sub,zero_add] at hb
  rw [hb]
  dsimp only [χ] at plus minus
  linear_combination plus-minus

private theorem char_diff (ω : ℝ) (k : ℤ) :
    areaCharacter ω k - areaCharacter ω (-k) = 2*Complex.I*(Real.sin (ω*k):ℂ) := by
  rw [Complex.ofReal_sin,Complex.sin]
  simp only [areaCharacter,Int.cast_neg,mul_neg,Complex.ofReal_neg,neg_mul]
  ring_nf
  simp [Complex.I_sq,sub_eq_add_neg]

/-- With fair normalization the ratio is cos((j+1)ω)/2 times
sin((2j+1)ω)/sin((j+1)ω) whenever the denominator is nonzero. -/
theorem fair_bridge_sine_step (ω : ℝ) (j : ℕ) :
    2*(Real.sin (ω*(j+1)):ℂ)*PowerSeries.coeff (2*j+2) (fairSeries (areaCharacter ω) bridges) =
      (Real.cos (ω*(j+1)):ℂ)*(Real.sin (ω*(2*j+1)):ℂ)*
        PowerSeries.coeff (2*j) (fairSeries (areaCharacter ω) bridges) := by
  have h := bridge_step_char ω j
  dsimp only at h
  rw [char_diff,char_diff,areaCharacter_pair] at h
  simp only [Int.cast_add,Int.cast_one,Int.cast_natCast,Int.cast_mul,Int.cast_ofNat] at h
  rw [fair_bridge_endpoint,fair_bridge_endpoint,pow_add]
  apply mul_left_cancel₀ (a := Complex.I) Complex.I_ne_zero
  linear_combination (2:ℂ)⁻¹^(2*j)/4 * h

private theorem sin_as_sinc (x : ℝ) : Real.sin x = x*Real.sinc x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero hx]
    field_simp

/-- This is the input recurrence used on the positive grid frequencies before
truncation. Only the sinc at the new index occurs in a denominator. -/
theorem fair_bridge_sinc_step (ω : ℝ) (j : ℕ) (hω : ω ≠ 0) (hs : Real.sinc (ω*(j+1)) ≠ 0) :
    PowerSeries.coeff (2*j+2) (fairSeries (areaCharacter ω) bridges) =
      PowerSeries.coeff (2*j) (fairSeries (areaCharacter ω) bridges) *
        ((Real.cos (ω*(j+1))/2*(Real.cos (ω*j) +
          Real.cos (ω*(j+1))*((j:ℝ)/(j+1))*(Real.sinc (ω*j)/Real.sinc (ω*(j+1)))) : ℝ):ℂ) := by
  let a := ω*(j:ℝ)
  let b := ω*(j+1)
  have hj : (j:ℝ)+1 ≠ 0 := by positivity
  have hb : b ≠ 0 := mul_ne_zero hω hj
  have hsin : Real.sin b ≠ 0 := by rw [sin_as_sinc]; exact mul_ne_zero hb hs
  have hratio : Real.sin (ω*(2*j+1)) = Real.sin b*(Real.cos a +
      Real.cos b*((j:ℝ)/(j+1))*(Real.sinc a/Real.sinc b)) := by
    rw [show ω*(2*j+1) = b+a by dsimp [a,b]; ring,Real.sin_add,sin_as_sinc a,sin_as_sinc b]
    field_simp [show Real.sinc b ≠ 0 from hs,hj]
    dsimp [a,b]
    ring
  have h := fair_bridge_sine_step ω j
  rw [hratio] at h
  change _ = _ * ((Real.cos b/2*(Real.cos a + Real.cos b*((j:ℝ)/(j+1))*(Real.sinc a/Real.sinc b)) : ℝ):ℂ)
  apply mul_left_cancel₀ (a := 2*(Real.sin b:ℂ)) (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hsin))
  simp only [Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_ofNat] at h ⊢
  change 2*(Real.sin b:ℂ)*_ = _ at h
  linear_combination h

end CentralUnimodality
