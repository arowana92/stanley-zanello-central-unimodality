module

public import CentralUnimodality.TiltedPairRates
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! At frequencies at most one eighth, space paired labels by the ceiling
of four times the inverse two-thirds power. The contraction is uniform in
the frequency while the block length accounts for the two-thirds power. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

noncomputable def innerSpacing (t : ℝ) := ⌈4/(t^(1/3:ℝ))^2⌉₊

private theorem inner_loss (wide : Bool) :
    let r : ℚ := if wide then 41/100 else 14/25
    (1+exp (-(pairWeight wide:ℝ)*(52/5)))/2 ≤ exp (-(r:ℝ)) := by
  let x := pairWeight wide*(52/5)
  let y : ℚ := if wide then 41/100 else 14/25
  have h : (1+upperNegExp x)/2 ≤ (1-y/128)^128 ∧ y ≤ 128 ∧ 0 ≤ x := by
    cases wide <;> decide +kernel
  have H : (1+(upperNegExp x:ℝ))/2 ≤ (1-(y:ℝ)/128)^128 := by exact_mod_cast h.1
  apply le_trans _ (H.trans (rate_lower_exp y (by exact_mod_cast h.2.1)))
  have hu := upperNegExp_sound h.2.2
  dsimp only [x] at hu
  push_cast at hu
  dsimp only [x]
  rw [neg_mul]
  linarith only [hu]

/-- At the chosen spacing the half-angle is at most 17/16 and the energy
l sin²(lθ/2) is at least 10.4. Constants include the rounding of the spacing. -/
theorem inner_spacing_energy {t : ℝ} (ht : 0<t) (ht' : t ≤ 1/8) :
    1 ≤ innerSpacing t ∧ (innerSpacing t:ℝ)*t^(2/3:ℝ) ≤ 17/4 ∧
      52/5 ≤ (innerSpacing t:ℝ)*sin (innerSpacing t*t/2)^2 := by
  let q := t^(1/3:ℝ)
  let l := innerSpacing t
  have hq : 0<q := rpow_pos_of_pos ht _
  have hq3 : q^3=t := by
    rw [← rpow_natCast,← rpow_mul ht.le]; norm_num
  have hq2 : q^2=t^(2/3:ℝ) := by
    rw [← rpow_natCast,← rpow_mul ht.le]; norm_num
  have hhalf : q ≤ 1/2 := by
    by_contra! hh
    have h := pow_lt_pow_left₀ hh (by norm_num) (by decide : 3 ≠ 0)
    rw [hq3] at h; linarith
  have lower : 4/q^2 ≤ (l:ℝ) := Nat.le_ceil _
  have upper : (l:ℝ) < 4/q^2+1 := Nat.ceil_lt_add_one (by positivity)
  have hl : 0 < (l:ℝ) := lt_of_lt_of_le (by positivity) lower
  have hlo := (div_le_iff₀ (sq_pos_of_pos hq)).mp lower
  have hqsmall := pow_le_pow_left₀ hq.le hhalf 2
  have hhi : (l:ℝ)*q^2 ≤ 17/4 := by
    have h := mul_lt_mul_of_pos_right upper (sq_pos_of_pos hq)
    rw [add_mul,div_mul_cancel₀ _ (sq_pos_of_pos hq).ne',one_mul] at h
    linarith
  let x := (l:ℝ)*t/2
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxhi : x ≤ 17/16 := by
    have hh := mul_le_mul hhi hhalf hq.le (by norm_num)
    dsimp [x]; rw [← hq3]; linarith only [hh]
  have hxsq := pow_le_pow_left₀ hx hxhi 2
  have hsin : (81/100)*x ≤ sin x := by
    have hsmall : (81/100:ℝ) ≤ 1-x^2/6 := by linarith only [hxsq]
    linarith only [mul_le_mul_of_nonneg_right hsmall hx,sin_ge_sub_cube hx]
  have hs : (13/20)*x^2 ≤ sin x^2 := by
    have H := pow_le_pow_left₀ (mul_nonneg (by norm_num) hx) hsin 2
    nlinarith only [H,sq_nonneg x]
  have HE := mul_le_mul_of_nonneg_left hs hl.le
  have H3 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4) hlo 3
  refine ⟨by exact_mod_cast hl,by rw [← hq2]; exact hhi,?_⟩
  change 52/5 ≤ (l:ℝ)*sin x^2
  apply le_trans _ HE
  dsimp [x]; rw [← hq3]; nlinarith only [H3]

theorem inner_pair_contraction {t : ℝ} (ht : 0<t) (ht' : t ≤ 1/8) (wide : Bool) :
    let l := innerSpacing t
    (1+exp (-(pairWeight wide:ℝ)*l*sin (l*t/2)^2))/2 ≤
      exp (-(if wide then 41/100 else 14/25 : ℝ)) := by
  have hw : 0 ≤ (pairWeight wide:ℝ) := by cases wide <;> norm_num [pairWeight]
  have he := mul_le_mul_of_nonneg_left (inner_spacing_energy ht ht').2.2 hw
  have h := exp_le_exp.mpr (show -(pairWeight wide:ℝ)*innerSpacing t*sin (innerSpacing t*t/2)^2 ≤
      -(pairWeight wide:ℝ)*(52/5) by linarith only [he])
  have H := inner_loss wide
  have h' := (div_le_div_of_nonneg_right (add_le_add (le_refl 1) h) (by norm_num : (0:ℝ) ≤ 2)).trans H
  cases wide <;> simpa using h'

end CentralUnimodality.MarkedExcursion
