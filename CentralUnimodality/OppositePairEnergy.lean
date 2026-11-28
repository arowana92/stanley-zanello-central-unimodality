module

public import CentralUnimodality.OppositeRankPairs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! A frequency bin gives a lower bound on each of the two energies.
The cubic expression retains the exact sum of the squared odd spacings. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

private theorem odd_squares (l : ℕ) :
    (∑ i ∈ Finset.range l, (2*(i:ℝ)+1)^2) = (2*l:ℝ)*((2*l:ℝ)^2-1)/6 := by
  induction l with
  | zero => norm_num
  | succ l ih => rw [Finset.sum_range_succ,ih]; push_cast; ring

private theorem sin_square_lower {x U : ℝ} (hx : 0≤x) (hU : x≤U) :
    x^2*(max 0 (1-U^2/6))^2 ≤ sin x^2 := by
  rcases le_total (1-U^2/6) 0 with h|h
  · rw [max_eq_left h]; simpa using sq_nonneg (sin x)
  rw [max_eq_right h]
  have h₂ := pow_le_pow_left₀ hx hU 2
  have hs : x*(1-U^2/6) ≤ sin x := by
    have H := mul_le_mul_of_nonneg_left (show 1-U^2/6≤1-x^2/6 by linarith only [h₂]) hx
    linarith only [H,sin_ge_sub_cube hx]
  simpa only [mul_pow] using pow_le_pow_left₀ (mul_nonneg hx h) hs 2

theorem opposite_energy_lower {θ U : ℝ} (l : ℕ) (hθ : 0≤θ) (hU : (l:ℝ)*θ≤U) :
    (2*l:ℝ)*((2*l:ℝ)^2-1)*θ^2*(max 0 (1-U^2/6))^2/120 ≤ oppositeEnergy l θ := by
  let A := (max 0 (1-U^2/6))^2
  have h (i : ℕ) (hi : i∈Finset.range l) :
      (2*(i:ℝ)+1)^2*(θ^2*A/4) ≤ sin ((2*(i:ℝ)+1)*θ/2)^2 := by
    have hi' : (i:ℝ)+1≤l := by exact_mod_cast Finset.mem_range.mp hi
    have hu : (2*(i:ℝ)+1)*θ/2≤U := by
      have H := mul_le_mul_of_nonneg_right hi' hθ
      linarith only [H,hU,hθ]
    exact (by convert sin_square_lower (by positivity : 0≤(2*(i:ℝ)+1)*θ/2) hu using 1; dsimp [A]; ring)
  have H := Finset.sum_le_sum h
  rw [← Finset.sum_mul,odd_squares] at H
  unfold oppositeEnergy
  apply le_trans _ (mul_le_mul_of_nonneg_left H (by norm_num : (0:ℝ)≤1/5))
  dsimp only [A]; apply le_of_eq; ring

/-- The true scaled frequency is at least v. The bin supplies an upper
half-angle U, a lower block fraction W and an upper bound ε on 1/m. -/
theorem scaled_opposite_energy {θ U W ε v : ℝ} {l m : ℕ}
    (hm : 0<m) (hθ : 0≤θ) (hU : (l:ℝ)*θ≤U) (hW : 0≤W)
    (hblock : W*m ≤ 2*l) (hε : 1≤ε*m) (hv : 0≤v) (hv' : v≤m*√m*θ) :
    v^2*(W^3-W*ε^2)*(max 0 (1-U^2/6))^2/120 ≤ oppositeEnergy l θ := by
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  by_cases hp : 0≤W^3-W*ε^2
  · have hε₀ : 0≤ε*m := by linarith only [hε]
    have he := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hε 2
    have hb₀ : 0≤W*m := mul_nonneg hW hm'.le
    have hcmp : (m:ℝ)^3*(W^3-W*ε^2) ≤ (2*l:ℝ)*((2*l:ℝ)^2-1) := by
      by_cases hh : 1≤W*m
      · have h₂ := pow_le_pow_left₀ hb₀ hblock 2
        have H := mul_le_mul hblock (show (W*m)^2-1 ≤ (2*l:ℝ)^2-1 by linarith only [h₂])
          (by nlinarith only [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hh 2])
          (by positivity : (0:ℝ)≤2*l)
        nlinarith only [H,mul_le_mul_of_nonneg_left he hb₀]
      · by_cases hl : l=0
        · subst l; norm_num at hblock ⊢
          have hw₀ : W=0 := by rcases mul_nonpos_iff.mp hblock with h|h <;> linarith
          simp [hw₀]
        · have hl' : (1:ℝ)≤l := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hl
          have hs := pow_le_pow_left₀ hb₀ (le_of_not_ge hh) 2
          have H := mul_le_mul_of_nonneg_left (hs.trans he) hb₀
          have hl₂ := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) (by linarith : (1:ℝ)≤2*l) 2
          nlinarith only [H,mul_nonneg (by positivity : (0:ℝ)≤2*l) (show 0≤(2*l:ℝ)^2-1 by linarith only [hl₂])]
    have hv₂ := pow_le_pow_left₀ hv hv' 2
    have ht : v^2 ≤ (m:ℝ)^3*θ^2 := by
      rw [mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)] at hv₂
      linarith only [hv₂]
    have H := (mul_le_mul_of_nonneg_right ht hp).trans (by
      convert mul_le_mul_of_nonneg_right hcmp (sq_nonneg θ) using 1; ring)
    apply le_trans _ (opposite_energy_lower l hθ hU)
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_right H (sq_nonneg _)
  · have he : 0≤oppositeEnergy l θ := by unfold oppositeEnergy; positivity
    apply le_trans _ he
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg v) (le_of_not_ge hp)) (sq_nonneg _)) (by norm_num)

end CentralUnimodality.MarkedExcursion
