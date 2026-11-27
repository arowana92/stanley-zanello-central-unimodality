module

public import CentralUnimodality.SineBlock
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-! A rational lower envelope for the sine-square sum throughout a positive
frequency arc. On short arcs it uses the cubic sine minorant, in the middle
the telescoping bound, and at the top the sign of the terminal sine. -/
@[expose] public section

namespace CentralUnimodality

open Real

noncomputable def cubicArcSum (t : ℝ) (l : ℕ) : ℝ :=
  let a := min t (3/(2*(l:ℝ)))
  ∑ i ∈ Finset.range l, let v := (a/2)*(2*(i:ℝ)+1); (v*(1-v^2/6))^2

private theorem small_arc {t θ : ℝ} {l : ℕ} (hl : 0 < l) (ht : 0 ≤ t) (htθ : t ≤ θ)
    (hθ : 2*l*θ ≤ π) : cubicArcSum t l ≤ blockSines θ l := by
  let a := min t (3/(2*(l:ℝ)))
  have hl' : (0:ℝ) < l := by exact_mod_cast hl
  have ha : 0 ≤ a := le_min ht (by positivity)
  have haθ : a ≤ θ := (min_le_left ..).trans htθ
  have hal : a*(2*l) ≤ 3 := (le_div_iff₀ (by positivity)).mp (min_le_right ..)
  apply Finset.sum_le_sum
  intro i hi
  have hi' : (i:ℝ)+1 ≤ l := by exact_mod_cast Finset.mem_range.mp hi
  let w : ℝ := 2*i+1
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hwl : w ≤ 2*l := by dsimp [w]; linarith
  let v := a/2*w
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hv' : v ≤ 3/2 := by
    have h := mul_le_mul_of_nonneg_left hwl ha
    dsimp [v]
    linarith only [h,hal]
  have hθ' : θ/2*w ≤ π/2 := by
    have h := mul_le_mul_of_nonneg_right hwl (ht.trans htθ)
    linarith only [h,hθ]
  have hmono : sin v ≤ sin (θ/2*w) := sin_le_sin_of_le_of_le_pi_div_two
    (by linarith only [hv,pi_pos]) hθ' (mul_le_mul_of_nonneg_right (by linarith only [haθ]) hw)
  have hlow : v*(1-v^2/6) ≤ sin v := by
    rcases hv.eq_or_lt with he|hp
    · simp [← he]
    · linarith only [sin_gt_sub_cube hp]
  have hpos : 0 ≤ v*(1-v^2/6) := by
    apply mul_nonneg hv
    nlinarith only [sq_le_sq₀ hv (by norm_num : (0:ℝ) ≤ 3/2) |>.2 hv']
  exact pow_le_pow_left₀ hpos (hlow.trans hmono) 2

private theorem large_arc {θ : ℝ} {l : ℕ} (hpos : 0 < θ) (hlt : θ < π)
    (htop : 2*l*(π-θ) ≤ π) : (l:ℝ)/4 ≤ blockSines θ l := by
  have hs := sin_pos_of_pos_of_lt_pi hpos hlt
  have hx : 0 ≤ 2*(l:ℝ)*(π-θ) := by positivity
  have hsin := sin_nonneg_of_nonneg_of_le_pi hx htop
  have hid := sin_nat_mul_two_pi_sub (2*l*(π-θ)) l
  rw [show (l:ℝ)*(2*π)-2*l*(π-θ) = 2*l*θ by ring] at hid
  apply le_of_mul_le_mul_left _ (show 0 < 4*sin θ by positivity)
  nlinarith only [blockSines_identity θ l,hid,hsin,mul_nonneg (Nat.cast_nonneg (α := ℝ) l) hs.le]

private theorem blockSines_pi (l : ℕ) : blockSines π l = l := by
  unfold blockSines
  calc
    _ = ∑ _i ∈ Finset.range l, (1:ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show π/2*(2*(i:ℝ)+1) = i*π+π/2 by ring,sin_add_pi_div_two,cos_nat_mul_pi,← pow_mul]
      rw [Nat.mul_comm, pow_mul]
      norm_num
    _ = _ := by simp

theorem blockSines_arc {t θ : ℝ} {l : ℕ} (hl : 0 < l) (ht : 0 ≤ t) (htθ : t ≤ θ) (hπ : θ ≤ π) :
    min ((l:ℝ)/4) (cubicArcSum t l) ≤ blockSines θ l := by
  rcases hπ.eq_or_lt with he|hlt
  · rw [he,blockSines_pi]
    exact (min_le_left ..).trans (by linarith [Nat.cast_nonneg (α := ℝ) l])
  by_cases hlo : 2*l*θ ≤ π
  · exact (min_le_right ..).trans (small_arc hl ht htθ hlo)
  apply (min_le_left ..).trans
  have hl' : (0:ℝ) < l := by exact_mod_cast hl
  have hθpos : 0 < θ := by
    by_contra! hz
    have h := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 2*(l:ℝ)) hz
    linarith [pi_pos]
  by_cases hhi : 2*l*(π-θ) ≤ π
  · exact large_arc hθpos hlt hhi
  apply blockSines_middle hl
  have small (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ π/2) (hx'' : π ≤ 2*l*x) : 1/(l:ℝ) ≤ sin x := by
    apply le_trans _ (mul_le_sin hx hx')
    rw [div_mul_eq_mul_div,div_le_div_iff₀ hl' pi_pos]
    linarith only [hx'']
  by_cases hhalf : θ ≤ π/2
  · exact small _ hθpos.le hhalf (by linarith only [hlo])
  · rw [← sin_pi_sub θ]
    exact small _ (by linarith only [hlt]) (by linarith only [hhalf]) (by linarith only [hhi])

theorem pairFactor_arc {t θ : ℝ} {l : ℕ} (hl : 0 < l) (ht : 0 ≤ t) (htθ : t ≤ θ) (hπ : θ ≤ π) :
    pairFactor (θ/2) l ≤ exp (-min ((l:ℝ)/4) (cubicArcSum t l)/4) := by
  apply (pairFactor_exp θ l).trans
  apply exp_le_exp.mpr
  linarith only [blockSines_arc hl ht htθ hπ]

end CentralUnimodality
