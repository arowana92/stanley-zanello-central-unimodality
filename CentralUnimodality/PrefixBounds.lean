module

public import CentralUnimodality.NormalizedCells

/-! An explicit lower bound for the minimum in the prefix induction.
Use squared weighted moment inequalities to avoid solving for a real minimizer. -/
@[expose] public section

namespace CentralUnimodality

def prefixConstant : ℚ := 3977/5000

private theorem weighted_cube {a b u v : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (a*u^2+b*v^2)^3 ≤ (a+b)*(a*u^3+b*v^3)^2 := by
  let A := a*u^2+b*v^2
  let B := a*u^3+b*v^3
  let F := a*u+b*v
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hc : F^2 ≤ (a+b)*A := by
    dsimp [F,A]
    nlinarith only [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (u-v))]
  have hd : A^2 ≤ F*B := by
    dsimp [A,F,B]
    nlinarith only [mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha hb) hu) hv) (sq_nonneg (u-v))]
  change A^3 ≤ (a+b)*B^2
  rcases hA.eq_or_lt with h|h
  · rw [← h,zero_pow (by decide : 3 ≠ 0)]
    exact mul_nonneg (add_nonneg ha hb) (sq_nonneg B)
  · apply (mul_le_mul_iff_right₀ h).mp
    calc
      A*A^3 = (A^2)^2 := by ring
      _ ≤ (F*B)^2 := (sq_le_sq₀ (sq_nonneg A) ((sq_nonneg A).trans hd)).mpr hd
      _ = F^2*B^2 := mul_pow ..
      _ ≤ ((a+b)*A)*B^2 := mul_le_mul_of_nonneg_right hc (sq_nonneg B)
      _ = _ := by ring

theorem prefix_minimum {l h : ℝ} (hl : 0 ≤ l) (hh : 0 ≤ h) :
    (prefixConstant:ℝ)*(l+h)*Real.sqrt (l+h) ≤
      (2*Real.sqrt 2/3)*l*Real.sqrt l + (131/250)*(2*h)*Real.sqrt (2*h) := by
  let u : ℝ := 0.9428
  let v : ℝ := 1.482
  have hu : 0 < u := by norm_num [u]
  have hv : 0 < v := by norm_num [v]
  have hu' : 0 ≤ u*Real.sqrt l := mul_nonneg hu.le (Real.sqrt_nonneg _)
  have hv' : 0 ≤ v*Real.sqrt h := mul_nonneg hv.le (Real.sqrt_nonneg _)
  have h₁ (x w : ℝ) (hx : 0 ≤ x) (hw : 0 < w) :
      (1/w^2)*(w*Real.sqrt x)^2 = x := by rw [mul_pow,Real.sq_sqrt hx]; field_simp
  have h₂ (x w : ℝ) (hx : 0 ≤ x) (hw : 0 < w) :
      (1/w^2)*(w*Real.sqrt x)^3 = w*x*Real.sqrt x := by
    rw [pow_succ (w*Real.sqrt x) 2,← mul_assoc,h₁ x w hx hw]; ring
  have he := weighted_cube (a := 1/u^2) (b := 1/v^2) (by positivity) (by positivity) hu' hv'
  rw [h₁ l u hl hu,h₁ h v hh hv,h₂ l u hl hu,h₂ h v hh hv] at he
  have hc : (prefixConstant:ℝ)^2*(1/u^2+1/v^2) ≤ 1 := by norm_num [prefixConstant,u,v]
  have hC : 0 ≤ (prefixConstant:ℝ) := by norm_num [prefixConstant]
  have hmin : (prefixConstant:ℝ)*(l+h)*Real.sqrt (l+h) ≤ u*l*Real.sqrt l+v*h*Real.sqrt h := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,mul_pow,Real.sq_sqrt (add_nonneg hl hh)]
    calc
      _ = (prefixConstant:ℝ)^2*(l+h)^3 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left he (sq_nonneg (prefixConstant:ℝ))
      _ ≤ _ := by
        rw [← mul_assoc]
        exact (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans_eq (one_mul _)
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hroot : (1.4142:ℝ) ≤ Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hu₀ : u ≤ 2*Real.sqrt 2/3 := by dsimp [u]; linarith
  have hv₀ : v ≤ (131/250)*2*Real.sqrt 2 := by dsimp [v]; linarith
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  apply hmin.trans
  have hu₁ := mul_le_mul_of_nonneg_right hu₀ (mul_nonneg hl (Real.sqrt_nonneg l))
  have hv₁ := mul_le_mul_of_nonneg_right hv₀ (mul_nonneg hh (Real.sqrt_nonneg h))
  linarith only [hu₁,hv₁]

end CentralUnimodality
