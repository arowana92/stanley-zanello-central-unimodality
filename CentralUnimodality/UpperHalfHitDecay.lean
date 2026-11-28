module

public import CentralUnimodality.UpperHalfPrefixScales

/-! Uniform first-crossing exponential cost when the scaled rank tilt
runs from 23.8 up to twice the square root of the length. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

theorem far_hit_decay {M γ a : ℝ} (hM : 4096 ≤ M) (hγ : 119/5 ≤ γ) (hcap : γ^2 ≤ 4*M)
    (ha : 1/160 ≤ a) :
    γ*exp (-(a*γ^2*(1-γ^2/(6*M)))) ≤ (119/5)*exp (-(a*(19/20)*(119/5)^2)) := by
  let g : ℝ := 119/5
  have hp : 0<M := by linarith
  have hg : 0<g := by norm_num [g]
  have hγ₀ : g ≤ γ := hγ
  have hγsq := pow_le_pow_left₀ hg.le hγ₀ 2
  have drift : 19/20*g^2+(γ^2-g^2)/6 ≤ γ^2*(1-γ^2/(6*M)) := by
    by_cases h₁ : γ≤32
    · have hs := pow_le_pow_left₀ (hg.le.trans hγ₀) h₁ 2
      have hdiv : γ^2/(6*M) ≤ 1/20 := (div_le_iff₀ (by positivity)).mpr (by linarith only [hs,hM])
      apply le_trans _ (mul_le_mul_of_nonneg_left (show 19/20 ≤ 1-γ^2/(6*M) by linarith only [hdiv]) (sq_nonneg γ))
      linear_combination (47/60:ℝ)*hγsq
    · have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤32) (le_of_not_ge h₁) 2
      by_cases h₂ : γ≤64
      · have hq := pow_le_pow_left₀ (hg.le.trans hγ₀) h₂ 2
        have hdiv : γ^2/(6*M) ≤ 1/6 := (div_le_iff₀ (by positivity)).mpr (by linarith only [hq,hM])
        dsimp only [g]; nlinarith only [mul_le_mul_of_nonneg_left hdiv (sq_nonneg γ),hs]
      · have hq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤64) (le_of_not_ge h₂) 2
        have hdiv : γ^2/(6*M) ≤ 2/3 := (div_le_iff₀ (by positivity)).mpr (by linarith only [hcap])
        dsimp only [g]; nlinarith only [mul_le_mul_of_nonneg_left hdiv (sq_nonneg γ),hq]
  let t := a*((γ^2-g^2)/6)
  have hab : 0 ≤ a := by linarith
  have hlinear : γ ≤ g*(1+t) := by
    have H := mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr hγsq)
    dsimp only [g,t] at *
    nlinarith only [H,sq_nonneg (γ-119/5),hγ]
  have he := (mul_le_mul_of_nonneg_left (add_one_le_exp t) hg.le)
  have ht : γ ≤ g*exp t := by linarith only [hlinear,he]
  apply (mul_le_mul_of_nonneg_right ht (exp_pos _).le).trans
  rw [mul_assoc,← exp_add]
  apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr _) hg.le
  dsimp only [t]; change _ ≤ -(a*(19/20)*g^2)
  linarith only [mul_le_mul_of_nonneg_left drift hab]

end CentralUnimodality.MarkedExcursion
