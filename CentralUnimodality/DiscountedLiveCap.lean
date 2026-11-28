module

public import CentralUnimodality.MarkedLateRankBounds

/-! A dimensionless survival estimate for a positive fraction of a walk.
It retains the Gaussian discount in the homogeneous ballot bound. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

noncomputable def discountedLive (β f : ℝ) : ℝ :=
  2*β+(4/5)/√f*exp (-(12/25)*β^2*f)

theorem scaled_live_cap {β f : ℝ} {m t : ℕ} (hm : 0<m) (hf : 0<f)
    (ht : f*m≤t) (hβ : 0≤β) (hβ' : β/√m≤6/25) :
    liveCap (β/√m) t ≤ discountedLive β f/√m := by
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have hr := sqrt_pos.mpr hm'
  let u := β/√m
  have hu : 0≤u := div_nonneg hβ hr.le
  have hlin : tanh u≤u := tanh_le_linear hu
  have hu' : u≤6/25 := hβ'
  have hs := pow_le_pow_left₀ hu hu' 2
  have hlow : (49/50)*u≤tanh u := by
    nlinarith only [tanh_cubic_lower hu,mul_le_mul_of_nonneg_left hs hu,hu]
  have hv := pow_le_pow_left₀ (mul_nonneg (by norm_num : (0:ℝ)≤49/50) hu) hlow 2
  have hS : (m:ℝ)*u^2=β^2 := by
    dsimp only [u]; rw [div_pow,sq_sqrt hm'.le]; field_simp
  have hdecay : exp (-((t:ℝ)*(tanh u)^2/2)) ≤ exp (-(12/25)*β^2*f) := by
    apply exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left hv (mul_nonneg hf.le hm'.le),
      mul_le_mul_of_nonneg_right ht (sq_nonneg (tanh u)),congrArg (f*·) hS,
      mul_nonneg hf.le (sq_nonneg β)]
  have hroot : √f*√m≤√(t:ℝ) := by rw [← sqrt_mul hf.le]; exact sqrt_le_sqrt ht
  have hquot := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤4/5) (mul_pos (sqrt_pos.mpr hf) hr) hroot
  have H := mul_le_mul hquot hdecay (exp_pos _).le (by positivity)
  change 2*tanh u+_≤_
  apply (add_le_add (mul_le_mul_of_nonneg_left hlin (by norm_num : (0:ℝ)≤2)) H).trans_eq
  dsimp only [u,discountedLive]; ring

theorem discounted_parameter_survival {β f c u : ℝ} {m t : ℕ} (hm : 0<m) (hf : 0<f)
    (ht : f*m≤t) (hβ : 0≤β) (hβ' : β/√m≤6/25)
    (hcap : ∀ i<t, u-c*i≤β/√m) :
    live c u t 1 ≤ discountedLive β f/√m := by
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have ht' : 0<t := by exact_mod_cast ((mul_pos hf hm').trans_le ht)
  apply (live_parameters c u 0 (β/√m) t 1 (fun i hi => by simpa only [zero_mul,sub_zero] using hcap i hi)).trans
  exact (homogeneous_live_upper (div_nonneg hβ (sqrt_nonneg _)) ht').trans
    (scaled_live_cap hm hf ht hβ hβ')

end CentralUnimodality.MarkedExcursion
