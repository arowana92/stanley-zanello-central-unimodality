module

public import CentralUnimodality.IntegratedTaylorRow
public import CentralUnimodality.LargePolynomialAmplitude
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Change of variable and truncation error for the exact polynomial
integral on the first 512 scaled frequencies. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

open Real Set intervalIntegral

set_option maxRecDepth 5000

noncomputable def spectralTrial (ξ : ℝ) := value candidate (|ξ|^(2/3:ℝ))

theorem spectralTrial_continuous : Continuous spectralTrial :=
  (value_continuous candidate).comp (continuous_rpow_const (by norm_num : (0:ℝ)≤2/3) |>.comp continuous_abs)

private theorem phaseTaylor_continuous (r D : ℕ) : Continuous (phaseTaylor r D) := by
  unfold phaseTaylor; fun_prop

private theorem scale_cubic {t : ℝ} (ht : 0≤t) : |512*t^3|^(2/3:ℝ)=64*t^2 := by
  rw [abs_of_nonneg (by positivity),show (512:ℝ)*t^3=(8*t)^3 by ring,← rpow_natCast _ 3,
    ← rpow_mul (by positivity : 0≤8*t)]
  norm_num; ring

theorem trial_taylor_integral (r D : ℕ) (x : ℝ) :
    (∫ ξ in (0:ℝ)..512, spectralTrial ξ*ξ^r*phaseTaylor r D (x*ξ))=
      integratedTaylor r D trialPower x := by
  let g := fun ξ : ℝ => spectralTrial ξ*ξ^r*phaseTaylor r D (x*ξ)
  let f := fun t : ℝ => 512*t^3
  have df (t : ℝ) : HasDerivAt f (1536*t^2) t := by
    convert ((hasDerivAt_id t).pow 3).const_mul 512 using 1 <;> simp <;> ring
  have cg : Continuous g := (spectralTrial_continuous.mul (continuous_id.pow r)).mul
    ((phaseTaylor_continuous r D).comp (continuous_const.mul continuous_id))
  have H := integral_comp_mul_deriv (a:=0) (b:=1) (g:=g) (fun t _ => df t)
    (by apply Continuous.continuousOn; fun_prop) cg
  simp only [f,zero_pow (by decide : 3≠0),one_pow,mul_zero,mul_one] at H
  change (∫ ξ in (0:ℝ)..512, g ξ)=_
  rw [← H,integratedTaylor]
  apply integral_congr
  intro t ht
  have ht' : t∈Icc (0:ℝ) 1 := by simpa using ht
  have small := input_pack_bounds.2.2.1
  dsimp only [Function.comp_apply,g,f,spectralTrial]
  rw [scale_cubic ht'.1,candidate,normalized_input _ _ small]
  change _=1536*t^2*((realDense (unpackCheb 1536 trialRow.toList)).eval (t^2/4)/2^120)*_*_
  rw [show 64*t^2/256=t^2/4 by ring]
  ring

set_option maxRecDepth 20000 in
theorem factorial_1025 : (324:ℕ)^1025*10^30≤Nat.factorial 1025 := by decide +kernel

private theorem phase_error {r : ℕ} {x ξ : ℝ} (hx : |x|≤0.631) (hξ : ξ∈Icc (0:ℝ) 512) :
    |phase r (x*ξ)-phaseTaylor r 1024 (x*ξ)|≤1/10^30 := by
  have cap : |x*ξ|≤324 := by
    rw [abs_mul,abs_of_nonneg hξ.1]
    exact (mul_le_mul hx hξ.2 hξ.1 (by norm_num)).trans (by norm_num)
  apply (phase_remainder r 1024 _).trans
  apply (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) cap 1025) (by positivity)).trans
  rw [div_le_div_iff₀ (by positivity) (by positivity),one_mul]
  exact_mod_cast factorial_1025

theorem spectralTrial_bound {ξ : ℝ} (hξ : |ξ|≤4096) : |spectralTrial ξ|≤2 := by
  apply (candidate_bounds _).1
  have nn := abs_nonneg ξ
  refine ⟨rpow_nonneg nn _,?_⟩
  have h := rpow_le_rpow nn hξ (by norm_num : (0:ℝ)≤2/3)
  apply h.trans_eq
  rw [show (4096:ℝ)=(16:ℝ)^(3:ℝ) by norm_num,← rpow_mul (by norm_num)]
  norm_num

theorem compact_phase_bound {r : ℕ} (hr : r≤2) {x : ℝ} (hx : |x|≤0.631) :
    |(∫ ξ in (0:ℝ)..512, spectralTrial ξ*ξ^r*phase r (x*ξ))-integratedTaylor r 1024 trialPower x|≤1/10^15 := by
  rw [← trial_taylor_integral,← integral_sub]
  · have point (ξ : ℝ) (hξ : ξ∈uIoc (0:ℝ) 512) :
        ‖spectralTrial ξ*ξ^r*phase r (x*ξ)-spectralTrial ξ*ξ^r*phaseTaylor r 1024 (x*ξ)‖≤
          2*512^2*(1/10^30:ℝ) := by
      have m : ξ∈Icc (0:ℝ) 512 := by
        rw [uIoc_of_le (by norm_num)] at hξ
        exact ⟨hξ.1.le,hξ.2⟩
      have a := spectralTrial_bound (ξ:=ξ) (by rw [abs_of_nonneg m.1]; linarith only [m.2])
      have b := (pow_le_pow_left₀ m.1 m.2 r).trans (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤512) hr)
      rw [Real.norm_eq_abs,← mul_sub,abs_mul,abs_mul,abs_pow,abs_of_nonneg m.1]
      exact mul_le_mul (mul_le_mul a b (pow_nonneg m.1 r) (by norm_num)) (phase_error hx m) (abs_nonneg _) (by positivity)
    have H := norm_integral_le_of_norm_le_const (a:=(0:ℝ)) (b:=512) point
    rw [Real.norm_eq_abs] at H
    exact H.trans (by norm_num)
  · apply Continuous.intervalIntegrable
    exact (spectralTrial_continuous.mul (continuous_id.pow r)).mul
      ((continuous_cos.comp (continuous_id.add continuous_const)).comp (continuous_const.mul continuous_id))
  · apply Continuous.intervalIntegrable
    exact (spectralTrial_continuous.mul (continuous_id.pow r)).mul
      ((phaseTaylor_continuous r 1024).comp (continuous_const.mul continuous_id))

end CentralUnimodality.PolynomialTrial
