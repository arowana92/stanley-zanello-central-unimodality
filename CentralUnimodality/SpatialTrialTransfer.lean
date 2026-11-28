module

public import CentralUnimodality.CompactPhaseIntegral
public import CentralUnimodality.SpatialOuterTail
public import CentralUnimodality.PackedTrialTail

/-! Transfer a sign margin for the integrated polynomial to the full
spatial derivatives of the finite staircase distribution. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

open Set Real Witness intervalIntegral

private theorem integral_cap {a b c : ℝ} {f : ℝ → ℝ} (hab : a≤b) (hf : ∀ ξ∈Icc a b, |f ξ|≤c) :
    |∫ ξ in a..b, f ξ|≤c*(b-a) := by
  have H := norm_integral_le_of_norm_le_const (a:=a) (b:=b) (f:=f) (C:=c) (fun ξ h => by
    rw [uIoc_of_le hab] at h
    simpa only [Real.norm_eq_abs] using hf ξ ⟨h.1.le,h.2⟩)
  rwa [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab)] at H

theorem full_period_error {n δ r : ℕ} (hs : δ≤1) (hn : 10^54≤n+δ) (hr : r≤2)
    {x : ℝ} (hx : |x|≤0.631) :
    |rankIntegralOrder n δ r x-integratedTaylor r 1024 trialPower x|≤
      (4096:ℝ)^(r+1)/10^10+1/100 := by
  let A := rankKernel n δ r x
  let F := fun ξ : ℝ => spectralTrial ξ*ξ^r*phase r (x*ξ)
  let T := 0.008*cellScale (n+δ)
  let U := π*cellScale (n+δ)
  have contA := rankKernel_continuous n δ r hs x
  have G : Continuous (fun ξ : ℝ => phase r (x*ξ)) := by unfold phase; fun_prop
  have contF : Continuous F := (spectralTrial_continuous.mul (continuous_id.pow r)).mul G
  have close : |(∫ ξ in (0:ℝ)..4096, A ξ)-(∫ ξ in (0:ℝ)..4096, F ξ)|≤4096^(r+1)/10^10 := by
    rw [← integral_sub (contA.intervalIntegrable ..) (contF.intervalIntegrable ..)]
    apply (integral_cap (by norm_num) (c:=(1/10^10)*4096^r) ?_).trans_eq
    · rw [pow_succ]; ring
    · intro ξ h
      have amp := amplitude_4096 hs hn (ξ:=ξ) (by rw [abs_of_nonneg h.1]; exact h.2)
      change |signedAmplitude n δ _*ξ^r*phase r (x*ξ)-spectralTrial ξ*ξ^r*phase r (x*ξ)|≤_
      rw [← sub_mul,← sub_mul,abs_mul,abs_mul,abs_pow,abs_of_nonneg h.1]
      apply (mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (pow_nonneg h.1 r)) (abs_cos_le_one _)).trans
      exact mul_le_mul amp (pow_le_pow_left₀ h.1 h.2 r) (pow_nonneg h.1 r) (by norm_num)
  have far : |∫ ξ in (512:ℝ)..4096, F ξ|≤1/1000 := by
    apply (integral_cap (by norm_num) (c:=(1/10^14)*4096^2) ?_).trans (by norm_num)
    intro ξ h
    have nn : 0≤ξ := by linarith only [h.1]
    have lower := rpow_le_rpow (by norm_num : (0:ℝ)≤512) h.1 (by norm_num : (0:ℝ)≤2/3)
    have upper := rpow_le_rpow nn h.2 (by norm_num : (0:ℝ)≤2/3)
    rw [show (512:ℝ)=(8:ℝ)^(3:ℝ) by norm_num,← rpow_mul (by norm_num)] at lower
    rw [show (4096:ℝ)=(16:ℝ)^(3:ℝ) by norm_num,← rpow_mul (by norm_num)] at upper
    norm_num at lower upper
    have band := trial_tail ⟨lower,upper⟩
    dsimp only [F,spectralTrial]
    rw [abs_of_nonneg nn,abs_mul,abs_mul,abs_pow,abs_of_nonneg nn]
    apply (mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (pow_nonneg nn _)) (abs_cos_le_one _)).trans
    apply mul_le_mul band ((pow_le_pow_left₀ nn h.2 r).trans (pow_le_pow_right₀ (by norm_num) hr))
      (pow_nonneg nn r) (by norm_num)
  have low := compact_phase_bound hr hx
  have mid := inner_rank_tail hs (by omega) hr x (long_scale hn).1 le_rfl
  have high := outer_rank_tail hs hn hr x
  let P := integratedTaylor r 1024 trialPower x
  have eq : rankIntegralOrder n δ r x-P=
      ((∫ ξ in (0:ℝ)..4096, A ξ)-(∫ ξ in (0:ℝ)..4096, F ξ))+
      ((∫ ξ in (0:ℝ)..512, F ξ)-P)+(∫ ξ in (512:ℝ)..4096, F ξ)+
      (∫ ξ in (4096:ℝ)..T, A ξ)+(∫ ξ in T..U, A ξ) := by
    change (∫ ξ in (0:ℝ)..U, A ξ)-P=_
    have s := integral_add_adjacent_intervals (μ:=MeasureTheory.volume) (a:=0) (b:=512) (c:=4096)
      (contF.intervalIntegrable ..) (contF.intervalIntegrable ..)
    have a := integral_add_adjacent_intervals (μ:=MeasureTheory.volume) (a:=0) (b:=4096) (c:=T)
      (contA.intervalIntegrable ..) (contA.intervalIntegrable ..)
    have b := integral_add_adjacent_intervals (μ:=MeasureTheory.volume) (a:=0) (b:=T) (c:=U)
      (contA.intervalIntegrable ..) (contA.intervalIntegrable ..)
    linarith only [s,a,b]
  change |rankIntegralOrder n δ r x-P|≤_
  rw [eq]
  apply (abs_add_le ..).trans
  apply (add_le_add (abs_add_le ..) high).trans
  apply (add_le_add (add_le_add (abs_add_le ..) mid) le_rfl).trans
  apply (add_le_add (add_le_add (add_le_add (abs_add_le ..) far) le_rfl) le_rfl).trans
  have hlow : |(∫ ξ in (0:ℝ)..512, F ξ)-P|≤1/10^15 := low
  linarith only [close,hlow]

end CentralUnimodality.PolynomialTrial
