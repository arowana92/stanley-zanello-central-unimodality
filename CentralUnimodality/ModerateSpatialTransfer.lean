module

public import CentralUnimodality.SpatialTrialTransfer
public import CentralUnimodality.ModerateFrequencyTail
public import CentralUnimodality.IntegralPeakWindow

/-! At moderate sizes, two absolute Fourier integrals certify the
full spatial comparisons uniformly on the three closed intervals. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Real Set Witness intervalIntegral

noncomputable def retainedError (n δ r : ℕ) :=
  ∫ ξ in (0:ℝ)..1728, |signedAmplitude n δ (ξ/cellScale (n+δ))-spectralTrial ξ| *ξ^r

theorem retained_transfer {n δ r : ℕ} (hs : δ≤1) (hn : 300000≤n+δ) (hr : r≤2)
    {x : ℝ} (hx : |x|≤0.631) :
    |rankIntegralOrder n δ r x-integratedTaylor r 1024 trialPower x|≤
      retainedError n δ r+1200*12^(3*r+1)*exp (-(0.157*144))+0.003 := by
  let A := rankKernel n δ r x
  let F := fun ξ : ℝ => spectralTrial ξ*ξ^r*phase r (x*ξ)
  let T := 0.008*cellScale (n+δ)
  let U := π*cellScale (n+δ)
  let P := integratedTaylor r 1024 trialPower x
  have cA := rankKernel_continuous n δ r hs x
  have cG : Continuous (fun ξ : ℝ => phase r (x*ξ)) := by unfold phase; fun_prop
  have cF : Continuous F := (spectralTrial_continuous.mul (continuous_id.pow r)).mul cG
  have close : |(∫ ξ in (0:ℝ)..1728, A ξ)-(∫ ξ in (0:ℝ)..1728, F ξ)|≤retainedError n δ r := by
    rw [← integral_sub (cA.intervalIntegrable ..) (cF.intervalIntegrable ..)]
    apply integral_abs_of_envelope (by norm_num) (cA.sub cF)
      (((amplitude_continuous _ _ hs).sub spectralTrial_continuous).abs.mul (continuous_id.pow r))
    intro ξ h
    change |signedAmplitude n δ _*ξ^r*phase r (x*ξ)-spectralTrial ξ*ξ^r*phase r (x*ξ)|≤_
    rw [← sub_mul,← sub_mul,abs_mul,abs_mul,abs_pow,abs_of_nonneg h.1]
    exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (pow_nonneg h.1 _)) (abs_cos_le_one _)
  have compact : |(∫ ξ in (0:ℝ)..512,F ξ)-P|≤1/10^15 := compact_phase_bound hr hx
  have band : |∫ ξ in (512:ℝ)..1728,F ξ|≤1/1000 := trial_band_integral (by norm_num) hr x
  have cut : 1728≤T := by have t := (long_scale_from_300000 hn).1; dsimp only [T]; linarith only [t]
  have middle := moderate_inner_tail hs (by omega) hr x cut (le_rfl : T≤0.008*cellScale (n+δ))
  have outer := outer_rank_tail_from_300000 hs hn hr x
  have eq : rankIntegralOrder n δ r x-P=
      ((∫ ξ in (0:ℝ)..1728,A ξ)-(∫ ξ in (0:ℝ)..1728,F ξ))+
      ((∫ ξ in (0:ℝ)..512,F ξ)-P)+(∫ ξ in (512:ℝ)..1728,F ξ)+
      (∫ ξ in (1728:ℝ)..T,A ξ)+(∫ ξ in T..U,A ξ) := by
    change (∫ ξ in (0:ℝ)..U,A ξ)-P=_
    have f := integral_add_adjacent_intervals (μ:=MeasureTheory.volume) (a:=0) (b:=512) (c:=1728)
      (cF.intervalIntegrable ..) (cF.intervalIntegrable ..)
    have a := integral_add_adjacent_intervals (μ:=MeasureTheory.volume) (a:=0) (b:=1728) (c:=T)
      (cA.intervalIntegrable ..) (cA.intervalIntegrable ..)
    have b := integral_add_adjacent_intervals (μ:=MeasureTheory.volume) (a:=0) (b:=T) (c:=U)
      (cA.intervalIntegrable ..) (cA.intervalIntegrable ..)
    linarith only [f,a,b]
  change |rankIntegralOrder n δ r x-P|≤_
  rw [eq]
  apply (abs_add_le ..).trans
  apply (add_le_add (abs_add_le ..) outer).trans
  apply (add_le_add (add_le_add (abs_add_le ..) middle) le_rfl).trans
  apply (add_le_add (add_le_add (add_le_add (abs_add_le ..) band) le_rfl) le_rfl).trans
  linarith only [close,compact]

private theorem tail_constants :
    1200*12^(3*1+1)*exp (-(0.157*144))≤0.004 ∧ 1200*12^(3*2+1)*exp (-(0.157*144))≤7 := by
  let a : ℚ := 0.157*144/16
  have H := pow_le_pow_left₀ (exp_pos _).le (upperNegExp_sound (show 0≤a by norm_num [a])) 16
  rw [← exp_nat_mul] at H
  have exactBound : exp (-(0.157*144))≤(upperNegExp a:ℝ)^16 := by
    apply le_trans _ H; apply exp_le_exp.mpr; norm_num [a]
  have budgets : 1200*(12:ℚ)^4*upperNegExp a^16≤0.004 ∧ 1200*(12:ℚ)^7*upperNegExp a^16≤7 := by decide +kernel
  obtain ⟨p,q⟩ := budgets
  have P := (Rat.cast_le (K:=ℝ)).2 p
  have Q := (Rat.cast_le (K:=ℝ)).2 q
  push_cast at P Q
  constructor
  · apply (mul_le_mul_of_nonneg_left exactBound (by norm_num)).trans
    norm_num at P ⊢; exact P
  · apply (mul_le_mul_of_nonneg_left exactBound (by norm_num)).trans
    norm_num at Q ⊢; exact Q

theorem peak_of_retained_errors {n δ : ℕ} (hs : δ≤1) (hn : 300000≤n)
    (first : retainedError n δ 1≤0.176) (second : retainedError n δ 2≤148.4)
    (left : ∀ x∈Icc (0.1359:ℝ) 0.339, 1/5 ≤ integratedTaylor 1 1024 trialPower x)
    (middle : ∀ x∈Icc (0.333:ℝ) 0.404, integratedTaylor 2 1024 trialPower x≤ -160)
    (right : ∀ x∈Icc (0.398:ℝ) 0.631, integratedTaylor 1 1024 trialPower x≤ -2) : ThreeFifthsPeak n δ := by
  apply threeFifths_of_integral_signs hn hs
  · intro x hx
    have tr := (abs_le.mp (retained_transfer (n:=n) hs (by omega) (by decide : 1≤2) (x:=x)
      (abs_le.mpr ⟨by linarith only [hx.1],by linarith only [hx.2]⟩))).1
    linarith only [tr,left x hx,first,tail_constants.1]
  · intro x hx
    have tr := (abs_le.mp (retained_transfer (n:=n) hs (by omega) (by decide : 2≤2) (x:=x)
      (abs_le.mpr ⟨by linarith only [hx.1],by linarith only [hx.2]⟩))).2
    linarith only [tr,middle x hx,second,tail_constants.2]
  · intro x hx
    have tr := (abs_le.mp (retained_transfer (n:=n) hs (by omega) (by decide : 1≤2) (x:=x)
      (abs_le.mpr ⟨by linarith only [hx.1],by linarith only [hx.2]⟩))).2
    linarith only [tr,right x hx,first,tail_constants.1]

end CentralUnimodality.PolynomialTrial
