module

public import CentralUnimodality.GridArcEstimates
public import CentralUnimodality.IntegralPeakSigns
public import CentralUnimodality.FourierPhaseTaylor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Continuous omitted-frequency estimates for the peak derivatives. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

open Real Set intervalIntegral Witness

noncomputable def rankKernel (n δ r : ℕ) (x ξ : ℝ) :=
  signedAmplitude n δ (ξ/cellScale (n+δ))*ξ^r*phase r (x*ξ)

theorem amplitude_continuous (n δ : ℕ) (hs : δ≤1) :
    Continuous (fun ξ => signedAmplitude n δ (ξ/cellScale (n+δ))) := by
  simp_rw [signedAmplitude_mean _ _ hs,rankMean]; fun_prop

theorem rankKernel_continuous (n δ r : ℕ) (hs : δ≤1) (x : ℝ) : Continuous (rankKernel n δ r x) := by
  have h := amplitude_continuous n δ hs
  unfold rankKernel phase; fun_prop

theorem amplitude_le_magnitude (n δ : ℕ) (θ : ℝ) : |signedAmplitude n δ θ|≤signedMagnitude n δ θ := by
  rw [signedAmplitude,signedMagnitude,abs_div,abs_of_pos (survival_pos _)]
  exact div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) (survival_pos _).le

theorem integral_abs_of_envelope {a b : ℝ} {f g : ℝ → ℝ} (hab : a≤b) (hf : Continuous f)
    (hg : Continuous g) (h : ∀ t∈Icc a b, |f t|≤g t) :
    |∫ t in a..b, f t|≤∫ t in a..b, g t := by
  rw [← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm hab).trans
  exact integral_mono_on hab (hf.norm.intervalIntegrable ..) (hg.intervalIntegrable ..)
    (fun t ht => by simpa only [Real.norm_eq_abs] using h t ht)

private noncomputable def envelope (ξ : ℝ) := 100*ξ^2*exp (-(0.157*ξ^(2/3:ℝ)))

private theorem envelope_cont : Continuous envelope := by
  have h := continuous_rpow_const (by norm_num : (0:ℝ)≤2/3)
  unfold envelope; fun_prop

private theorem exp_256 : 1100*(16:ℝ)^7*exp (-(0.157*256))≤1/1000 := by
  let a : ℚ := 0.157*256/16
  have h := upperNegExp_sound (show 0≤a by norm_num [a])
  have expbound := pow_le_pow_left₀ (exp_pos _).le h 16
  rw [← exp_nat_mul] at expbound
  have actual : exp (-(0.157*256))≤(upperNegExp a:ℝ)^16 := by
    apply le_trans _ expbound
    apply exp_le_exp.mpr
    norm_num [a]
  apply (mul_le_mul_of_nonneg_left actual (by norm_num : (0:ℝ)≤1100*16^7)).trans
  have H : ((1100*16^7*upperNegExp a^16:ℚ):ℝ)≤((1/1000:ℚ):ℝ) :=
    Rat.cast_le.mpr (by decide +kernel)
  push_cast at H
  exact H

private theorem inner_envelope_integral {b : ℝ} (hb : 4096≤b) :
    (∫ ξ in (4096:ℝ)..b, envelope ξ)≤1/1000 := by
  let B := b^(1/3:ℝ)
  have bn : 0≤b := by linarith only [hb]
  have b3 : B^3=b := by dsimp [B]; rw [← rpow_natCast _ 3,← rpow_mul bn]; norm_num
  have ge : 16≤B := by
    apply le_of_pow_le_pow_left₀ (n:=3) (by decide) (rpow_nonneg bn _)
    rw [b3]; norm_num; exact hb
  let f := fun t : ℝ => t^3
  have df (t : ℝ) : HasDerivAt f (3*t^2) t := by simpa [f] using hasDerivAt_pow 3 t
  have sub := integral_comp_mul_deriv (a:=16) (b:=B) (g:=envelope) (fun t _ => df t)
    (by apply Continuous.continuousOn; fun_prop) envelope_cont
  change (∫ t in (16:ℝ)..B, (envelope ∘ f) t*(3*t^2))=∫ ξ in (16:ℝ)^3..B^3, envelope ξ at sub
  rw [b3,show (16:ℝ)^3=4096 by norm_num] at sub
  rw [← sub]
  let G := fun t : ℝ => -1100*t^7*exp (-(0.157*t^2))
  let d := fun t : ℝ => (1100*(2*0.157*t^2-7)*t^6)*exp (-(0.157*t^2))
  have der (t : ℝ) : HasDerivAt G (d t) t := by
    have E := (((hasDerivAt_pow 2 t).const_mul (-0.157:ℝ)).exp)
    convert (((hasDerivAt_pow 7 t).const_mul (-1100:ℝ)).mul E) using 1
    · funext s; dsimp [G]; simp only [neg_mul]
    · dsimp [d]; simp only [neg_mul]; ring
  have prim := integral_eq_sub_of_hasDerivAt (a:=16) (b:=B) (fun t _ => der t)
    (by apply Continuous.intervalIntegrable; dsimp [d]; fun_prop)
  apply (integral_mono_on ge _ _ (g:=d) ?_).trans
  · rw [prim]
    have neg : G B≤0 := by dsimp [G]; apply mul_nonpos_of_nonpos_of_nonneg _ (exp_pos _).le
                           exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (pow_nonneg (by linarith only [ge]) _)
    have left : -G 16=1100*16^7*exp (-(0.157*256)) := by dsimp [G]; norm_num
    linarith only [exp_256,left,neg]
  · apply Continuous.intervalIntegrable
    exact (envelope_cont.comp (continuous_id.pow 3)).mul (continuous_const.mul (continuous_id.pow 2))
  · apply Continuous.intervalIntegrable; dsimp [d]; fun_prop
  · intro t ht
    have nn : 0≤t := by linarith only [ht.1]
    have cube : (t^3)^(2/3:ℝ)=t^2 := by rw [← rpow_natCast _ 3,← rpow_mul nn]; norm_num
    dsimp [Function.comp_apply,envelope,f,d]
    rw [cube]
    have sqbound := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤16) ht.1 2
    have gain : 300*t^2≤1100*(2*0.157*t^2-7) := by linarith only [sqbound]
    have prod := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right gain (pow_nonneg nn 6))
      (exp_pos (-(0.157*t^2))).le
    linarith only [prod]

theorem inner_rank_tail {n δ r : ℕ} (hs : δ≤1) (hn : 2049≤n+δ) (hr : r≤2) (x : ℝ)
    {b : ℝ} (hb : 4096≤b) (hS : b≤0.008*cellScale (n+δ)) :
    |∫ ξ in (4096:ℝ)..b, rankKernel n δ r x ξ|≤1/1000 := by
  apply (integral_abs_of_envelope hb (rankKernel_continuous _ _ _ hs x) envelope_cont ?_).trans
    (inner_envelope_integral hb)
  intro ξ hξ
  have absA := (amplitude_le_magnitude n δ _).trans
    (scaled_inner_magnitude hs hn (by linarith only [hξ.1]) (hξ.2.trans hS))
  have power := pow_le_pow_right₀ (by linarith only [hξ.1] : (1:ℝ)≤ξ) hr
  rw [rankKernel,abs_mul,abs_mul,abs_pow,abs_of_nonneg (by linarith only [hξ.1] : 0≤ξ)]
  have nn : 0≤ξ := by linarith only [hξ.1]
  apply (mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (pow_nonneg nn _)) (abs_cos_le_one _)).trans
  exact (mul_le_mul absA power (pow_nonneg nn _) (by positivity)).trans_eq (by unfold envelope; ring)

end CentralUnimodality.PolynomialTrial
