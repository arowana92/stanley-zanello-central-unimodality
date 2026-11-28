module

public import CentralUnimodality.QuarticSymbolSlopes
public import CentralUnimodality.LogarithmicSymbols
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Monotonicity and sixth-order remainders for the cosine and sinc
logarithms throughout the retained lattice-frequency window. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit
open Real Set

noncomputable def cosLoss (x : ℝ) := -log (cos x)-x^2/2-x^4/12
noncomputable def sincLoss (x : ℝ) := -log (sinc x)-x^2/6-x^4/180

private theorem control {f d : ℝ → ℝ} {c : ℝ} (hf : ContinuousOn f (Icc 0 (9/8)))
    (zero : f 0=0) (df : ∀ x∈Ioo 0 (9/8), HasDerivAt f (d x) x ∧ 0≤d x ∧ d x≤6*c*x^5) :
    MonotoneOn f (Icc 0 (9/8)) ∧ ∀ x∈Icc 0 (9/8), f x≤c*x^6 := by
  have m := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0:ℝ) (9/8)) hf (f':=d)
    (fun x hx => (df x (by simpa only [interior_Icc] using hx)).1.hasDerivWithinAt)
    (fun x hx => (df x (by simpa only [interior_Icc] using hx)).2.1)
  let g := fun x : ℝ => c*x^6-f x
  have cg : ContinuousOn g (Icc 0 (9/8)) := (continuous_const.mul (continuous_id.pow 6)).continuousOn.sub hf
  have dg (x : ℝ) (hx : x∈Ioo 0 (9/8)) : HasDerivAt g (6*c*x^5-d x) x := by
    convert (((hasDerivAt_pow 6 x).const_mul c).sub (df x hx).1) using 1
    norm_num; ring
  have n := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0:ℝ) (9/8)) cg
    (f':=fun x => 6*c*x^5-d x)
    (fun x hx => (dg x (by simpa only [interior_Icc] using hx)).hasDerivWithinAt)
    (fun x hx => sub_nonneg.mpr (df x (by simpa only [interior_Icc] using hx)).2.2)
  refine ⟨m,fun x hx => ?_⟩
  have H := n (show (0:ℝ)∈Icc 0 (9/8) by norm_num) hx hx.1
  simpa [g,zero] using H

theorem cosLoss_control : MonotoneOn cosLoss (Icc 0 (9/8)) ∧
    ∀ x∈Icc 0 (9/8), cosLoss x≤(1/20)*x^6 := by
  have pos {x : ℝ} (hx : x∈Icc 0 (9/8)) := cos_pos_nine_eighths (by rw [abs_of_nonneg hx.1]; exact hx.2)
  have hf : ContinuousOn cosLoss (Icc 0 (9/8)) := by
    unfold cosLoss
    exact (((continuous_cos.continuousOn.log (fun x hx => (pos hx).ne')).neg.sub
      ((continuous_id.pow 2).div_const 2).continuousOn).sub ((continuous_id.pow 4).div_const 12).continuousOn)
  apply control (d:=fun x => sin x/cos x-x-x^3/3) hf (by norm_num [cosLoss])
  intro x hx
  have cp := pos (Ioo_subset_Icc_self hx)
  have ⟨a,b,_,_⟩ := trig_quartic_slopes hx.1 hx.2.le
  have eq : x*sinc x=sin x := by rw [sinc_of_ne_zero hx.1.ne']; field_simp [hx.1.ne']
  have lo := mul_le_mul_of_nonneg_left a hx.1.le
  have hi := mul_le_mul_of_nonneg_left b hx.1.le
  rw [eq] at lo hi
  refine ⟨?_,?_,?_⟩
  · convert ((((hasDerivAt_cos x).log cp.ne').neg.sub ((hasDerivAt_pow 2 x).div_const 2)).sub
      ((hasDerivAt_pow 4 x).div_const 12)) using 1
    · rfl
    · norm_num; ring
  · have h : x+x^3/3≤sin x/cos x := (le_div_iff₀ cp).mpr (by linarith only [lo])
    linarith only [h]
  · have h : sin x/cos x≤x+x^3/3+3*x^5/10 := (div_le_iff₀ cp).mpr (by linarith only [hi])
    linarith only [h]

theorem sincLoss_control : MonotoneOn sincLoss (Icc 0 (9/8)) ∧
    ∀ x∈Icc 0 (9/8), sincLoss x≤(1/1000)*x^6 := by
  have pos {x : ℝ} (hx : x∈Icc 0 (9/8)) := sinc_pos_nine_eighths (by rw [abs_of_nonneg hx.1]; exact hx.2)
  have hf : ContinuousOn sincLoss (Icc 0 (9/8)) := by
    unfold sincLoss
    exact (((continuous_sinc.continuousOn.log (fun x hx => (pos hx).ne')).neg.sub
      ((continuous_id.pow 2).div_const 6).continuousOn).sub ((continuous_id.pow 4).div_const 180).continuousOn)
  apply control (d:=fun x => 1/x-cos x/sin x-x/3-x^3/45) hf (by norm_num [sincLoss])
  intro x hx
  have sp := sin_pos_of_pos_of_lt_pi hx.1 (by linarith only [hx.2,pi_gt_three])
  have ⟨_,_,a,b⟩ := trig_quartic_slopes hx.1 hx.2.le
  rw [sinc_of_ne_zero hx.1.ne'] at a b
  have lo : cos x*x≤(1-x^2/3-x^4/45)*sin x := by
    rwa [← mul_div_assoc,le_div_iff₀ hx.1] at a
  have hi : (1-x^2/3-x^4/45-3*x^6/500)*sin x≤cos x*x := by
    rwa [← mul_div_assoc,div_le_iff₀ hx.1] at b
  have scaled : (1/x-cos x/sin x-x/3-x^3/45)*(x*sin x) =
      (1-x^2/3-x^4/45)*sin x-cos x*x := by field_simp [hx.1.ne',sp.ne']; ring
  refine ⟨?_,?_,?_⟩
  · have localEq : sincLoss =ᶠ[nhds x] (fun y => log y-log (sin y)-y^2/6-y^4/180) := by
      filter_upwards [lt_mem_nhds hx.1,gt_mem_nhds (show x<π by linarith only [hx.2,pi_gt_three])] with y hp hpi
      rw [sincLoss,sinc_of_ne_zero hp.ne',log_div (sin_pos_of_pos_of_lt_pi hp hpi).ne' hp.ne']; ring
    apply HasDerivAt.congr_of_eventuallyEq _ localEq
    convert ((((hasDerivAt_log hx.1.ne').sub ((hasDerivAt_sin x).log sp.ne')).sub
      ((hasDerivAt_pow 2 x).div_const 6)).sub ((hasDerivAt_pow 4 x).div_const 180)) using 1
    norm_num; ring
  · apply (mul_le_mul_iff_of_pos_right (mul_pos hx.1 sp)).mp
    rw [zero_mul,scaled]; linarith only [lo]
  · apply (mul_le_mul_iff_of_pos_right (mul_pos hx.1 sp)).mp
    rw [scaled]; linarith only [hi]

end CentralUnimodality.ReturnSplit
