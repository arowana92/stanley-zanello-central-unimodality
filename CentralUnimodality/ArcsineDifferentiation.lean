module

public import CentralUnimodality.ArcsineSplit
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Integration by parts for the arcsine split and differentiation with
respect to a smooth time parameter. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit

open Set Real intervalIntegral MeasureTheory

theorem arc_stein {f d : ℝ → ℝ} (der : ∀ x, HasDerivAt f (d x) x) (cd : Continuous d) :
    arc (fun x => (2*x-1)*f x)=2*arc (fun x => x*(1-x)*d x) := by
  let z := fun t => sin t^2
  let G := fun t => sin t*cos t*f (z t)
  let D := fun t => 2*(z t*(1-z t)*d (z t))-(2*z t-1)*f (z t)
  have cf := continuous_iff_continuousAt.mpr (fun x => (der x).continuousAt)
  have dg (t : ℝ) : HasDerivAt G (D t) t := by
    have dz := (hasDerivAt_sin t).pow 2
    have H := ((hasDerivAt_sin t).mul (hasDerivAt_cos t)).mul ((der (z t)).comp t dz)
    convert H using 1
    · rfl
    · dsimp [D,z]
      have h := cos_sq' t
      linear_combination -(f (sin t^2)+2*sin t^2*d (sin t^2))*h
  have int := integral_eq_sub_of_hasDerivAt (a:=(0:ℝ)) (b:=π) (fun t _ => dg t)
    (by apply Continuous.intervalIntegrable; dsimp [D,z]; fun_prop)
  simp only [G,sin_pi,sin_zero,zero_mul,sub_zero] at int
  let b := fun t => z t*(1-z t)*d (z t)
  let a := fun t => (2*z t-1)*f (z t)
  change (∫ t in (0:ℝ)..π, 2*b t-a t)=0 at int
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; dsimp [b,z]; fun_prop)
    (by apply Continuous.intervalIntegrable; dsimp [a,z]; fun_prop),intervalIntegral.integral_const_mul] at int
  change (∫ t in (0:ℝ)..π, a t)/π=2*((∫ t in (0:ℝ)..π, b t)/π)
  field_simp; linarith only [int]

theorem arc_parameter {f d : ℝ → ℝ → ℝ} (cf : Continuous f.uncurry) (cd : Continuous d.uncurry)
    (der : ∀ v x, HasDerivAt (fun t => f t x) (d v x) v) (v : ℝ) :
    HasDerivAt (fun t => arc (f t)) (arc (d v)) v := by
  let z := fun t => sin t^2
  let F := fun u t => f u (z t)
  let D := fun u t => d u (z t)
  let s := Icc (v-1) (v+1)
  have hs : s∈nhds v := Icc_mem_nhds (by linarith) (by linarith)
  have zc : Continuous z := continuous_sin.pow 2
  have cg : Continuous F.uncurry :=
    cf.comp (continuous_fst.prodMk (zc.comp continuous_snd))
  have dc : Continuous D.uncurry :=
    cd.comp (continuous_fst.prodMk (zc.comp continuous_snd))
  obtain ⟨C,hC⟩ := (isCompact_Icc (a:=v-1) (b:=v+1) |>.prod (isCompact_uIcc (a:=(0:ℝ)) (b:=π))).bddAbove_image
    (continuous_abs.comp dc).continuousOn
  have slice (t : ℝ) : Continuous (F t) := cg.comp (continuous_const.prodMk continuous_id)
  have sd (t : ℝ) : Continuous (D t) := dc.comp (continuous_const.prodMk continuous_id)
  have H := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=F) (F':=D) (μ:=volume)
    (a:=0) (b:=π) (x₀:=v) (bound:=fun _ => C) hs (Filter.Eventually.of_forall (fun u => (slice u).aestronglyMeasurable))
    ((slice v).intervalIntegrable ..) (sd v).aestronglyMeasurable (Filter.Eventually.of_forall (fun t ht u hu => by
      rw [Real.norm_eq_abs]
      exact hC (mem_image_of_mem _ (show (u,t)∈s ×ˢ uIcc 0 π from ⟨hu,uIoc_subset_uIcc ht⟩))))
    (intervalIntegrable_const) (Filter.Eventually.of_forall (fun t _ u _ => der u (z t)))).2
  exact H.div_const π

end CentralUnimodality.ReturnSplit
