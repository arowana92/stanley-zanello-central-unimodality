module

public import CentralUnimodality.TiltedFirstHit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.Deriv

/-! A lower bound on the partition function of the centered linear tilt. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion

open Real Set

private theorem nonneg_from_zero {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (h₀ : f 0 = 0) (hs : ∀ x ≥ 0, 0 ≤ f' x) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0:ℝ))
    (fun z _ => (hf z).continuousAt.continuousWithinAt)
    (fun z _ => (hf z).hasDerivWithinAt) (fun z hz => hs z (interior_subset hz))
  simpa [h₀] using hm (show (0:ℝ) ∈ Ici 0 by simp) hx hx

private theorem tanh_deriv (x : ℝ) : HasDerivAt tanh (1-(tanh x)^2) x := by
  simp only [funext tanh_eq_sinh_div_cosh]
  convert (hasDerivAt_sinh x).div (hasDerivAt_cosh x) (cosh_pos x).ne' using 1
  field_simp [(cosh_pos x).ne']

theorem tanh_le_linear {z : ℝ} (hz : 0 ≤ z) : tanh z ≤ z := by
  have h := nonneg_from_zero (f := fun v => v-tanh v) (f' := fun v => 1-(1-(tanh v)^2))
    (fun v => (hasDerivAt_id v).sub (tanh_deriv v)) (by simp)
    (fun v _ => by nlinarith only [sq_nonneg (tanh v)]) hz
  linarith only [h]

theorem tanh_cubic_lower {z : ℝ} (hz : 0 ≤ z) : z-z^3/3 ≤ tanh z := by
  have H (v : ℝ) : HasDerivAt (fun t => tanh t-t+t^3/3) (v^2-(tanh v)^2) v := by
    convert ((tanh_deriv v).sub (hasDerivAt_id' v)).add (((hasDerivAt_id' v).pow 3).div_const 3) using 1
    ring
  have h := nonneg_from_zero H (by simp) (fun v hv => sub_nonneg.mpr
    ((sq_le_sq₀ (by rw [tanh_eq_sinh_div_cosh]; exact div_nonneg (sinh_nonneg_iff.mpr hv) (cosh_pos _).le) hv).mpr (tanh_le_linear hv))) hz
  linarith only [h]

private theorem log_cosh_lower_pos {x : ℝ} (hx : 0 ≤ x) :
    x^2/2-x^4/12 ≤ log (cosh x) := by
  have H (z : ℝ) : HasDerivAt (fun t => log (cosh t)-t^2/2+t^4/12) (tanh z-z+z^3/3) z := by
    convert (((hasDerivAt_cosh z).log (cosh_pos z).ne').sub (((hasDerivAt_id z).pow 2).div_const 2)).add
      (((hasDerivAt_id z).pow 4).div_const 12) using 1
    · rfl
    · simp only [tanh_eq_sinh_div_cosh,id_eq]; ring
  have h := nonneg_from_zero H (by simp) (fun z hz => by linarith only [tanh_cubic_lower hz]) hx
  linarith only [h]

/-- The cumulant of a centered tilted sign is bounded by the same quadratic
for every starting parameter and every increment of either sign. -/
theorem log_cosh_shift (u w : ℝ) :
    log (cosh (u+w)) - log (cosh u) ≤ w*tanh u + w^2/2 := by
  have pos (a x : ℝ) (hx : 0 ≤ x) :
      log (cosh (a+x))-log (cosh a) ≤ x*tanh a+x^2/2 := by
    have dh (v : ℝ) : HasDerivAt (fun t => tanh (a+t)) (1-(tanh (a+v))^2) v := by
      convert (tanh_deriv (a+v)).comp v ((hasDerivAt_id' v).const_add a) using 1
      · rfl
      · ring
    have slope (v : ℝ) (hv : 0 ≤ v) : 0 ≤ tanh a+v-tanh (a+v) := by
      apply nonneg_from_zero (f := fun t => tanh a+t-tanh (a+t))
        (f' := fun t => 1-(1-(tanh (a+t))^2)) (fun t => ((hasDerivAt_id' t).const_add _).sub (dh t))
        (by simp) (fun t _ => by nlinarith only [sq_nonneg (tanh (a+t))]) hv
    have D (v : ℝ) : HasDerivAt (fun t => t*tanh a+t^2/2-(log (cosh (a+t))-log (cosh a)))
        (tanh a+v-tanh (a+v)) v := by
      have h := ((hasDerivAt_cosh (a+v)).log (cosh_pos _).ne').comp v ((hasDerivAt_id' v).const_add a)
      convert (((hasDerivAt_id' v).mul_const (tanh a)).add (((hasDerivAt_id' v).pow 2).div_const 2)).sub
        (h.sub_const (log (cosh a))) using 1
      · rfl
      · simp only [tanh_eq_sinh_div_cosh]; ring
    have h := nonneg_from_zero D (by simp) slope hx
    linarith only [h]
  rcases le_total 0 w with hw|hw
  · exact pos u w hw
  · simpa only [show -u+-w = -(u+w) by ring,cosh_neg,tanh_neg,neg_mul_neg,neg_sq] using
      pos (-u) (-w) (neg_nonneg.mpr hw)

/-- Concavity on the positive half-line bounds the drift at each label
below by its proportion of the largest-label drift. -/
theorem tanh_chord {h a : ℝ} (hh : 0 ≤ h) (ha : 0 ≤ a) (ha' : a ≤ 1) :
    a*tanh h ≤ tanh (a*h) := by
  have diff : Differentiable ℝ tanh := fun x => (tanh_deriv x).differentiableAt
  have hm := monotone_of_hasDerivAt_nonneg tanh_deriv (fun x => sub_nonneg.mpr (tanh_sq_lt_one x).le)
  have hconc : ConcaveOn ℝ (Ici 0) tanh := by
    apply AntitoneOn.concaveOn_of_deriv (convex_Ici _) diff.continuous.continuousOn diff.differentiableOn
    intro x hx z _ hxz
    have hpos : 0 ≤ tanh x := by simpa using hm (show 0 ≤ x from interior_subset hx)
    rw [(tanh_deriv x).deriv,(tanh_deriv z).deriv]
    exact sub_le_sub_left (pow_le_pow_left₀ hpos (hm hxz) 2) _
  simpa only [smul_eq_mul,mul_zero,add_zero,tanh_zero] using
    hconc.2 hh (show (0:ℝ) ∈ Ici 0 by simp) ha (sub_nonneg.mpr ha') (show a+(1-a)=1 by ring)

private theorem log_cosh_lower (x : ℝ) : x^2/2-x^4/12 ≤ log (cosh x) := by
  rcases le_total 0 x with hx|hx
  · exact log_cosh_lower_pos hx
  · simpa [show (-x)^4 = x^4 by ring] using log_cosh_lower_pos (neg_nonneg.mpr hx)

theorem linear_sum_sq (c u : ℝ) (t : ℕ) : ∑ i ∈ Finset.range t, (u-c*i)^2 =
    t*u^2-c*u*t*((t:ℝ)-1)+c^2*t*(t-1)*(2*t-1)/6 := by
  induction t with
  | zero => simp
  | succ t ih => rw [Finset.sum_range_succ,ih,Nat.cast_succ]; ring

/-- The largest absolute natural parameter is cd at first-hit time 2d+1.
The bound follows after summing all squared parameters exactly. -/
theorem centered_cosh_lower (c : ℝ) (d : ℕ) :
    exp (c^2*d*(d+1)*(2*d+1)/6*(1-(c*d)^2/6)) ≤ coshProduct c (c*d) (2*d+1) := by
  let t := 2*d+1
  let u := fun i : ℕ => c*(d:ℝ)-c*i
  have hsq : (∑ i ∈ Finset.range t, (u i)^2) = c^2*d*(d+1)*(2*d+1)/3 := by
    rw [linear_sum_sq]
    dsimp [t]; push_cast; ring
  have he (i : ℕ) (hi : i ∈ Finset.range t) :
      (u i)^2/2*(1-(c*d)^2/6) ≤ log (cosh (u i)) := by
    apply le_trans _ (log_cosh_lower _)
    have hd : (i:ℝ) ≤ 2*d := by exact_mod_cast (show i ≤ 2*d by have := Finset.mem_range.mp hi; dsimp [t] at this; omega)
    have h0 := Nat.cast_nonneg (α := ℝ) i
    have h1 : ((d:ℝ)-i)^2 ≤ (d:ℝ)^2 := by nlinarith only [mul_nonneg h0 (sub_nonneg.mpr hd)]
    have hh := mul_le_mul_of_nonneg_left h1 (sq_nonneg c)
    have hh' : (u i)^2 ≤ (c*d)^2 := by dsimp [u]; nlinarith only [hh]
    nlinarith only [mul_nonneg (sq_nonneg (u i)) (sub_nonneg.mpr hh')]
  have h := Finset.sum_le_sum he
  simp only [div_eq_mul_inv,← Finset.sum_mul,hsq] at h
  have hp := exp_le_exp.mpr h
  rw [Real.exp_sum] at hp
  simp only [exp_log (cosh_pos _)] at hp
  change _ ≤ ∏ i ∈ Finset.range t, cosh (u i)
  apply le_trans _ hp
  apply exp_le_exp.mpr
  exact le_of_eq (by ring)

end CentralUnimodality.MarkedExcursion
