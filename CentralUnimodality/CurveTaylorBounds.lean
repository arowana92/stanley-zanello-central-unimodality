module

public import CentralUnimodality.PolynomialGaussianInputs
public import CentralUnimodality.ContinuumResidual
import Mathlib.Algebra.Order.Group.Pointwise.Interval

/-! A quadratic Taylor bound for the true bridge cubic multiplied by
the specific polynomial trial. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Real Set ReturnSplit

theorem interval_lipschitz {g d : ℝ → ℝ} (hg : ∀ z, HasDerivAt g (d z) z)
    {s : Set ℝ} (hs : Convex ℝ s) {M : ℝ} (bound : ∀ z∈s, |d z|≤M)
    {x y : ℝ} (hx : x∈s) (hy : y∈s) : |g y-g x|≤M*|y-x| := by
  simpa only [Real.norm_eq_abs] using hs.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (hg z).hasDerivWithinAt) (fun z hz => by simpa only [Real.norm_eq_abs] using bound z hz) hx hy

theorem quadratic_from_second {g d dd : ℝ → ℝ} (hg : ∀ z, HasDerivAt g (d z) z)
    (hd : ∀ z, HasDerivAt d (dd z) z) {M : ℝ} (hM : 0≤M) (bound : ∀ z∈Icc 0 1, |dd z|≤M) :
    QuadraticRemainder g d (2*M) := by
  intro x hx y hy
  let f := fun z => g z-z*d x
  have df (z : ℝ) : HasDerivAt f (d z-d x) z := by
    convert (hg z).sub ((hasDerivAt_id z).mul_const (d x)) using 1
    · rfl
    · simp
  have lip (z : ℝ) (hz : z∈uIcc x y) : |d z-d x|≤M*|y-x| :=
    (interval_lipschitz hd (convex_Icc ..) bound hx (uIcc_subset_Icc hx hy hz)).trans
      (mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc hz) hM)
  have est := interval_lipschitz df (convex_Icc ..) lip left_mem_uIcc right_mem_uIcc
  rw [show f y-f x=g y-g x-(y-x)*d x by dsimp [f]; ring] at est
  apply est.trans_eq
  rw [mul_assoc,← sq, sq_abs]; ring

theorem trial_hasDeriv (v : ℝ) : HasDerivAt (value candidate) (deriv (value candidate) v) v :=
  (value_hasDerivAt candidate v).differentiableAt.hasDerivAt

theorem trial_second (v : ℝ) :
    HasDerivAt (deriv (value candidate)) (deriv (deriv (value candidate)) v) v := by
  apply DifferentiableAt.hasDerivAt
  have D : deriv (value candidate)=fun x => -value (derivativeRow 0 candidate) x/128 :=
    funext (fun x => (value_hasDerivAt candidate x).deriv)
  rw [D]; exact ((value_hasDerivAt _ v).differentiableAt.neg.div_const _)

private noncomputable def bridgeSlope (x : ℝ) : ℝ := -(x^2/32)*bridgeCurve x
private noncomputable def bridgeSecond (x : ℝ) : ℝ := ((x^2/32)^2-x/16)*bridgeCurve x

theorem bridge_hasDeriv (x : ℝ) : HasDerivAt bridgeCurve (-(x^2/32)*bridgeCurve x) x := by
  have inner : HasDerivAt (fun t : ℝ => -(t^3/96)) (-(x^2/32)) x := by
    convert (((hasDerivAt_id x).pow 3).div_const 96).neg using 1
    · rfl
    · simp; ring
  convert inner.exp using 1
  · rfl
  · change -(x^2/32)*exp (-(x^3/96))=_
    ring

private theorem bridge_second (x : ℝ) : HasDerivAt bridgeSlope (bridgeSecond x) x := by
  have dg : HasDerivAt (fun t : ℝ => -(t^2/32)) (-(x/16)) x := by
    convert (((hasDerivAt_id x).pow 2).div_const 32).neg using 1
    · rfl
    · simp; ring
  convert dg.mul (bridge_hasDeriv x) using 1
  · rfl
  · unfold bridgeSecond; ring

private theorem bridge_bounds {x : ℝ} (hx : x∈Icc (0:ℝ) 256) :
    |bridgeCurve x|≤1 ∧ |bridgeSlope x|≤2048 ∧ |bridgeSecond x|≤4194320 := by
  have gauss : |bridgeCurve x|≤1 := by
    rw [bridgeCurve,abs_of_pos (exp_pos _),exp_le_one_iff]
    exact neg_nonpos.mpr (by have := hx.1; positivity)
  have sqbound : x^2/32≤2048 := by
    have h := pow_le_pow_left₀ hx.1 hx.2 2; linarith only [h]
  have nn : 0≤x^2/32 := by positivity
  refine ⟨gauss,?_,?_⟩
  · rw [bridgeSlope,abs_mul,abs_neg,abs_of_nonneg nn]
    exact (mul_le_mul sqbound gauss (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  · rw [bridgeSecond,abs_mul]
    apply (mul_le_mul_of_nonneg_left gauss (abs_nonneg _)).trans
    rw [mul_one]
    apply (abs_sub ..).trans
    rw [abs_of_nonneg (sq_nonneg _),abs_of_nonneg (div_nonneg hx.1 (by norm_num))]
    have h := pow_le_pow_left₀ nn sqbound 2
    linarith only [h,hx.2]

theorem split_quadratic {v : ℝ} (hv : v∈Icc (0:ℝ) 256) :
    ∃ slope, QuadraticRemainder (splitCurve (value candidate) v) slope (18000000*v^2) := by
  let f := value candidate
  let d := deriv f
  let dd := deriv d
  let x₁ := fun x : ℝ => v*x
  let x₂ := fun x : ℝ => v*(1-x)
  let D := fun x => v*(bridgeSlope (x₁ x)*f (x₂ x)-bridgeCurve (x₁ x)*d (x₂ x))
  let DD := fun x => v^2*(bridgeSecond (x₁ x)*f (x₂ x)-2*bridgeSlope (x₁ x)*d (x₂ x)+bridgeCurve (x₁ x)*dd (x₂ x))
  have dx (x : ℝ) : HasDerivAt x₁ v x := by simpa [x₁] using (hasDerivAt_id x).const_mul v
  have dy (x : ℝ) : HasDerivAt x₂ (-v) x := by
    simpa [x₂] using ((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).const_mul v
  have dg (x : ℝ) : HasDerivAt (splitCurve f v) (D x) x := by
    have H := ((bridge_hasDeriv _).comp x (dx x)).mul ((trial_hasDeriv _).comp x (dy x))
    convert H using 1
    · rfl
    · dsimp [D,bridgeSlope,f,d,Function.comp_def]; ring
  have d2 (x : ℝ) : HasDerivAt D (DD x) x := by
    have L := ((bridge_second _).comp x (dx x)).mul ((trial_hasDeriv _).comp x (dy x))
    have R := ((bridge_hasDeriv _).comp x (dx x)).mul ((trial_second _).comp x (dy x))
    convert (L.sub R).const_mul v using 1
    · rfl
    · dsimp [DD,bridgeSlope,f,d,dd,Function.comp_def]; ring
  refine ⟨D,?_⟩
  rw [show 18000000*v^2=2*(9000000*v^2) by ring]
  apply quadratic_from_second dg d2 (by positivity)
  intro x hx
  have dom {t : ℝ} (ht : t∈Icc (0:ℝ) 1) : v*t∈Icc (0:ℝ) 256 :=
    ⟨mul_nonneg hv.1 ht.1,(mul_le_mul_of_nonneg_left ht.2 hv.1).trans_eq (mul_one v) |>.trans hv.2⟩
  have ⟨B,B1,B2⟩ := bridge_bounds (dom hx)
  have ⟨F,F1,F2⟩ := candidate_bounds (dom (show 1-x∈Icc 0 1 by constructor <;> linarith only [hx.1,hx.2]))
  change |v^2*(_-_+_)|≤_
  rw [abs_mul,abs_of_nonneg (sq_nonneg _),mul_comm (9000000:ℝ)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply (abs_add_le ..).trans
  apply (add_le_add (abs_sub ..) le_rfl).trans
  simp only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  change _≤(9000000:ℝ)
  have l := mul_le_mul B2 F (abs_nonneg _) (by norm_num)
  have m := mul_le_mul B1 F1 (abs_nonneg _) (by norm_num)
  have r := mul_le_mul B F2 (abs_nonneg _) (by norm_num)
  dsimp only [x₁,x₂,dd,d,f] at *
  linarith only [l,m,r]

end CentralUnimodality.PolynomialTrial
