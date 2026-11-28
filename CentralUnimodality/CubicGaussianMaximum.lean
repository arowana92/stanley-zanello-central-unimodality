module

public import CentralUnimodality.ScaledNegativeExp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Endpoint and interior estimates for the monomials in each Gaussian
derivative. At an interior maximum the cube of the estimate removes
the cube root. The global bound follows from `z ≤ exp (z-1)`. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Real Set

noncomputable def gaussianTerm (b : ℝ) (j : ℕ) (v : ℝ) := v^j*exp (-(v^3/b))

private theorem gaussian_derivative (b : ℝ) (j : ℕ) (v : ℝ) :
    HasDerivAt (gaussianTerm b (j+1)) (gaussianTerm b j v*((j:ℝ)+1-3*v^3/b)) v := by
  have d := (hasDerivAt_pow (j+1) v).mul (((hasDerivAt_pow 3 v).div_const b).neg.exp)
  convert d using 1
  · rfl
  · simp only [gaussianTerm,Pi.neg_apply,Nat.cast_succ,Nat.add_sub_cancel,pow_succ]
    ring

theorem gaussian_left {b l v : ℝ} {j : ℕ} (hb : 0<b) (hl : 0≤l) (lv : l≤v)
    (h : (j:ℝ)*b≤3*l^3) : gaussianTerm b j v≤gaussianTerm b j l := by
  cases j with
  | zero =>
    simp only [gaussianTerm,pow_zero,one_mul,exp_le_exp,neg_le_neg_iff]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hl lv 3) hb.le
  | succ j =>
    have d := gaussian_derivative b j
    have smooth : Differentiable ℝ (gaussianTerm b (j+1)) := fun x => (d x).differentiableAt
    have mono : AntitoneOn (gaussianTerm b (j+1)) (Ici l) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici _) smooth.continuous.continuousOn smooth.differentiableOn
      intro x hx
      have xl : l≤x := interior_subset hx
      rw [(d x).deriv]
      apply mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (pow_nonneg (hl.trans xl) j) (exp_nonneg _))
      apply sub_nonpos.mpr
      apply (le_div_iff₀ hb).mpr
      push_cast at h
      linarith only [h,pow_le_pow_left₀ hl xl 3]
    exact mono le_rfl lv lv

theorem gaussian_right {b v u : ℝ} {j : ℕ} (hb : 0<b) (hv : 0≤v) (vu : v≤u)
    (h : 3*u^3≤(j:ℝ)*b) : gaussianTerm b j v≤gaussianTerm b j u := by
  cases j with
  | zero =>
    have uz : u=0 := by
      by_contra ne
      have up := lt_of_le_of_ne (hv.trans vu) (Ne.symm ne)
      simp only [Nat.cast_zero,zero_mul] at h
      linarith only [h,pow_pos up 3]
    have vz : v=0 := by linarith
    rw [uz,vz]
  | succ j =>
    have d := gaussian_derivative b j
    have smooth : Differentiable ℝ (gaussianTerm b (j+1)) := fun x => (d x).differentiableAt
    have mono : MonotoneOn (gaussianTerm b (j+1)) (Icc 0 u) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc ..) smooth.continuous.continuousOn smooth.differentiableOn
      intro x hx
      have xp : x∈Icc 0 u := interior_subset hx
      rw [(d x).deriv]
      apply mul_nonneg (mul_nonneg (pow_nonneg xp.1 j) (exp_nonneg _))
      apply sub_nonneg.mpr
      apply (div_le_iff₀ hb).mpr
      push_cast at h
      linarith only [h,pow_le_pow_left₀ xp.1 xp.2 3]
    exact mono ⟨hv,vu⟩ ⟨hv.trans vu,le_rfl⟩ vu

theorem gaussian_global_cube {b v : ℝ} {j : ℕ} (hb : 0<b) (hv : 0≤v) (hj : 0<j) :
    (gaussianTerm b j v)^3≤(b*j/(3*2.71))^j := by
  have jp : 0<(j:ℝ) := by exact_mod_cast hj
  let z := 3*v^3/(b*j)
  have ze : z*exp (-z)≤exp (-1) := by
    have e := add_one_le_exp (z-1)
    have m := mul_le_mul_of_nonneg_right (by linarith only [e] : z≤exp (z-1)) (exp_nonneg (-z))
    rwa [← exp_add,show z-1+-z= -1 by ring] at m
  have eq : v^3=(b*j/3)*z := by dsimp [z]; field_simp
  have factor : v^3*exp (-z)≤b*j/(3*2.71) := by
    have e : exp (-1)≤1/2.71 := by
      rw [exp_neg,inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith only [exp_one_gt_d9])
    rw [eq,mul_assoc]
    apply (mul_le_mul_of_nonneg_left (ze.trans e) (by positivity : 0≤b*j/3)).trans_eq
    ring
  have power := pow_le_pow_left₀ (mul_nonneg (pow_nonneg hv 3) (exp_nonneg (-z))) factor j
  have ez : (j:ℝ)*(-z)=3*(-(v^3/b)) := by dsimp [z]; field_simp
  unfold gaussianTerm
  rw [mul_pow,← pow_mul,← exp_nat_mul,ez,Nat.mul_comm 3 j] at power
  rw [mul_pow,← pow_mul,← exp_nat_mul]
  exact power

end CentralUnimodality.PolynomialTrial
