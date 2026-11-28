module

public import CentralUnimodality.SplitFirstCorrection
public import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-! The corrected discrete split in lattice scaling. The derivative
bounds may be chosen separately at each time v. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit

open Set Polynomial

theorem cubic_of_fourth {g : ℝ → ℝ} (hg : ContDiff ℝ 4 g) {K : ℝ}
    (hK : ∀ x∈Icc (0:ℝ) 1, |iteratedDeriv 4 g x|≤K) :
    CubicRemainder g (iteratedDeriv 1 g) (iteratedDeriv 2 g) (iteratedDeriv 3 g) K := by
  intro x hx y hy
  by_cases eq : x=y
  · subst y; simp
  let s := uIcc x y
  obtain ⟨t,ht,h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n:=3) eq (hg.contDiffOn (s:=s))
  have der (k : ℕ) (hk : k≤3) : iteratedDerivWithin k g s x=iteratedDeriv k g x := by
    apply iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc eq) _ left_mem_uIcc
    apply (hg.of_le _).contDiffAt
    exact_mod_cast (show k≤4 by omega)
  have poly : taylorWithinEval g 3 s x y=g x+iteratedDeriv 1 g x*(y-x)+
      iteratedDeriv 2 g x/2*(y-x)^2+iteratedDeriv 3 g x/6*(y-x)^3 := by
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,smul_eq_mul]
    rw [der 0 (by decide),der 1 (by decide),der 2 (by decide),der 3 (by decide)]
    norm_num [Nat.factorial]; ring
  change g y-taylorWithinEval g 3 s x y=_ at h
  rw [poly] at h
  rw [h,abs_div,abs_mul,abs_pow]
  have b := hK t (uIcc_subset_Icc hx hy (Ioo_subset_Icc_self ht))
  have nn : 0≤(y-x)^4 := by positivity
  norm_num [Nat.factorial,show |y-x|^4=(y-x)^4 by rw [← abs_pow,abs_of_nonneg nn]]
  linarith only [mul_le_mul_of_nonneg_right b nn]

theorem split_space_second (B F : ℝ[X]) (v : ℝ) :
    iteratedDeriv 2 (splitFactor B F v)=splitSpace2 B F v := by
  have first (P Q : ℝ[X]) : deriv (splitFactor P Q v)=fun x =>
      v*(splitFactor (derivative P) Q v x-splitFactor P (derivative Q) v x) :=
    funext fun x => (split_space_derivative P Q v x).deriv
  rw [iteratedDeriv_succ,iteratedDeriv_one,first]
  funext x
  have d := (((split_space_derivative (derivative B) F v x).sub
    (split_space_derivative B (derivative F) v x)).const_mul v).deriv
  apply d.trans; unfold splitSpace2; ring

theorem sample_split_corrected (B F : ℝ[X]) {j : ℕ} (hj : 0<j) {τ v M K : ℝ}
    (hv : v=j*τ) (k0 : 0≤K)
    (third : ∀ x∈Icc (0:ℝ) 1, |iteratedDeriv 3 (splitFactor B F v) x|≤v^3*M)
    (fourth : ∀ x∈Icc (0:ℝ) 1, |iteratedDeriv 4 (splitFactor B F v) x|≤v^4*K) :
    |sample j (splitFactor B F v)-(betaProduct B F).eval v-
      τ*((fullDrift (betaProduct B F)).eval v-(betaProduct (halfDrift B) F+betaProduct B (halfDrift F)).eval v)|
      ≤τ^2*(v*M/24+v^2*K/128) := by
  have smooth (P : ℝ[X]) : ContDiff ℝ 4 (fun x => P.eval x) := by simpa using P.contDiff_aeval (𝕜:=ℝ) 4
  have hg : ContDiff ℝ 4 (splitFactor B F v) :=
    ((smooth B).comp (contDiff_const.mul contDiff_id)).mul
      ((smooth F).comp (contDiff_const.mul (contDiff_const.sub contDiff_id)))
  have he : Continuous (iteratedDeriv 2 (splitFactor B F v)) := hg.continuous_iteratedDeriv 2 (by norm_num)
  have H := sample_corrected_arc hj hg.continuous he (mul_nonneg (by positivity) k0) third
    (cubic_of_fourth hg fourth)
  rw [split_space_second,split_first_correction] at H
  rw [show arc (splitFactor B F v)=(betaProduct B F).eval v from arc_polynomial v B F] at H
  have jp : (j:ℝ)≠0 := Nat.cast_ne_zero.mpr hj.ne'
  rw [show 1/(2*(j:ℝ))*(2*v*((fullDrift (betaProduct B F)).eval v-
    (betaProduct (halfDrift B) F+betaProduct B (halfDrift F)).eval v))=
    τ*((fullDrift (betaProduct B F)).eval v-(betaProduct (halfDrift B) F+betaProduct B (halfDrift F)).eval v)
    by rw [hv]; field_simp] at H
  apply H.trans_eq
  rw [hv]; field_simp

end CentralUnimodality.ReturnSplit
