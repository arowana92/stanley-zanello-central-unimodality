module

public import CentralUnimodality.SmoothSplitQuadrature

/-! The local quadrature cost for the sum of a leading split and its
order-τ correction. The three derivative bounds are at the current time. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit
open Set

theorem quadratic_of_second {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {K : ℝ}
    (hK : ∀ x∈Icc (0:ℝ) 1, |iteratedDeriv 2 g x|≤K) :
    QuadraticRemainder g (iteratedDeriv 1 g) K := by
  intro x hx y hy
  by_cases eq : x=y
  · subst y; simp
  let s := uIcc x y
  obtain ⟨t,ht,h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n:=1) eq (hg.contDiffOn (s:=s))
  have der : iteratedDerivWithin 1 g s x=iteratedDeriv 1 g x :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc eq) (hg.of_le (by norm_num)).contDiffAt left_mem_uIcc
  have poly : taylorWithinEval g 1 s x y=g x+(y-x)*iteratedDeriv 1 g x := by
    rw [taylor_within_apply]
    simp [Finset.sum_range_succ,der]
  change g y-taylorWithinEval g 1 s x y=_ at h
  rw [poly,← sub_sub] at h
  rw [h,abs_div,abs_mul,abs_pow]
  have b := hK t (uIcc_subset_Icc hx hy (Ioo_subset_Icc_self ht))
  norm_num [Nat.factorial,sq_abs]
  linarith only [mul_le_mul_of_nonneg_right b (sq_nonneg (y-x))]

theorem direct_split_error {j : ℕ} (hj : 0<j) {τ v D₂ D₃ D₄ : ℝ} (hv : v=j*τ) (t0 : 0≤τ)
    (d2 : 0≤D₂) (d4 : 0≤D₄) {g m e : ℝ → ℝ} (hg : ContDiff ℝ 4 g) (hm : ContDiff ℝ 2 m)
    (dd : ∀ x, iteratedDeriv 2 g x=v^2*e x)
    (mixed : ∀ x∈Icc (0:ℝ) 1, |iteratedDeriv 2 m x|≤v^2*D₂)
    (third : ∀ x∈Icc (0:ℝ) 1, |iteratedDeriv 3 g x|≤v^3*D₃)
    (fourth : ∀ x∈Icc (0:ℝ) 1, |iteratedDeriv 4 g x|≤v^4*D₄) :
    |sample j (fun x => g x+τ*m x)-(arc g+τ*(arc m+(v/2)*arc (fun x => x*(1-x)*e x)))|≤
      τ^2*(v*D₂/8+v*D₃/24+v^2*D₄/128) := by
  have cj := (Nat.cast_pos.mpr hj : (0:ℝ)<j)
  have H := sample_corrected_arc hj hg.continuous (hg.continuous_iteratedDeriv 2 (by norm_num))
    (mul_nonneg (by positivity) d4) third (cubic_of_fourth hg fourth)
  have B := sample_arc_bound hj hm.continuous (mul_nonneg (sq_nonneg v) d2) (quadratic_of_second hm mixed)
  have J := mul_le_mul_of_nonneg_left B t0
  have A : (fun x => x*(1-x)*iteratedDeriv 2 g x)=fun x => v^2*(x*(1-x)*e x) := by
    funext x; rw [dd]; ring
  rw [A,arc_const_mul] at H
  rw [show 1/(2*(j:ℝ))*(v^2*arc (fun x => x*(1-x)*e x))=τ*(v/2)*arc (fun x => x*(1-x)*e x)
    by rw [hv]; field_simp] at H
  have S : sample j (fun x => g x+τ*m x)=sample j g+τ*sample j m := by
    simp only [sample,average,mul_add,Finset.sum_add_distrib,Finset.mul_sum]; congr 1
    apply Finset.sum_congr rfl; intro k _; ring
  rw [S,show sample j g+τ*sample j m-(arc g+τ*(arc m+(v/2)*arc (fun x => x*(1-x)*e x)))=
    (sample j g-arc g-τ*(v/2)*arc (fun x => x*(1-x)*e x))+τ*(sample j m-arc m) by ring]
  apply (abs_add_le ..).trans
  rw [abs_mul,abs_of_nonneg t0]
  apply (add_le_add H J).trans_eq
  rw [hv]; field_simp; ring

end CentralUnimodality.ReturnSplit
