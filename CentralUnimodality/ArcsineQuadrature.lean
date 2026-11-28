module

public import CentralUnimodality.ArcsineSplit
public import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! The finite split law is a binomial mixture over the arcsine law.
A second-order remainder on the unit interval controls the error at
every positive sample size. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit

open Polynomial

noncomputable def splitBasis (N k : ℕ) (x : ℝ) : ℝ :=
  (N.choose k:ℝ)*x^k*(1-x)^(N-k)

theorem arc_splitBasis (N k : ℕ) (h : k≤N) : arc (splitBasis N k)=weight N k := by
  have eq : splitBasis N k=fun x : ℝ => (N.choose k:ℝ)*(x^k*(1-x)^(N-k)) := by
    funext x; dsimp [splitBasis]; ring
  rw [eq,arc_const_mul,arc_mixed,betaWeight,weight,Nat.add_sub_of_le h]
  have id : (N.choose k:ℝ)*k.factorial*(N-k).factorial=N.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial h
  field_simp
  linear_combination survival k*survival (N-k)*id

noncomputable def binomialSample (N : ℕ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ k : Fin (N+1), g ((k:ℕ)/ (N:ℝ))*splitBasis N k x

theorem continuous_binomialSample (N : ℕ) (g : ℝ → ℝ) : Continuous (binomialSample N g) := by
  unfold binomialSample splitBasis
  fun_prop

theorem arc_binomialSample (N : ℕ) (g : ℝ → ℝ) : arc (binomialSample N g)=sample N g := by
  unfold binomialSample sample average
  rw [arc_sum _ _ (by intro k _; dsimp [splitBasis]; fun_prop),Finset.sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [arc_const_mul,arc_splitBasis _ _ k.is_le,mul_comm]

private theorem basis_agrees (N k : ℕ) (x : unitInterval) :
    splitBasis N k x=bernstein N k x := (bernstein_apply ..).symm

private theorem centered_mean {N : ℕ} (hN : 0<N) (x : unitInterval) :
    ∑ k : Fin (N+1), (bernstein.z k-(x:ℝ))*bernstein N k x=0 := by
  have m := congrArg (fun p : ℝ[X] => p.eval (x:ℝ)) (bernsteinPolynomial.sum_smul ℝ N)
  simp only [eval_finsetSum,nsmul_eq_mul,eval_mul,eval_natCast,eval_X,Finset.sum_range] at m
  change ∑ k : Fin (N+1), (k:ℝ)*bernstein N k x=(N:ℝ)*x at m
  simp only [bernstein.z,sub_mul,Finset.sum_sub_distrib,← Finset.mul_sum,bernstein.probability,mul_one]
  simp_rw [div_mul_eq_mul_div,← Finset.sum_div,m]
  field_simp
  ring

theorem binomialSample_error {N : ℕ} (hN : 0<N) (g slope : ℝ → ℝ) {M : ℝ} (hM : 0≤M)
    (hr : QuadraticRemainder g slope M) (x : unitInterval) :
    |binomialSample N g x-g x| ≤ M/(8*(N:ℝ)) := by
  let H := fun k : Fin (N+1) => g (bernstein.z k)-g x-((bernstein.z k:ℝ)-x)*slope x
  have eq : binomialSample N g x-g x=∑ k, H k*bernstein N k x := by
    have lin : (∑ k : Fin (N+1), (((bernstein.z k:ℝ)-x)*slope x)*bernstein N k x)=0 := by
      simp_rw [mul_right_comm _ (slope x),← Finset.sum_mul,centered_mean hN,zero_mul]
    simp only [H,sub_mul,Finset.sum_sub_distrib,← Finset.mul_sum,
      bernstein.probability,mul_one,binomialSample,basis_agrees,bernstein.z] at lin ⊢
    linarith only [lin]
  have var := bernstein.variance hN.ne' x
  have v₀ : 0<(N:ℝ) := by exact_mod_cast hN
  rw [eq]
  calc
    _ ≤ ∑ k : Fin (N+1), |H k*bernstein N k x| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ k : Fin (N+1), (M/2)*((((x:ℝ)-bernstein.z k)^2)*bernstein N k x) := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul,abs_of_nonneg bernstein_nonneg,← mul_assoc,sub_sq_comm]
      exact mul_le_mul_of_nonneg_right (hr x x.2 _ (bernstein.z k).2) bernstein_nonneg
    _ = (M/2)*((x:ℝ)*(1-x)/N) := by rw [← Finset.mul_sum,var]
    _ ≤ _ := by
      have hv : (x:ℝ)*(1-x)≤1/4 := by nlinarith only [sq_nonneg (2*(x:ℝ)-1)]
      have hb := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hv v₀.le) (by positivity : 0≤M/2)
      exact hb.trans_eq (by ring)

theorem sample_arc_bound {N : ℕ} (hN : 0<N) {g slope : ℝ → ℝ} {M : ℝ}
    (hg : Continuous g) (hM : 0≤M) (hr : QuadraticRemainder g slope M) :
    |sample N g-arc g|≤M/(8*(N:ℝ)) := by
  rw [← arc_binomialSample,← arc_sub (continuous_binomialSample ..) hg]
  apply arc_bound
  intro x hx
  exact binomialSample_error hN _ _ hM hr ⟨x,hx⟩

end CentralUnimodality.ReturnSplit
