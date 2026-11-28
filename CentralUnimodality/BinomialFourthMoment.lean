module

public import CentralUnimodality.ArcsineQuadrature
import Mathlib.Data.Nat.Choose.Sum

/-! Exact centered moments of the binomial law used in the last-return
quadrature. These identify the first finite-size correction to the arcsine split. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit

open Finset

noncomputable def countMean (n : ℕ) (x : ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ range (n+1), splitBasis n k x*f k

theorem countMean_step (n : ℕ) (x : ℝ) (f : ℕ → ℝ) :
    countMean (n+1) x f=countMean n x (fun k => (1-x)*f k+x*f (k+1)) := by
  let g := fun i j : ℕ => x^i*(1-x)^j*f i
  have rep (m : ℕ) : countMean m x f=∑ k ∈ range (m+1), (m.choose k:ℝ)*g k (m-k) := by
    unfold countMean
    apply sum_congr rfl
    intro k _; dsimp [g,splitBasis]; ring
  rw [rep,Finset.sum_choose_succ_mul,← sum_add_distrib,countMean]
  apply sum_congr rfl
  intro k hk
  have d : n+1-k=(n-k)+1 := by have := mem_range.mp hk; omega
  dsimp [g,splitBasis]; rw [d,pow_succ,pow_succ]; ring

noncomputable def centered (n : ℕ) (x : ℝ) (r : ℕ) :=
  countMean n x (fun k => ((k:ℝ)-n*x)^r)

private theorem countMean_one (n : ℕ) (x : ℝ) : countMean n x (fun _ => 1)=1 := by
  induction n with
  | zero => simp [countMean,splitBasis]
  | succ n ih => rw [countMean_step]; simpa using ih

private theorem countMean_add (n : ℕ) (x : ℝ) (f g : ℕ → ℝ) :
    countMean n x (fun k => f k+g k)=countMean n x f+countMean n x g := by
  simp [countMean,mul_add,Finset.sum_add_distrib]

private theorem countMean_mul (n : ℕ) (x c : ℝ) (f : ℕ → ℝ) :
    countMean n x (fun k => c*f k)=c*countMean n x f := by
  simp only [countMean,Finset.mul_sum]; apply sum_congr rfl
  intro i _; ring

private theorem countMean_const (n : ℕ) (x c : ℝ) : countMean n x (fun _ => c)=c := by
  simpa [countMean_one] using countMean_mul n x c (fun _ => 1)

theorem centered_low (n : ℕ) (x : ℝ) :
    centered n x 1=0 ∧ centered n x 2=n*(x*(1-x)) ∧
    centered n x 3=n*(x*(1-x))*(1-2*x) ∧
    centered n x 4=3*n^2*(x*(1-x))^2+n*(x*(1-x))*(1-6*(x*(1-x))) := by
  induction n with
  | zero => norm_num [centered,countMean,splitBasis]
  | succ n ih =>
    let z := fun k : ℕ => (k:ℝ)-n*x
    let q := x*(1-x)
    let f := fun (r k : ℕ) => (z k)^r
    have step (r : ℕ) : centered (n+1) x r=countMean n x (fun k => (1-x)*(z k-x)^r+x*(z k+(1-x))^r) := by
      rw [centered,countMean_step]; congr 1; funext k; dsimp [z]; push_cast; ring
    have e1 (k : ℕ) : (1-x)*(z k-x)^1+x*(z k+(1-x))^1=f 1 k := by dsimp [f]; ring
    have e2 (k : ℕ) : (1-x)*(z k-x)^2+x*(z k+(1-x))^2=f 2 k+q := by dsimp [f,q]; ring
    have e3 (k : ℕ) : (1-x)*(z k-x)^3+x*(z k+(1-x))^3=f 3 k+(3*q)*f 1 k+q*(1-2*x) := by dsimp [f,q]; ring
    have e4 (k : ℕ) : (1-x)*(z k-x)^4+x*(z k+(1-x))^4=
        f 4 k+(6*q)*f 2 k+(4*q*(1-2*x))*f 1 k+q*(1-3*q) := by dsimp [f,q]; ring
    have id (r : ℕ) : countMean n x (f r)=centered n x r := rfl
    simp_rw [step,e1,e2,e3,e4]
    simp only [countMean_add,countMean_mul,countMean_const,id,ih.1,ih.2.1,ih.2.2.1,ih.2.2.2,q,Nat.cast_succ]
    constructor
    · trivial
    · constructor
      · ring
      · constructor <;> ring

theorem scaled_centered {n : ℕ} (hn : 0<n) (x : ℝ) (r : ℕ) :
    binomialSample n (fun y => (y-x)^r) x=centered n x r/(n:ℝ)^r := by
  have nz : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  simp only [binomialSample,centered,countMean,Finset.sum_range,Finset.sum_div]
  apply sum_congr rfl
  intro k _
  rw [show (k.val:ℝ)/n-x=((k.val:ℝ)-n*x)/n by field_simp,div_pow]
  ring

end CentralUnimodality.ReturnSplit
