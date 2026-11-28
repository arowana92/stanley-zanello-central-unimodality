module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A global Taylor bound for the cosine. Its first omitted even
moment controls the characteristic-function error after averaging. -/
@[expose] public section

namespace CentralUnimodality
open Real

def cosineCoefficient (j : ℕ) : ℚ := (-1:ℚ)^j/(2*j).factorial

noncomputable def cosineTaylor (h : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (h+1), (cosineCoefficient j:ℝ)*x^(2*j)

private theorem sum_even_terms (f : ℕ → ℝ) (h : ∀ j, f (2*j+1)=0) (n : ℕ) :
    (∑ k ∈ Finset.range (2*n), f k)=∑ j ∈ Finset.range n, f (2*j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega,Finset.sum_range_succ,Finset.sum_range_succ,h,
      add_zero,ih,Finset.sum_range_succ (n:=n)]

theorem cosine_remainder (h : ℕ) (x : ℝ) :
    |cos x-cosineTaylor h x| ≤ |x|^(2*(h+1))/(2*(h+1)).factorial := by
  by_cases hz : x=0
  · subst x
    simp [cosineTaylor,Finset.sum_range_succ',cosineCoefficient]
  have nz := Ne.symm hz
  let s := Set.uIcc 0 x
  have t := taylor_mean_remainder_lagrange_iteratedDeriv (n:=2*h+1) nz
    (Real.contDiff_cos.contDiffOn (s:=s))
  obtain ⟨y,_,hy⟩ := t
  have der (k : ℕ) : iteratedDerivWithin k cos s 0=iteratedDeriv k cos 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc nz) Real.contDiff_cos.contDiffAt Set.left_mem_uIcc
  let f := fun k : ℕ => ((k.factorial:ℝ)⁻¹*x^k)*iteratedDeriv k cos 0
  have hodd (j : ℕ) : f (2*j+1)=0 := by simp [f]
  have hsum : taylorWithinEval cos (2*h+1) s 0 x=cosineTaylor h x := by
    rw [taylor_within_apply]
    simp only [sub_zero,smul_eq_mul,der]
    change (∑ k ∈ Finset.range (2*h+1+1), f k)=_
    rw [show 2*h+1+1=2*(h+1) by omega,sum_even_terms f hodd,cosineTaylor]
    apply Finset.sum_congr rfl
    intro j _
    simp [f,cosineCoefficient,div_eq_mul_inv]
    ring
  change cos x-taylorWithinEval cos (2*h+1) s 0 x=_ at hy
  rw [hsum,show 2*h+1+1=2*(h+1) by omega,iteratedDeriv_even_cos] at hy
  rw [hy]
  simp only [sub_zero,Pi.mul_apply,Pi.pow_apply,Pi.neg_apply,Pi.one_apply,abs_div,
    abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul, Nat.abs_cast]
  exact div_le_div_of_nonneg_right (mul_le_of_le_one_left (by positivity) (abs_cos_le_one _)) (by positivity)

end CentralUnimodality
