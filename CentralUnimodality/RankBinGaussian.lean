module

public import CentralUnimodality.RankSignAssembly
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! The one-sided Gaussian Taylor estimate and the small exponential step
in the right-flank growth and curvature tests. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

theorem gaussian_cubic_lower (x : ℝ) : 1-x+x^2/2-x^3/6 ≤ exp (-x) := by
  by_cases hx : x=0
  · subst x; norm_num
  let F := fun y : ℝ => exp (-1*y)
  have smooth (n : ℕ) : ContDiff ℝ n F := by dsimp [F]; fun_prop
  have hx' : (0:ℝ)≠x := Ne.symm hx
  obtain ⟨z,_,H⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n:=3) hx' (smooth 4).contDiffOn
  have pol : taylorWithinEval F 3 (Set.uIcc 0 x) 0 x = 1-x+x^2/2-x^3/6 := by
    rw [taylor_within_apply]
    have deriv (k : ℕ) : iteratedDerivWithin k F (Set.uIcc 0 x) 0=(-1:ℝ)^k := by
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx') (smooth k).contDiffAt Set.left_mem_uIcc]
      simp only [F,iteratedDeriv_exp_const_mul,mul_zero,exp_zero,mul_one]
    simp only [deriv]
    norm_num [Finset.sum_range_succ,Nat.factorial]; ring
  rw [pol] at H
  have hfour : 0 ≤ iteratedDeriv 4 F z := by rw [iteratedDeriv_exp_const_mul]; positivity
  have he : F x=exp (-x) := by simp [F]
  rw [he] at H
  have h := mul_nonneg hfour (show 0 ≤ (x-0)^4 by positivity)
  norm_num [Nat.factorial] at H h
  linarith only [H,h]

theorem tiny_tilt_step {x : ℝ} (hx : 0 ≤ x) (hhi : x ≤ 1/1000) :
    (999/1000)*x ≤ 1-exp (-x) := by
  rw [exp_neg,le_sub_comm,← one_div,div_le_iff₀ (exp_pos _)]
  have hpos : 0 ≤ 1-(999/1000)*x := by linarith only [hhi]
  have H := mul_le_mul_of_nonneg_left (add_one_le_exp x) hpos
  nlinarith only [H,mul_nonneg hx (sub_nonneg.mpr hhi),hx]

theorem bin_gaussian_comparison {V B : ℝ} (hV : 0 ≤ V) (hB : 0 ≤ B) (hVB : V ≤ B) :
    let x := B/2
    let E := 1-x+x^2/2-x^3/6
    E ≤ exp (-V/2) ∧ V/(1+V/2)-exp (-V/2) ≤ B/(1+B/2)-E := by
  have he := (gaussian_cubic_lower (B/2)).trans (exp_le_exp.mpr (by linarith : -(B/2) ≤ -V/2))
  have hmono : V/(1+V/2) ≤ B/(1+B/2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    linarith only [hVB]
  exact ⟨he,sub_le_sub hmono he⟩

end CentralUnimodality.MarkedExcursion
