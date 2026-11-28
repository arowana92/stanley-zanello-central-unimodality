module

public import CentralUnimodality.LocalJetTable
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! In cell `i`, the correction includes a drift of the main trial.
At order `r` its two terms use orders `r+1` and `r+2` of that trial. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Polynomial ReturnSplit

theorem polynomial_jet (P : ℝ[X]) (r : ℕ) :
    iteratedDeriv r P.eval=(derivative^[r] P).eval := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ,ih,Function.iterate_succ_apply']
    funext x; exact Polynomial.deriv _

private theorem diff_corrected (M F : ℝ[X]) (r : ℕ) :
    derivative^[r] (M+halfDrift F)=
      derivative^[r] M+C (1/2:ℝ)*(C ((r:ℝ)+1)*(derivative^[r+1] F)+X*(derivative^[r+2] F)) := by
  induction r with
  | zero => simp [halfDrift]
  | succ r ih =>
    rw [Function.iterate_succ_apply' derivative r (M+halfDrift F),ih]
    simp only [derivative_add,derivative_mul,derivative_C,derivative_one,derivative_X,one_mul,
      Function.iterate_succ_apply',Nat.cast_succ,C_add,C_1]
    ring

theorem corrected_jet (σ r : ℕ) (v : ℝ) :
    iteratedDeriv r (correctedValue σ) v=iteratedDeriv r (value (correctionCandidate σ)) v+
      (((r:ℝ)+1)*iteratedDeriv (r+1) (value candidate) v+v*iteratedDeriv (r+2) (value candidate) v)/2 := by
  rw [← physical_evaluation,← physical_evaluation]
  change iteratedDeriv r (correctedPoly σ).eval v=_
  rw [polynomial_jet (correctedPoly σ),correctedPoly,diff_corrected]
  simp only [polynomial_jet,eval_add,eval_mul,eval_C,eval_X]
  ring

theorem corrected_jet_bound {σ i r : ℕ} {v : ℝ} (hv : v∈halfInterval i) {M A B : ℝ}
    (hm : |iteratedDeriv r (value (correctionCandidate σ)) v|≤M)
    (ha : |iteratedDeriv (r+1) (value candidate) v|≤A)
    (hb : |iteratedDeriv (r+2) (value candidate) v|≤B) :
    |iteratedDeriv r (correctedValue σ) v|≤M+((r:ℝ)+1)*A/2+((i:ℝ)+1)*B/4 := by
  have v0 : 0≤v := le_trans (by positivity : (0:ℝ)≤(i:ℝ)/2) hv.1
  have ve : v≤((i:ℝ)+1)/2 := by exact_mod_cast hv.2
  rw [corrected_jet]
  apply (abs_add_le ..).trans
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have sum := abs_add_le (((r:ℝ)+1)*iteratedDeriv (r+1) (value candidate) v)
    (v*iteratedDeriv (r+2) (value candidate) v)
  rw [abs_mul,abs_mul,abs_of_nonneg (by positivity : 0≤(r:ℝ)+1),abs_of_nonneg v0] at sum
  have a := mul_le_mul_of_nonneg_left ha (by positivity : 0≤(r:ℝ)+1)
  have b := mul_le_mul ve hb (abs_nonneg _) (by positivity)
  linarith only [hm,sum,a,b]

end CentralUnimodality.PolynomialTrial
