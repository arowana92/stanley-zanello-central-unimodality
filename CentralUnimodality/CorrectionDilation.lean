module

public import CentralUnimodality.FirstCorrectionRows
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Compatibility of the arcsine convolution and drift operators with
the change of variables from physical time to the unit interval. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Polynomial ReturnSplit

noncomputable def dilate256 (P : ℝ[X]) := P.comp (C (256:ℝ)*X)

theorem dilate_eval (P : ℝ[X]) (z : ℝ) : (dilate256 P).eval z=P.eval (256*z) := by
  simp [dilate256]

theorem dilate_beta (P Q : ℝ[X]) :
    dilate256 (betaProduct P Q)=betaProduct (dilate256 P) (dilate256 Q) := by
  apply Polynomial.funext; intro z
  rw [dilate_eval,← arc_polynomial,← arc_polynomial]
  apply arc_congr; intro x _
  simp only [dilate_eval]; ring_nf

theorem beta_constants (a b : ℝ) (P Q : ℝ[X]) :
    betaProduct (C a*P) (C b*Q)=C (a*b)*betaProduct P Q := by
  apply Polynomial.funext; intro z
  simp only [eval_mul,eval_C,← arc_polynomial,← arc_const_mul]
  apply arc_congr; intro x _
  ring

theorem dilate_drifts (P : ℝ[X]) :
    dilate256 (halfDrift P)=C (1/512:ℝ)*driftOp 1 (dilate256 P) ∧
    dilate256 (fullDrift P)=C (1/512:ℝ)*driftOp 2 (dilate256 P) := by
  have der (Q : ℝ[X]) : (dilate256 Q).derivative=C (256:ℝ)*dilate256 Q.derivative := by
    simp only [dilate256,derivative_comp,derivative_C_mul,derivative_X,mul_one]
  constructor <;> apply Polynomial.funext <;> intro z
  all_goals simp only [halfDrift,fullDrift,driftOp,der,derivative_C_mul,dilate_eval,eval_mul,eval_C,eval_add,eval_X]
  all_goals push_cast; ring

theorem dilate_normalized (a : List ℤ) (b : ℕ) (small : (coefficientMass a:ℤ)*7^a.length<2^b) :
    dilate256 (physicalPoly (doubleHead a))=C (1/(2:ℝ)^120)*realDense (unpackCheb b a) := by
  apply Polynomial.funext; intro z
  rw [dilate_eval,physical_eval,normalized_input b a small,show 256*z/256=z by ring,
    eval_mul,eval_C]; ring

theorem drift_linear (d : ℕ) (a b : ℝ) (P Q : ℝ[X]) :
    driftOp d (C a*P+C b*Q)=C a*driftOp d P+C b*driftOp d Q := by
  simp only [driftOp,derivative_add,derivative_C_mul]; ring

end CentralUnimodality.PolynomialTrial
