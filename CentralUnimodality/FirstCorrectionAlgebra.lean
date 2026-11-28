module

public import CentralUnimodality.CorrectionDilation

/-! Clear the scales in the corrected residual. After the change of
variable, only two ordinary factorial-weighted products remain. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Polynomial ReturnSplit

theorem realDense_linear_rows (p q : ℤ) (a b : List ℤ) :
    realDense (linearRows p q a b)=C (p:ℝ)*realDense a+C (q:ℝ)*realDense b := by
  simp [realDense,dense_linear]

private theorem dilate_sub (P Q : ℝ[X]) : dilate256 (P-Q)=dilate256 P-dilate256 Q := by simp [dilate256]
private theorem dilate_mul (P Q : ℝ[X]) : dilate256 (P*Q)=dilate256 P*dilate256 Q := by simp [dilate256]
private theorem dilate_neg (P : ℝ[X]) : dilate256 (-P)= -dilate256 P := by simp [dilate256]
private theorem drift_scalar (t : ℕ) (c : ℝ) (P : ℝ[X]) : driftOp t (C c*P)=C c*driftOp t P := by
  simp only [driftOp,derivative_C_mul]; ring

private noncomputable def formFree := physicalPoly freeCandidate
private noncomputable def formBridge := physicalPoly bridgeCandidate
private noncomputable def formTrial := physicalPoly candidate
private noncomputable def formBase := betaProduct formBridge formTrial
private noncomputable def formU := -formBridge*bridgeLogPoly-halfDrift formBridge
private noncomputable def formA (σ : ℕ) := -formFree*freeLogPoly σ-fullDrift formBase

private theorem scale_free : dilate256 formFree=C (1/(2:ℝ)^120)*realDense freePower :=
  dilate_normalized _ _ input_pack_bounds.1
private theorem scale_bridge : dilate256 formBridge=C (1/(2:ℝ)^120)*realDense bridgePower :=
  dilate_normalized _ _ input_pack_bounds.2.1
private theorem scale_trial : dilate256 formTrial=C (1/(2:ℝ)^120)*realDense trialPower :=
  dilate_normalized _ _ input_pack_bounds.2.2.1

private theorem scale_base : dilate256 formBase=C (1/(2:ℝ)^120)*realDense freePower+
    C (-1/(residualDen:ℝ))*realDense residualPower := by
  rw [formBase,dilate_beta,scale_bridge,scale_trial,beta_constants]
  apply Polynomial.funext; intro z
  have eq := congrArg (fun p : ℝ[X] => p.eval z) cleared_real
  simp only [eval_sub,eval_mul,eval_add,eval_C] at eq ⊢
  have dn : (residualDen:ℝ)≠0 := by exact_mod_cast (show residualDen≠0 by decide +kernel)
  field_simp [dn]; linarith only [eq]

private theorem scale_u : dilate256 formU=C (1/(7680*(2:ℝ)^120))*realDense firstBridge := by
  rw [formU,dilate_sub,dilate_mul,dilate_neg,(dilate_drifts formBridge).1,scale_bridge,drift_scalar]
  apply Polynomial.funext; intro z
  rw [firstBridge,bridgeLogTimes,realDense_linear_rows,logTimesRow_exact,driftRow_exact]
  simp only [eval_sub,eval_add,eval_mul,eval_C,eval_neg,eval_pow,eval_X,dilate_eval,(log_evals 0 (256*z)).2]
  unfold bridgeLogCorrection; push_cast; ring

private theorem scale_a (σ : ℕ) (z : ℝ) :
    7680*(2:ℝ)^240*residualDen*(dilate256 (formA σ)).eval z=(realDense (firstOrdinary σ)).eval z := by
  rw [formA,dilate_sub,dilate_mul,dilate_neg,scale_free,(dilate_drifts formBase).2,scale_base,drift_linear]
  simp only [firstOrdinary,freeLogTimes,realDense_linear_rows,driftRow_exact,logTimesRow_exact,dilate_eval,
    (log_evals σ (256*z)).1,eval_mul,eval_sub,eval_neg,eval_C,eval_pow,eval_X,eval_add]
  unfold freeLogCorrection; push_cast
  have dn : (residualDen:ℝ)≠0 := by exact_mod_cast (show residualDen≠0 by decide +kernel)
  field_simp [dn]; ring

theorem first_cleared_equation (σ : ℕ)
    (small : (coefficientMass (if σ=0 then evenCorrectionRow else oddCorrectionRow).toList:ℤ)*
      7^(if σ=0 then evenCorrectionRow else oddCorrectionRow).size<2^1536) (z : ℝ) :
    (7680*(2:ℝ)^240*residualDen)*(firstPoly σ).eval (256*z)=(realDense (firstOrdinary σ)).eval z-
      (residualDen:ℝ)*((betaProduct (realDense firstBridge) (realDense trialPower)).eval z+
      7680*(betaProduct (realDense bridgePower) (realDense (correctionPower σ))).eval z) := by
  have scale_m : dilate256 (physicalPoly (correctionCandidate σ))=
      C (1/(2:ℝ)^120)*realDense (correctionPower σ) := dilate_normalized _ _ small
  have raw : firstPoly σ=formA σ-betaProduct formU formTrial-
      betaProduct formBridge (physicalPoly (correctionCandidate σ)) := rfl
  rw [← dilate_eval,raw,dilate_sub,dilate_sub,dilate_beta,dilate_beta,scale_u,scale_trial,scale_bridge,scale_m,
    beta_constants,beta_constants]
  simp only [eval_sub,eval_mul,eval_C]
  linarith only [scale_a σ z]

end CentralUnimodality.PolynomialTrial
