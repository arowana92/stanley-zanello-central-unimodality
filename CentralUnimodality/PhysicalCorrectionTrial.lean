module

public import CentralUnimodality.PolynomialFirstResidual
public import CentralUnimodality.PolynomialGaussianInputs
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! The physical-variable polynomials used for the first split correction.
Each correction row is the original dyadic Chebyshev table. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Polynomial ReturnSplit Set

noncomputable def physicalPoly (a : List ℤ) : ℝ[X] :=
  (realRow a).comp (1-X*C (1/128:ℝ))*C (1/(2*2^120):ℝ)

theorem physical_eval (a : List ℤ) (v : ℝ) : (physicalPoly a).eval v=value a v := by
  simp only [physicalPoly,eval_mul,eval_C,eval_comp,eval_sub,eval_one,eval_X,value]
  rw [show v*(1/128)=v/128 by ring]; ring

theorem physical_evaluation (a : List ℤ) : (fun t => (physicalPoly a).eval t)=value a :=
  funext (physical_eval a)

def correctionCandidate (σ : ℕ) := doubleHead (if σ=0 then evenCorrectionRow else oddCorrectionRow).toList

noncomputable def correctedPoly (σ : ℕ) := physicalPoly (correctionCandidate σ)+halfDrift (physicalPoly candidate)
noncomputable def correctedValue (σ : ℕ) (v : ℝ) := (correctedPoly σ).eval v

noncomputable def freeLogPoly (σ : ℕ) : ℝ[X] := C ((2*σ+1:ℝ)/32)*X^2+C (1/1920:ℝ)*X^5
noncomputable def bridgeLogPoly : ℝ[X] := C (1/192:ℝ)*X^2+C (1/30720:ℝ)*X^5

noncomputable def firstPoly (σ : ℕ) := firstResidualPoly
  (-(physicalPoly freeCandidate)*freeLogPoly σ) (-(physicalPoly bridgeCandidate)*bridgeLogPoly)
  (physicalPoly bridgeCandidate) (physicalPoly candidate) (physicalPoly (correctionCandidate σ))

theorem log_evals (σ : ℕ) (v : ℝ) :
    (freeLogPoly σ).eval v=freeLogCorrection σ v ∧ bridgeLogPoly.eval v=bridgeLogCorrection v := by
  simp only [freeLogPoly,bridgeLogPoly,eval_add,eval_mul,eval_pow,eval_X,eval_C,freeLogCorrection,bridgeLogCorrection]
  constructor <;> ring

theorem halfDrift_eval (P : ℝ[X]) (v : ℝ) : (halfDrift P).eval v=
    (deriv (fun t => P.eval t) v+v*deriv (deriv (fun t => P.eval t)) v)/2 := by
  have der (Q : ℝ[X]) : deriv (fun t => Q.eval t)=fun t => Q.derivative.eval t :=
    funext (fun t => (Q.hasDerivAt t).deriv)
  simp [halfDrift,der]; ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem correction_sizes : rowBudget (doubleHead evenCorrectionRow.toList)≤16*2^120 ∧
    rowBudget (doubleHead oddCorrectionRow.toList)≤16*2^120 := by decide +kernel

theorem correctedValue_bound (σ : ℕ) {v : ℝ} (hv : v∈Icc (0:ℝ) 144) : |correctedValue σ v|≤160 := by
  have big : v∈Icc (0:ℝ) 256 := ⟨hv.1,by linarith only [hv.2]⟩
  have mass : rowBudget (correctionCandidate σ)≤16*2^120 := by
    by_cases e : σ=0
    · simpa only [correctionCandidate,e,ite_true] using correction_sizes.1
    · simpa only [correctionCandidate,e,ite_false] using correction_sizes.2
  have realMass : (rowBudget (correctionCandidate σ):ℝ)≤16*2^120 := by exact_mod_cast mass
  have M : |value (correctionCandidate σ) v|≤8 := (value_bound _ big).trans (by linarith only [realMass])
  have hb := candidate_bounds big
  have prod : |v*deriv (deriv (value candidate)) v|≤144*2 := by
    rw [abs_mul,abs_of_nonneg hv.1]
    exact mul_le_mul hv.2 hb.2.2 (abs_nonneg _) (by norm_num)
  simp only [correctedValue,correctedPoly,eval_add,halfDrift_eval,physical_eval]
  apply (abs_add_le ..).trans
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith only [M,abs_add_le (deriv (value candidate) v) (v*deriv (deriv (value candidate)) v),hb.2.1,prod]

theorem retained_logs {σ : ℕ} (hs : σ≤1) {v : ℝ} (hv : v∈Icc (0:ℝ) 144) :
    |freeLogCorrection σ v|≤34000000 ∧ |bridgeLogCorrection v|≤2100000 := by
  have v0 := hv.1
  have p := pow_le_pow_left₀ v0 hv.2 5
  have q := pow_le_pow_left₀ v0 hv.2 2
  have s : (σ:ℝ)≤1 := by exact_mod_cast hs
  have prod := mul_le_mul (show 2*(σ:ℝ)+1≤3 by linarith) q (sq_nonneg _) (by norm_num)
  unfold freeLogCorrection bridgeLogCorrection
  rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
  constructor <;> linarith only [p,q,prod]

end CentralUnimodality.PolynomialTrial
