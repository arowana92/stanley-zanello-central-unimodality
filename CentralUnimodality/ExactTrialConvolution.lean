module

public import CentralUnimodality.PackedBaseResidual
public import CentralUnimodality.NormalizedChebyshev
public import CentralUnimodality.ArcsineSplit
public import CentralUnimodality.PolynomialGaussianDefect

/-! Exact identity between the trial convolution, the computed residual,
and the original Chebyshev polynomials on the scaled frequency axis. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Polynomial ReturnSplit

set_option maxRecDepth 8000
set_option exponentiation.threshold 16384

theorem cleared_polynomials :
    densePoly clearedLeft=C (residualDen:ℤ)*(densePoly clearedBridge*densePoly clearedTrial) := by
  apply eq_of_packed_eval 14336
  · intro i
    exact (dense_coeff_bound ..).trans_lt (by exact_mod_cast product_pack_bounds.1)
  · intro i
    rw [coeff_C_mul,abs_mul,abs_of_nonneg (Int.natCast_nonneg residualDen)]
    apply (mul_le_mul_of_nonneg_left (dense_product_bound clearedBridge clearedTrial i)
      (Int.natCast_nonneg residualDen)).trans_lt
    exact_mod_cast (by simpa only [mul_assoc] using product_pack_bounds.2 :
      residualDen*(coefficientMass clearedBridge*coefficientMass clearedTrial)<2^14336)
  · rw [eval_mul,eval_C,eval_mul,← packDense_eval,← packDense_eval,← packDense_eval,← mul_assoc]
    exact packed_product_check

theorem cleared_real :
    C ((2:ℝ)^120*residualDen)*realDense freePower-C ((2:ℝ)^240)*realDense residualPower=
      C (residualDen:ℝ)*betaProduct (realDense bridgePower) (realDense trialPower) := by
  have eq : realDense clearedLeft=C (residualDen:ℝ)*(realDense clearedBridge*realDense clearedTrial) := by
    simp [realDense,cleared_polynomials]
  have half (a : List ℤ) : realDense (halfWeighted a)=diagonal (fun k => (halfFactor k:ℝ)) (realDense a) :=
    realDense_weightList _ halfFactor (fun _ => rfl) a
  have full (a : List ℤ) : realDense (fullWeighted a)=diagonal (fun k => (fullFactor k:ℝ)) (realDense a) :=
    realDense_weightList _ fullFactor (fun _ => rfl) a
  change realDense (fullWeighted clearedPower)=C (residualDen:ℝ)*
    (realDense (halfWeighted bridgePower)*realDense (halfWeighted trialPower)) at eq
  rw [full,half,half,← diagonal_betaProduct,← diagonal_const_mul] at eq
  have H := diagonal_full_injective eq
  simp [clearedPower,realDense,dense_linear,sub_eq_add_neg] at H ⊢
  rw [show C (2:ℝ)=(2:ℝ[X]) by exact map_ofNat _ 2]
  norm_num at H ⊢
  exact H

def residualCandidate := doubleHead residualRow.toList

noncomputable def baseResidual (v : ℝ) : ℝ := (2^120/(residualDen:ℝ))*value residualCandidate v

theorem trial_convolution (v : ℝ) :
    value freeCandidate v-arc (fun x => value bridgeCandidate (v*x)*value candidate (v*(1-x)))=baseResidual v := by
  obtain ⟨smallP,smallB,smallF,smallR⟩ := input_pack_bounds
  let P := realDense freePower
  let B := realDense bridgePower
  let F := realDense trialPower
  let R := realDense residualPower
  let z := v/256
  have eP : value freeCandidate v=P.eval z/2^120 := normalized_input _ _ smallP _
  have eR : value residualCandidate v=R.eval z/2^120 := normalized_input _ _ smallR _
  have integrand : (fun x => value bridgeCandidate (v*x)*value candidate (v*(1-x))) =
      fun x => (1/2^240:ℝ)*(B.eval (z*x)*F.eval (z*(1-x))) := by
    funext x
    rw [bridgeCandidate,candidate,normalized_input _ _ smallB,normalized_input _ _ smallF]
    change B.eval (v*x/256)/2^120*(F.eval (v*(1-x)/256)/2^120)=_
    rw [show v*x/256=z*x by dsimp [z]; ring,show v*(1-x)/256=z*(1-x) by dsimp [z]; ring]
    ring
  rw [eP,integrand,arc_const_mul,arc_polynomial,baseResidual,eR]
  have H := congrArg (fun p : ℝ[X] => p.eval z) cleared_real
  simp only [eval_sub,eval_mul,eval_C] at H
  change (2^120*(residualDen:ℝ))*P.eval z-2^240*R.eval z=
    (residualDen:ℝ)*(betaProduct B F).eval z at H
  have nz : (residualDen:ℝ)≠0 := by exact_mod_cast (show residualDen≠0 by decide +kernel)
  field_simp [nz]
  linarith only [H]

end CentralUnimodality.PolynomialTrial
