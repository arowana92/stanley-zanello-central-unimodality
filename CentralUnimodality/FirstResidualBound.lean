module

public import CentralUnimodality.CorrectionPackedRows
public import CentralUnimodality.FirstCorrectionAlgebra
public import CentralUnimodality.ChebyshevMass
public import CentralUnimodality.FirstResidualTransfer

/-! Recover the exact first residual from the cleared integer identity
and bound its value throughout the retained interval. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Set Polynomial ReturnSplit

theorem first_bound_of_packing (σ : ℕ)
    (packing : betaPairCheck 18432 (residualDen*(firstWitness σ).1) (firstPacking σ)=true)
    (positive : 0<(firstWitness σ).1)
    (mass : coefficientMass (firstWitness σ).2*10^15≤2852*(firstWitness σ).1)
    (small : (coefficientMass (firstWitness σ).2:ℤ)*7^(firstWitness σ).2.length<2^5120)
    (input : (coefficientMass (if σ=0 then evenCorrectionRow else oddCorrectionRow).toList:ℤ)*
      7^(if σ=0 then evenCorrectionRow else oddCorrectionRow).size<2^1536)
    {v : ℝ} (hv : v∈Icc (0:ℝ) 144) : |(firstPoly σ).eval v|≤2852/10^15 := by
  let z := v/256
  let d : ℝ := (firstWitness σ).1
  let K : ℝ := 7680*2^240*residualDen
  have den : (0:ℝ)<residualDen := by exact_mod_cast (show 0<residualDen by decide +kernel)
  have dpos : 0<d := by dsimp only [d]; exact_mod_cast positive
  have kp : 0<K := by dsimp only [K]; positivity
  have A := first_cleared_equation σ input z
  have evaluate := two_betas_of_check (firstLeft σ) firstBridge trialPower bridgePower (correctionPower σ) packing
  have pair := congrArg (fun Q : ℝ[X] => Q.eval z) evaluate
  simp only [firstLeft,realDense_linear_rows,eval_mul,eval_add,eval_C] at pair
  push_cast at pair
  rw [show 256*z=v by dsimp only [z]; ring] at A
  have exactValue : (firstPoly σ).eval v=(realDense (firstResidualPower σ)).eval z/d := by
    apply (eq_div_iff dpos.ne').mpr
    apply mul_left_cancel₀ kp.ne'
    dsimp only [K,d]
    linear_combination (norm := ring) ((firstWitness σ).1:ℝ)*A+pair
  have w : |1-2*z|≤1 := by dsimp only [z]; exact abs_le.mpr ⟨by linarith only [hv.2],by linarith only [hv.1]⟩
  have close := unpacked_mass _ _ small w
  rw [exactValue,abs_div,abs_of_pos dpos,div_le_iff₀ dpos]
  change |(realDense (unpackCheb 5120 (firstWitness σ).2)).eval z|≤_
  apply close.trans
  have cap : (coefficientMass (firstWitness σ).2:ℝ)*10^15≤2852*d := by dsimp only [d]; exact_mod_cast mass
  linarith only [cap]

end CentralUnimodality.PolynomialTrial
