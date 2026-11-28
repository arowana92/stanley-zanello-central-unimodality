module

public import CentralUnimodality.VerifiedCorrectionPowers

/-! Verify the candidate rows against the weighted products of the
original dyadic inputs, and check both cleared polynomial equalities. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option Elab.async false

private theorem left_even : fullWeighted (firstLeft 0)=evenLeftWeighted := by
  rw [firstLeft,firstOrdinary,freeLogTimes,rawFree_exact,rawBase_exact,evenRawFirst_exact]; decide +kernel
private theorem left_odd : fullWeighted (firstLeft 1)=oddLeftWeighted := by
  rw [firstLeft,firstOrdinary,freeLogTimes,rawFree_exact,rawBase_exact,oddRawFirst_exact]; decide +kernel
private theorem shared_u : halfWeighted firstBridge=firstBridgeWeighted := by
  rw [firstBridge,bridgeLogTimes,rawBridge_exact]; decide +kernel
private theorem shared_f : halfWeighted trialPower=firstTrialWeighted := by rw [rawTrial_exact]; decide +kernel
private theorem shared_b : halfWeighted bridgePower=bridgeTrialWeighted := by rw [rawBridge_exact]; decide +kernel
private theorem m_even : halfWeighted (correctionPower 0)=evenMWeighted := by rw [evenRawM_exact]; decide +kernel
private theorem m_odd : halfWeighted (correctionPower 1)=oddMWeighted := by rw [oddRawM_exact]; decide +kernel

private theorem even_cache : firstPacking 0=evenCachedPacking := by
  simp only [firstPacking,weightedPair,left_even,shared_u,shared_f,shared_b,m_even,evenCachedPacking]

private theorem odd_cache : firstPacking 1=oddCachedPacking := by
  simp only [firstPacking,weightedPair,left_odd,shared_u,shared_f,shared_b,m_odd,oddCachedPacking]

private theorem check_even : betaPairCheck 18432 (residualDen*evenFirstWitness.1) evenCachedPacking=true := by decide +kernel
private theorem check_odd : betaPairCheck 18432 (residualDen*oddFirstWitness.1) oddCachedPacking=true := by decide +kernel

theorem first_packing_verified {σ : ℕ} (hs : σ≤1) :
    betaPairCheck 18432 (residualDen*(firstWitness σ).1) (firstPacking σ)=true := by
  rcases (show σ=0 ∨ σ=1 by omega) with rfl|rfl
  · rw [even_cache]; exact check_even
  · rw [odd_cache]; exact check_odd

theorem first_residual_inputs {σ : ℕ} (hs : σ≤1) :
    0<(firstWitness σ).1 ∧ coefficientMass (firstWitness σ).2*10^15≤2852*(firstWitness σ).1 ∧
    (coefficientMass (firstWitness σ).2:ℤ)*7^(firstWitness σ).2.length<2^5120 ∧
    (coefficientMass (if σ=0 then evenCorrectionRow else oddCorrectionRow).toList:ℤ)*
      7^(if σ=0 then evenCorrectionRow else oddCorrectionRow).size<2^1536 := by
  rcases (show σ=0 ∨ σ=1 by omega) with rfl|rfl
  · exact ⟨even_first_size.1,even_first_size.2,by decide +kernel,by decide +kernel⟩
  · exact ⟨odd_first_size.1,odd_first_size.2,by decide +kernel,by decide +kernel⟩

end CentralUnimodality.PolynomialTrial
