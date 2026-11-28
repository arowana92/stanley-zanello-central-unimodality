module

public import CentralUnimodality.CorrectionPackedRows
public import CentralUnimodality.BlockRadixDigits
public meta import CentralUnimodality.CorrectionPackedRows
import Mathlib.Tactic.Eval

/-! Verify the monomial conversions independently before weighting the
two convolution products. Decode the radix expansion by bisection. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option Elab.async false

def rawFree : List ℤ := eval% freePower
noncomputable def rawFreePacked : ℤ := eval% packCheb 2048 freeRow.toList

private theorem rawFree_packed : packCheb 2048 freeRow.toList=rawFreePacked := by decide +kernel

theorem rawFree_exact : freePower=rawFree := by
  change centeredDigits 2048 freeRow.toList.length (packCheb 2048 freeRow.toList)=rawFree
  rw [← blockCenteredDigits_exact 2048 10,rawFree_packed]; decide +kernel

def rawBridge : List ℤ := eval% bridgePower
noncomputable def rawBridgePacked : ℤ := eval% packCheb 2048 bridgeRow.toList

private theorem rawBridge_packed : packCheb 2048 bridgeRow.toList=rawBridgePacked := by decide +kernel

theorem rawBridge_exact : bridgePower=rawBridge := by
  change centeredDigits 2048 bridgeRow.toList.length (packCheb 2048 bridgeRow.toList)=rawBridge
  rw [← blockCenteredDigits_exact 2048 10,rawBridge_packed]; decide +kernel

def rawTrial : List ℤ := eval% trialPower
noncomputable def rawTrialPacked : ℤ := eval% packCheb 1536 trialRow.toList

private theorem rawTrial_packed : packCheb 1536 trialRow.toList=rawTrialPacked := by decide +kernel

theorem rawTrial_exact : trialPower=rawTrial := by
  change centeredDigits 1536 trialRow.toList.length (packCheb 1536 trialRow.toList)=rawTrial
  rw [← blockCenteredDigits_exact 1536 10,rawTrial_packed]; decide +kernel

def rawBase : List ℤ := eval% residualPower
noncomputable def rawBasePacked : ℤ := eval% packCheb 5120 residualRow.toList

private theorem rawBase_packed : packCheb 5120 residualRow.toList=rawBasePacked := by decide +kernel

theorem rawBase_exact : residualPower=rawBase := by
  change centeredDigits 5120 residualRow.toList.length (packCheb 5120 residualRow.toList)=rawBase
  rw [← blockCenteredDigits_exact 5120 10,rawBase_packed]; decide +kernel

def evenRawM : List ℤ := eval% correctionPower 0
noncomputable def evenRawMPacked : ℤ := eval% packCheb 1536 evenCorrectionRow.toList

private theorem evenRawM_packed : packCheb 1536 evenCorrectionRow.toList=evenRawMPacked := by decide +kernel

theorem evenRawM_exact : correctionPower 0=evenRawM := by
  change centeredDigits 1536 evenCorrectionRow.toList.length (packCheb 1536 evenCorrectionRow.toList)=evenRawM
  rw [← blockCenteredDigits_exact 1536 10,evenRawM_packed]; decide +kernel

def oddRawM : List ℤ := eval% correctionPower 1
noncomputable def oddRawMPacked : ℤ := eval% packCheb 1536 oddCorrectionRow.toList

private theorem oddRawM_packed : packCheb 1536 oddCorrectionRow.toList=oddRawMPacked := by decide +kernel

theorem oddRawM_exact : correctionPower 1=oddRawM := by
  change centeredDigits 1536 oddCorrectionRow.toList.length (packCheb 1536 oddCorrectionRow.toList)=oddRawM
  rw [← blockCenteredDigits_exact 1536 10,oddRawM_packed]; decide +kernel

def evenRawFirst : List ℤ := eval% firstResidualPower 0
noncomputable def evenRawFirstPacked : ℤ := eval% packCheb 5120 evenFirstWitness.2

private theorem evenRawFirst_packed : packCheb 5120 evenFirstWitness.2=evenRawFirstPacked := by decide +kernel

theorem evenRawFirst_exact : firstResidualPower 0=evenRawFirst := by
  change centeredDigits 5120 evenFirstWitness.2.length (packCheb 5120 evenFirstWitness.2)=evenRawFirst
  rw [← blockCenteredDigits_exact 5120 10,evenRawFirst_packed]; decide +kernel

def oddRawFirst : List ℤ := eval% firstResidualPower 1
noncomputable def oddRawFirstPacked : ℤ := eval% packCheb 5120 oddFirstWitness.2

private theorem oddRawFirst_packed : packCheb 5120 oddFirstWitness.2=oddRawFirstPacked := by decide +kernel

theorem oddRawFirst_exact : firstResidualPower 1=oddRawFirst := by
  change centeredDigits 5120 oddFirstWitness.2.length (packCheb 5120 oddFirstWitness.2)=oddRawFirst
  rw [← blockCenteredDigits_exact 5120 10,oddRawFirst_packed]; decide +kernel

end CentralUnimodality.PolynomialTrial
