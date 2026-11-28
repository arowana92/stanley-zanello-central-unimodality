module

public import CentralUnimodality.IntegerBetaProduct
public import CentralUnimodality.PolynomialTrialData
public import CentralUnimodality.PolynomialResidualData

/-! Exact integer certificate for the base residual. Each packed
monomial row comes from the published Chebyshev coefficients. The two
sides of the cleared product have signed digits in a 14337-bit base. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

def freePower := unpackCheb 2048 freeRow.toList
def bridgePower := unpackCheb 2048 bridgeRow.toList
def trialPower := unpackCheb 1536 trialRow.toList
def residualPower := unpackCheb 5120 residualRow.toList

def halfWeighted (a : List ℤ) := weightList (fun i => 4*i+2) a 0 1
def fullWeighted (a : List ℤ) := weightList (fun i => 4*(i+1)) a 0 1

def clearedPower := linearRows (2^120*(residualDen:ℤ)) (-(2^240)) freePower residualPower
def clearedLeft := fullWeighted clearedPower
def clearedBridge := halfWeighted bridgePower
def clearedTrial := halfWeighted trialPower

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem input_pack_bounds :
    (coefficientMass freeRow.toList:ℤ)*7^freeRow.size<2^2048 ∧
    (coefficientMass bridgeRow.toList:ℤ)*7^bridgeRow.size<2^2048 ∧
    (coefficientMass trialRow.toList:ℤ)*7^trialRow.size<2^1536 ∧
    (coefficientMass residualRow.toList:ℤ)*7^residualRow.size<2^5120 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem product_pack_bounds :
    coefficientMass clearedLeft<2^14336 ∧
    residualDen*coefficientMass clearedBridge*coefficientMass clearedTrial<2^14336 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem packed_product_check :
    packDense 14337 clearedLeft=(residualDen:ℤ)*packDense 14337 clearedBridge*packDense 14337 clearedTrial := by
  decide +kernel

end CentralUnimodality.PolynomialTrial
