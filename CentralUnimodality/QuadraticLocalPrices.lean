module

public import CentralUnimodality.QuadraticPrices
public import CentralUnimodality.IntegerCellChecks

/-! Connect each of the 228 integer price triples to its defining formulas. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option Elab.async false

def quadraticLocalCheck (i : ℕ) := decide (quadraticCostTable[i]?=some (localQuadraticCosts i))
check_bool_range check_local_prices quadraticLocalCheck 0 228

theorem local_quadratic_prices {i : ℕ} (hi : i<228) :
    secondPrice i=secondUnits i ∧ cubicPrice i=cubicUnits i ∧ signedPrice i=jetNum (cubeInput i).signed 0 := by
  have eq := check_local_prices i hi
  simp only [quadraticLocalCheck,Nat.zero_add,decide_eq_true_eq] at eq
  simp [secondPrice,cubicPrice,signedPrice,quadraticCostAt,eq,localQuadraticCosts]

end CentralUnimodality.PolynomialTrial
