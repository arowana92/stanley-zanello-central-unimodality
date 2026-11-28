module

public import CentralUnimodality.QuadraticCellChecks
public import CentralUnimodality.QuadraticInversePricing
public import CentralUnimodality.CubicPairMaxima
public meta import CentralUnimodality.QuadraticCellChecks
public meta import CentralUnimodality.CubicPairMaxima
import Mathlib.Tactic.Eval

/-! Exact rational inverse weights and frequency charges at half-length
10,000. The front term uses the exact square root of 10,000. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open ReturnSplit

def secondUnits (i : ℕ) := cellQuadraticNum (i/4)+303*10^21

abbrev LocalQuadraticCosts := ℕ × ℕ × ℕ
def localQuadraticCosts (i : ℕ) : LocalQuadraticCosts :=
  (secondUnits i,cubicUnits i,jetNum (cubeInput i).signed 0)

set_option maxRecDepth 65536 in
def quadraticCostTable : Array LocalQuadraticCosts := eval% ((List.range 228).map localQuadraticCosts).toArray

def quadraticCostAt (i : ℕ) := quadraticCostTable[i]?.getD default
def secondPrice (i : ℕ) := (quadraticCostAt i).1
def cubicPrice (i : ℕ) := (quadraticCostAt i).2.1
def signedPrice (i : ℕ) := (quadraticCostAt i).2.2

def inverseQuote (c : ℕ → ℕ) (i : ℕ) :=
  200*(unitPrice c i+earlyPrice c i)+latePrice c i

def quadraticFrequencyAllowance (i : ℕ) : ℚ :=
  if i<228 then
    let h := topTime i
    let t := h/10000
    (1+topFrequency i/2)*(15/10^16)+(36/10^14)*h+400*t*(3/10^12)+
      t^2*inverseQuote secondPrice i+t^3*inverseQuote cubicPrice i+t*(signedPrice i:ℚ)/10^30
  else outerCellAllowance i

def quadraticFrequencyCharge (i r : ℕ) := roundUpper
  (3/4*rootHigh (topTime i)*(topFrequency i)^r*quadraticFrequencyAllowance i)

end CentralUnimodality.PolynomialTrial
