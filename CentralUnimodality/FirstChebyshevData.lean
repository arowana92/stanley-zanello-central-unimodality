module

public import CentralUnimodality.CorrectedChebyshevWitness
public meta import CentralUnimodality.CorrectedChebyshevWitness
import Mathlib.Tactic.Eval

/-! Rational Chebyshev witnesses for the first correction of the two
walk series. Their normalization is independent in each parity. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option Elab.async false

def evenFirstWitness : ℕ × List ℤ := eval% residualWitness 0
def oddFirstWitness : ℕ × List ℤ := eval% residualWitness 1

def firstWitness (σ : ℕ) := if σ=0 then evenFirstWitness else oddFirstWitness

theorem even_first_size : 0<evenFirstWitness.1 ∧
    coefficientMass evenFirstWitness.2*10^15≤2852*evenFirstWitness.1 := by decide +kernel

theorem odd_first_size : 0<oddFirstWitness.1 ∧
    coefficientMass oddFirstWitness.2*10^15≤2852*oddFirstWitness.1 := by decide +kernel

end CentralUnimodality.PolynomialTrial
