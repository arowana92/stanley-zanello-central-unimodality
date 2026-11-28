module

public import CentralUnimodality.TabulatedSpatialRow
public meta import CentralUnimodality.TabulatedSpatialRow
import Mathlib.Tactic.Eval

/-! Integer witnesses for the spatial Taylor integrals. `eval%` inserts
literal integers into the definitions. Separate kernel equalities check
them against the weight, moment and coefficient formulas. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

set_option maxRecDepth 40000
set_option maxHeartbeats 0
set_option Elab.async false

def spatialWeights : List ℤ := eval% (quarterWeights trialPower).1
def momentAtIndex (i : ℕ) := unitNumerator (fun k => common4000/k) spatialWeights (6*i+2)
def spatialMoments : Array ℤ := eval% ((List.range 514).map momentAtIndex).toArray

def firstTrialRow : List ℤ := eval% tabulatedRow 1 1024 spatialMoments
def secondTrialRow : List ℤ := eval% tabulatedRow 2 1024 spatialMoments
def trialRowDen : ℕ := eval% common4000*4^421*2^120*(1024:ℕ).factorial

theorem spatial_weights_eq : (quarterWeights trialPower).1=spatialWeights := by decide +kernel

end CentralUnimodality.PolynomialTrial
