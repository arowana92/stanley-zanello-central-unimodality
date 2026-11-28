module

public import CentralUnimodality.GaussianLatticeNoise
public meta import CentralUnimodality.GaussianLatticeNoise
import Mathlib.Tactic.Eval

/-! Rounded Gaussian and lattice allowances in units of 10⁻³⁰.
There are 64 initial half-unit cells and one common final cell. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

abbrev GaussianBounds := List ℕ × List ℕ × ℕ × ℕ

def bridgeBinJets (k : ℕ) := (List.range 5).map (gaussianJetUnits 96 1 k bridgeMainRow)
def firstBinJets (k : ℕ) := (List.range 3).map (gaussianJetUnits 96 30720 k bridgeFirstRow)

def gaussianBoundsAt (k : ℕ) : GaussianBounds :=
  (bridgeBinJets k,firstBinJets k,freeNoiseUnits k,bridgeNoiseUnits k)

set_option maxRecDepth 10000 in
def gaussianWitnesses : Array GaussianBounds := eval% ((List.range 65).map gaussianBoundsAt).toArray

end CentralUnimodality.PolynomialTrial
