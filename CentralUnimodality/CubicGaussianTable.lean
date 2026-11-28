module

public import CentralUnimodality.QuadraticGaussianCosts
public meta import CentralUnimodality.QuadraticGaussianCosts
import Mathlib.Tactic.Eval
import Mathlib.Tactic.IntervalCases

/-! Bounds on the bridge symbol, both signed corrections, and the two
lattice errors for the cubic remainder. Cells starting at 32 share the
Gaussian envelope on the interval from 32 to 144. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open ReturnSplit

abbrev CubicGaussianInputs := List ℕ × List ℕ × List ℕ × ℕ × ℕ

def cubicGaussAt (k : ℕ) : CubicGaussianInputs :=
  ((List.range 7).map (gaussianJetUnits 96 1 k bridgeMainRow),
   (List.range 5).map (gaussianJetUnits 96 30720 k bridgeFirstRow),
   (List.range 3).map (gaussianJetUnits 96 bridgeSecondPolyRowDen k bridgeSecondPolyRow),
   noiseCellNum 24 freeCubicNoiseDen k freeCubicNoise,noiseCellNum 96 bridgeCubicNoiseDen k bridgeCubicNoise)

set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option Elab.async false

def cubicGaussWitness : Array CubicGaussianInputs := eval% ((List.range 65).map cubicGaussAt).toArray

private theorem gauss_checked (k : ℕ) (hk : k<65) : cubicGaussWitness[k]?=some (cubicGaussAt k) := by
  interval_cases k <;> decide +kernel

def cubicGauss (i : ℕ) := cubicGaussWitness[gaussianBin i]?.getD default

private theorem gauss_lookup (i : ℕ) : cubicGauss i=cubicGaussAt (gaussianBin i) := by
  have h : gaussianBin i<65 := (min_le_right i 64).trans_lt (by decide)
  simp only [cubicGauss,gauss_checked _ h,Option.getD_some]

theorem cubic_gauss_main {i r : ℕ} (hi : i<228) (hr : r<7) {v : ℝ} (hv : v∈halfInterval i) :
    |iteratedDeriv r bridgeCurve v|≤(((cubicGauss i).1[r]?.getD 0:ℕ):ℝ)/10^30 := by
  simp only [gauss_lookup,cubicGaussAt,List.getElem?_map,List.getElem?_range hr,Option.map_some,Option.getD_some]
  exact bridge_curve_jet (by omega) hv r

theorem cubic_gauss_first {i r : ℕ} (hi : i<228) (hr : r<5) {v : ℝ} (hv : v∈halfInterval i) :
    |iteratedDeriv r bridgeFirst v|≤(((cubicGauss i).2.1[r]?.getD 0:ℕ):ℝ)/10^30 := by
  simp only [gauss_lookup,cubicGaussAt,List.getElem?_map,List.getElem?_range hr,Option.map_some,Option.getD_some]
  exact bridge_first_jet (by omega) hv r

theorem cubic_gauss_second {i r : ℕ} (hi : i<228) (hr : r<3) {v : ℝ} (hv : v∈halfInterval i) :
    |iteratedDeriv r bridgeSecond v|≤(((cubicGauss i).2.2.1[r]?.getD 0:ℕ):ℝ)/10^30 := by
  simp only [gauss_lookup,cubicGaussAt,List.getElem?_map,List.getElem?_range hr,Option.map_some,Option.getD_some]
  exact second_bridge_jet (by omega) hv r

theorem cubic_gauss_noise {σ i : ℕ} (hs : σ≤1) (hi : i<228) {v τ : ℝ} (hv : v∈halfInterval i)
    (t0 : 0≤τ) (ht : τ≤57/5000) :
    freeQuadraticCost σ v τ≤((cubicGauss i).2.2.2.1:ℝ)/10^30 ∧
    bridgeQuadraticCost v τ≤((cubicGauss i).2.2.2.2:ℝ)/10^30 := by
  simpa only [gauss_lookup,cubicGaussAt] using quadratic_gaussian_noise hs hi hv t0 ht

end CentralUnimodality.PolynomialTrial
