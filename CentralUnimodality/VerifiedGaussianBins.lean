module

public import CentralUnimodality.GaussianBinData
import Mathlib.Tactic.IntervalCases

/-! Validate the Gaussian inputs of the 64 initial cells and the one
common tail interval against the analytic bounds. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open ReturnSplit

set_option maxRecDepth 12000
set_option maxHeartbeats 0
set_option Elab.async false

private def gaussianBlock (b : ℕ) := (List.range 5).all fun j =>
  let i := 5*b+j
  gaussianWitnesses[i]? == some (gaussianBoundsAt i)

private theorem block0 : gaussianBlock 0=true := by decide +kernel
private theorem block1 : gaussianBlock 1=true := by decide +kernel
private theorem block2 : gaussianBlock 2=true := by decide +kernel
private theorem block3 : gaussianBlock 3=true := by decide +kernel
private theorem block4 : gaussianBlock 4=true := by decide +kernel
private theorem block5 : gaussianBlock 5=true := by decide +kernel
private theorem block6 : gaussianBlock 6=true := by decide +kernel
private theorem block7 : gaussianBlock 7=true := by decide +kernel
private theorem block8 : gaussianBlock 8=true := by decide +kernel
private theorem block9 : gaussianBlock 9=true := by decide +kernel
private theorem block10 : gaussianBlock 10=true := by decide +kernel
private theorem block11 : gaussianBlock 11=true := by decide +kernel
private theorem block12 : gaussianBlock 12=true := by decide +kernel

private theorem blocks (b : ℕ) (h : b<13) : gaussianBlock b=true := by
  interval_cases b
  · exact block0
  · exact block1
  · exact block2
  · exact block3
  · exact block4
  · exact block5
  · exact block6
  · exact block7
  · exact block8
  · exact block9
  · exact block10
  · exact block11
  · exact block12

theorem gaussian_witness_at {k : ℕ} (hk : k<65) : gaussianWitnesses[k]?=some (gaussianBoundsAt k) := by
  have eq := List.all_eq_true.mp (blocks (k/5) (by omega)) (k%5) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  simpa only [show 5*(k/5)+k%5=k by omega,beq_iff_eq] using eq

def gaussianInputs (i : ℕ) := gaussianWitnesses[gaussianBin i]?.getD default

theorem gaussian_inputs_eq (i : ℕ) : gaussianInputs i=gaussianBoundsAt (gaussianBin i) := by
  have le : gaussianBin i≤64 := min_le_right ..
  simp [gaussianInputs,gaussian_witness_at (by omega : gaussianBin i<65)]

theorem verified_bridge_jet {i r : ℕ} (hi : i<288) (hr : r<5) {v : ℝ} (hv : v∈halfInterval i) :
    |iteratedDeriv r bridgeCurve v|≤((((gaussianInputs i).1[r]?).getD 0:ℕ):ℝ)/10^30 := by
  simpa only [gaussian_inputs_eq,gaussianBoundsAt,bridgeBinJets,List.getElem?_map,List.getElem?_range hr,
    Option.map_some,Option.getD_some] using bridge_curve_jet hi hv r

theorem verified_first_jet {i r : ℕ} (hi : i<288) (hr : r<3) {v : ℝ} (hv : v∈halfInterval i) :
    |iteratedDeriv r bridgeFirst v|≤((((gaussianInputs i).2.1[r]?).getD 0:ℕ):ℝ)/10^30 := by
  simpa only [gaussian_inputs_eq,gaussianBoundsAt,firstBinJets,List.getElem?_map,List.getElem?_range hr,
    Option.map_some,Option.getD_some] using bridge_first_jet hi hv r

theorem verified_lattice_noise {i σ : ℕ} (hi : i<288) (hs : σ≤1) {v τ : ℝ} (hv : v∈halfInterval i)
    (t0 : 0≤τ) (ht : τ≤(maxStep:ℝ)) :
    freeLocalCost σ v τ≤((gaussianInputs i).2.2.1:ℝ)/10^30 ∧
    bridgeLocalCost v τ≤((gaussianInputs i).2.2.2:ℝ)/10^30 := by
  simpa only [gaussian_inputs_eq,gaussianBoundsAt] using And.intro (free_noise_bound hi hs hv t0 ht) (bridge_noise_bound hi hv t0 ht)

end CentralUnimodality.PolynomialTrial
