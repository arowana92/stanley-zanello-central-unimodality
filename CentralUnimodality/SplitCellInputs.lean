module

public import CentralUnimodality.CertifiedLocalJets
public import CentralUnimodality.VerifiedGaussianBins
import Mathlib.Tactic.Eval
public import Lean.ToLevel
public import Lean.ToExpr
public meta import CentralUnimodality.CertifiedLocalJets
public meta import CentralUnimodality.VerifiedGaussianBins

/-! Common integer input rows for the split. The correction has scale
`4·10³⁰`; all other fields have scale `10³⁰`. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open ReturnSplit

set_option maxRecDepth 65536
set_option maxHeartbeats 0

structure CellInputs where
  trial : List ℕ
  correction : List ℕ
  bridge : List ℕ
  firstBridge : List ℕ
  freeNoise : ℕ
  bridgeNoise : ℕ
  deriving Inhabited, DecidableEq, Repr, Lean.ToExpr

def makeCellInputs (i : ℕ) : CellInputs :=
  let a := gaussianInputs i
  ⟨(jetWitnesses[i]?.getD default).1,(List.range 3).map (correctionJetNum i),
    a.1,a.2.1,a.2.2.1,a.2.2.2⟩

def inputTable : Array CellInputs := eval% ((List.range 288).map makeCellInputs).toArray

private theorem input_checks : (List.range 288).all (fun i =>
    decide (inputTable[i]?=some (makeCellInputs i)))=true := by decide +kernel

def splitInputs (i : ℕ) := inputTable[i]?.getD default
def jetNum (j : List ℕ) (r : ℕ) := (j[r]?).getD 0

theorem split_inputs_exact {i : ℕ} (hi : i<288) : splitInputs i=makeCellInputs i := by
  have h := of_decide_eq_true (List.all_eq_true.mp input_checks i (List.mem_range.mpr hi))
  simp [splitInputs,h]

theorem cell_trial {i r : ℕ} (hi : i<288) (hr : r<5) {v : ℝ} (hv : v∈halfInterval i) :
    |iteratedDeriv r (value candidate) v|≤(jetNum (splitInputs i).trial r:ℝ)/10^30 := by
  rw [split_inputs_exact hi]; exact certified_trial_jet hi hr hv

theorem cell_correction {i r σ : ℕ} (hs : σ≤1) (hi : i<288) (hr : r<3) {v : ℝ} (hv : v∈halfInterval i) :
    |iteratedDeriv r (correctedValue σ) v|≤(jetNum (splitInputs i).correction r:ℝ)/(4*10^30) := by
  simp only [split_inputs_exact hi,makeCellInputs,jetNum,List.getElem?_map,List.getElem?_range hr,Option.map_some,Option.getD_some]
  exact certified_correction_jet hs hi hr hv

theorem cell_bridge {i r : ℕ} (hi : i<288) (hr : r<5) {v : ℝ} (hv : v∈halfInterval i) :
    |iteratedDeriv r bridgeCurve v|≤(jetNum (splitInputs i).bridge r:ℝ)/10^30 := by
  rw [split_inputs_exact hi]; exact verified_bridge_jet hi hr hv

theorem cell_bridge_first {i r : ℕ} (hi : i<288) (hr : r<3) {v : ℝ} (hv : v∈halfInterval i) :
    |iteratedDeriv r bridgeFirst v|≤(jetNum (splitInputs i).firstBridge r:ℝ)/10^30 := by
  rw [split_inputs_exact hi]; exact verified_first_jet hi hr hv

theorem cell_noise {i σ : ℕ} (hi : i<288) (hs : σ≤1) {v τ : ℝ} (hv : v∈halfInterval i)
    (t0 : 0≤τ) (ht : τ≤(maxStep:ℝ)) : freeLocalCost σ v τ≤((splitInputs i).freeNoise:ℝ)/10^30 ∧
    bridgeLocalCost v τ≤((splitInputs i).bridgeNoise:ℝ)/10^30 := by
  rw [split_inputs_exact hi]; exact verified_lattice_noise hi hs hv t0 ht

end CentralUnimodality.PolynomialTrial
