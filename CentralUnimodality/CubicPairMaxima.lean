module

public import CentralUnimodality.CubicGaussianTable
public import CentralUnimodality.CubicJetChecks
public import CentralUnimodality.SplitPairBudgets
public meta import CentralUnimodality.CubicGaussianTable
public meta import CentralUnimodality.CubicJetChecks
public meta import CentralUnimodality.SplitPairBudgets

/-! Maximize the seven Taylor terms independently over all admissible
pairs of half-unit cells. Integer products use units of 10⁻⁶⁰. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

structure CubicInputs where
  main : List ℕ
  first : List ℕ
  second : List ℕ
  freeNoise : ℕ
  bridgeNoise : ℕ
  trial : List ℕ
  signed : List ℕ
deriving Inhabited, DecidableEq, Lean.ToExpr

def cubicInputsAt (i : ℕ) : CubicInputs :=
  let g := cubicGauss i
  let j := cubicJetData[i]?.getD default
  let signed := (List.range 5).map fun r => ceilQuotient (max (jetNum j.2.1 r) (jetNum j.2.2 r)) 512
  ⟨g.1,g.2.1,g.2.2.1,g.2.2.2.1,g.2.2.2.2,j.1,signed⟩

set_option maxRecDepth 65536 in
def cubicInputsData : Array CubicInputs := eval% ((List.range 228).map cubicInputsAt).toArray

def cubeInput (i : ℕ) := cubicInputsData[i]?.getD default

def cubicPairEntry (a b : CubicInputs) : ℕ → ℕ
  | 0 => a.bridgeNoise*(5000*jetNum b.trial 0+57*jetNum b.signed 0)+5000*jetNum a.second 0*jetNum b.signed 0
  | 1 => jetProduct 2 a.second b.trial+jetProduct 2 a.first b.signed
  | 2 => jetProduct 3 a.first b.trial+jetProduct 3 a.main b.signed
  | 3 => jetProduct 4 a.first b.trial+jetProduct 4 a.main b.signed
  | 4 => jetProduct 4 a.main b.trial
  | 5 => jetProduct 5 a.main b.trial
  | _ => jetProduct 6 a.main b.trial

def cubicMaxAt (i r : ℕ) :=
  (Finset.range (i+1)).sup fun p =>
    max (cubicPairEntry (cubeInput p) (cubeInput (i-p)) r) (cubicPairEntry (cubeInput p) (cubeInput (i-p-1)) r)

def cubicMaxRow (i : ℕ) := (List.range 7).map (cubicMaxAt i)

set_option maxRecDepth 65536 in
def cubicMaxData : Array (List ℕ) := eval% ((List.range 228).map cubicMaxRow).toArray

def cubicMaxNum (i r : ℕ) := jetNum (cubicMaxData[i]?.getD []) r

theorem cubic_pair_le {i p q r : ℕ} (hp : p≤ i) (hq : q≤ i-p) (low : i≤p+q+1) (hr : r<7)
    (row : cubicMaxData[i]?=some (cubicMaxRow i)) :
    cubicPairEntry (cubeInput p) (cubeInput q) r≤cubicMaxNum i r := by
  have mem : p∈Finset.range (i+1) := Finset.mem_range.mpr (by omega)
  have h : max (cubicPairEntry (cubeInput p) (cubeInput (i-p)) r)
      (cubicPairEntry (cubeInput p) (cubeInput (i-p-1)) r)≤cubicMaxAt i r :=
    Finset.le_sup (f:=fun n => max (cubicPairEntry (cubeInput n) (cubeInput (i-n)) r)
      (cubicPairEntry (cubeInput n) (cubeInput (i-n-1)) r)) mem
  simp only [cubicMaxNum,row,Option.getD_some,cubicMaxRow,jetNum,List.getElem?_map,List.getElem?_range hr,Option.map_some]
  rcases (show q=i-p ∨ q=i-p-1 by omega) with rfl|rfl
  · exact (le_max_left ..).trans h
  · exact (le_max_right ..).trans h

def cubicUnits (i : ℕ) :=
  let h := i+1
  let m := cubicMaxNum i
  ceilQuotient (2880000*(cubeInput i).freeNoise*10^30+576*m 0+
    180000*h*m 1+60000*h*m 2+5625*h^2*m 3+15000*h*m 4+3750*h^2*m 5+250*h^3*m 6) (2880000*10^30)

end CentralUnimodality.PolynomialTrial
