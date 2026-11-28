module

public import CentralUnimodality.CombinedCorrectionJets
public meta import CentralUnimodality.CombinedCorrectionJets
public import Mathlib.Tactic.Eval
public import Mathlib.Tactic.IntervalCases

/-! Candidate derivative bounds for all split factors in the cubic
remainder, in the 228 half-unit cells of the quadratic expansion. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

def cubicJetsAt (i : ℕ) := (localJetTable rawTrial i 7,
  localJetTable evenCombinedPower i 5,localJetTable oddCombinedPower i 5)

set_option maxRecDepth 65536 in
def cubicJetData : Array (List ℕ × List ℕ × List ℕ) := eval% ((List.range 228).map cubicJetsAt).toArray

theorem cubic_jets_by_parts (i : ℕ) (a b c : List ℕ) (lookup : cubicJetData[i]?=some (a,b,c))
    (main : localJetTable rawTrial i 7=a) (ev : localJetTable evenCombinedPower i 5=b)
    (od : localJetTable oddCombinedPower i 5=c) : cubicJetData[i]?=some (cubicJetsAt i) := by
  simp only [cubicJetsAt,main,ev,od,lookup]

open Lean in
macro "check_cubic_jet_cells " label:ident start:num count:num : command => do
  let mut cmds := #[]
  let mut cases := #[]
  for j in [:count.getNat] do
    let i := start.getNat+j
    let idx := Syntax.mkNumLit (toString i)
    let name := mkIdent (Name.mkSimple ("cubic_jet_"++toString i))
    let row ← `(private theorem $name : cubicJetData[$idx]?=some (cubicJetsAt $idx) := by
      apply cubic_jets_by_parts $idx (eval% localJetTable rawTrial $idx 7)
        (eval% localJetTable evenCombinedPower $idx 5) (eval% localJetTable oddCombinedPower $idx 5) <;>
        decide +kernel)
    cmds := cmds.push row.raw
    cases := cases.push (← `(tactic| exact $name))
  let block ← `(theorem $label (j : ℕ) (hj : j<$count) :
      cubicJetData[$start+j]?=some (cubicJetsAt ($start+j)) := by
    interval_cases j
    $[$cases:tactic]*)
  return ⟨mkNullNode (cmds.push block.raw)⟩

end CentralUnimodality.PolynomialTrial
