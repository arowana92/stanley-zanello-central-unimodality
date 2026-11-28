module

public import CentralUnimodality.LocalJetCandidates
public meta import CentralUnimodality.LocalJetCandidates
public import Mathlib.Tactic.Eval
public import Mathlib.Tactic.IntervalCases

/-! Certify each of the three polynomials separately for each literal
bin index. This keeps reductions of different shifted polynomials out
of the same arithmetic check. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Lean

theorem jets_by_parts (i : ℕ) (a b c : List ℕ) (lookup : jetWitnesses[i]?=some (a,b,c))
    (m : localJetTable rawTrial i 5=a) (e : localJetTable evenRawM i 3=b)
    (o : localJetTable oddRawM i 3=c) : jetWitnesses[i]?=some (jetBoundsAt i) := by
  simpa only [jetBoundsAt,m,e,o] using lookup

macro "check_jet_range " name:ident start:num count:num : command => do
  let mut cmds := #[]
  let mut cases := #[]
  for j in [:count.getNat] do
    let i := start.getNat+j
    let idx := Syntax.mkNumLit (toString i)
    let label := mkIdent (Name.mkSimple ("jet_row_"++toString i))
    let row ← `(private theorem $label : jetWitnesses[$idx]?=some (jetBoundsAt $idx) := by
      apply jets_by_parts $idx (eval% localJetTable rawTrial $idx 5)
        (eval% localJetTable evenRawM $idx 3) (eval% localJetTable oddRawM $idx 3) <;> decide +kernel)
    cmds := cmds.push row.raw
    cases := cases.push (← `(tactic| exact $label))
  let block ← `(theorem $name (j : ℕ) (hj : j<$count) :
      jetWitnesses[$start+j]?=some (jetBoundsAt ($start+j)) := by
    interval_cases j
    $[$cases:tactic]*)
  return ⟨mkNullNode (cmds.push block.raw)⟩

end CentralUnimodality.PolynomialTrial
