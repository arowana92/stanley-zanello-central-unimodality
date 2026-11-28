module

public import CentralUnimodality.SplitCellMaxima
public import Mathlib.Tactic.IntervalCases

/-! Check each cell in a separate theorem. A fresh kernel computation
per cell keeps the arithmetic workspace bounded. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Lean

macro "check_bool_range " name:ident test:ident start:num count:num : command => do
  let mut cmds := #[]
  let mut cases := #[]
  for j in [:count.getNat] do
    let i := start.getNat+j
    let idx := Syntax.mkNumLit (toString i)
    let label := mkIdent (Name.mkSimple (name.getId.toString++"_cell_"++toString i))
    let row ← `(private theorem $label : $test $idx=true := by decide +kernel)
    cmds := cmds.push row.raw
    cases := cases.push (← `(tactic| exact $label))
  let block ← `(theorem $name (j : ℕ) (hj : j<$count) : $test ($start+j)=true := by
    interval_cases j
    $[$cases:tactic]*)
  return ⟨mkNullNode (cmds.push block.raw)⟩

end CentralUnimodality.PolynomialTrial
