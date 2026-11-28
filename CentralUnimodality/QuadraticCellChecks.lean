module

public import CentralUnimodality.TwoUnitResidual
public meta import CentralUnimodality.TwoUnitResidual
public import Mathlib.Tactic.Eval
public import Mathlib.Tactic.IntervalCases

/-! Check the residual prefixes on all 57 two-unit intervals. Each parity
and each interval has its own kernel reduction. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Lean

def twoUnitMax (g : ℕ) := max (twoUnitNum evenQuadraticPower g) (twoUnitNum oddQuadraticPower g)
def quadraticCellCaps : Array ℕ := eval% ((List.range 57).map twoUnitMax).toArray
def cellQuadraticNum (g : ℕ) := quadraticCellCaps[g]?.getD 0

macro "check_quadratic_cells " label:ident start:num count:num : command => do
  let mut cmds := #[]
  let mut cases := #[]
  for j in [:count.getNat] do
    let i := start.getNat+j
    let n := Syntax.mkNumLit (toString i)
    let name := mkIdent (Name.mkSimple ("quadratic_cell_"++toString i))
    let row ← `(private theorem $name : twoUnitMax $n≤cellQuadraticNum $n := by
      apply max_le <;> decide +kernel)
    cmds := cmds.push row.raw
    cases := cases.push (← `(tactic| exact $name))
  let block ← `(theorem $label (j : ℕ) (hj : j<$count) :
      twoUnitMax ($start+j)≤cellQuadraticNum ($start+j) := by
    interval_cases j
    $[$cases:tactic]*)
  return ⟨mkNullNode (cmds.push block.raw)⟩

end CentralUnimodality.PolynomialTrial
