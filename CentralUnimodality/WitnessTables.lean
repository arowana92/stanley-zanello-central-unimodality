module

public import CentralUnimodality.SampleBlocks
import Mathlib.Tactic.Eval
meta import CentralUnimodality.CellMoments

/-! Quote the proposed degree-20 tables as rational data. Their proof
uses the independent packed-rank checks and the 84-size determination
theorem. Quotation only supplies the candidate values. -/
@[expose] public section

namespace CentralUnimodality.Witness

open Laurent

def proposedCells (δ : ℕ) : Array Laurent :=
  let T := tables 20
  let R := rawNumerator (lookup T.1) (lookup T.2) δ
  let p := ((List.range 21).map R).toArray
  ((List.range 21).map fun r => cellNumerator (-(δ:ℚ)/2) (fun j => p[j]?.getD []) r).toArray

def evenCells : Array Laurent := eval% proposedCells 0
def oddCells : Array Laurent := eval% proposedCells 1

theorem evenCells_bounds : boundsAll evenCells = true := by decide +kernel
theorem oddCells_bounds : boundsAll oddCells = true := by decide +kernel

def sampleBlock (C : Array Laurent) (δ b : ℕ) :=
  (List.range 6).all fun i => rowCheck C (6*b+i) δ

theorem all_row_checks {C : Array Laurent} {δ : ℕ}
    (h : ∀ b < 14, sampleBlock C δ b = true) (n : ℕ) (hn : n < 84) : rowCheck C n δ = true := by
  have he := List.all_eq_true.mp (h (n/6) (by omega)) (n%6) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  rwa [show 6*(n/6)+n%6 = n by omega] at he

end CentralUnimodality.Witness
