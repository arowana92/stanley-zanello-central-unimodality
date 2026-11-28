module

public import CentralUnimodality.LocalJetTable
public meta import CentralUnimodality.LocalJetTable
import Mathlib.Tactic.Eval

/-! Half-unit derivative candidates are rounded upwards in decimal
units. Each row consists of five main-trial bounds and three bounds
for each of the two correction polynomials. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

abbrev JetBounds := List ℕ × List ℕ × List ℕ

def jetBoundsAt (i : ℕ) : JetBounds :=
  (localJetTable rawTrial i 5,localJetTable evenRawM i 3,localJetTable oddRawM i 3)

set_option maxRecDepth 65536 in
def jetWitnesses : Array JetBounds := eval% ((List.range 288).map jetBoundsAt).toArray

def jetsCheck (b : ℕ) : Bool := (List.range 4).all fun j =>
  let i := 4*b+j
  jetWitnesses[i]? == some (jetBoundsAt i)

theorem jets_from_blocks (blocks : ∀ b<72, jetsCheck b=true) {i : ℕ} (hi : i<288) :
    jetWitnesses[i]?=some (jetBoundsAt i) := by
  have h := List.all_eq_true.mp (blocks (i/4) (by omega)) (i%4) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  simp only [show 4*(i/4)+i%4=i by omega,beq_iff_eq] at h
  exact h

end CentralUnimodality.PolynomialTrial
