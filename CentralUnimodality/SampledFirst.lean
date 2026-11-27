module

public import CentralUnimodality.TabulatedWitness
public import CentralUnimodality.EvenCellChecks
public import CentralUnimodality.OddCellChecks

/-! Uniform sign for the degree-20 witness. The two coefficient tables
are certified at all sizes by the finite determination theorem. -/
@[expose] public section

namespace CentralUnimodality.Witness

theorem first_expectation {n δ : ℕ} (hδ : δ ≤ 1) (hn : 96 ≤ n+δ) :
    polyExpectation (normalizedCell n δ) 0 (coefficients first.B first.t first.roots) ≤
      -(1/10000000000:ℝ) := by
  have hlen : (coefficients first.B first.t first.roots).length = 21 := by decide +kernel
  rcases (by omega : δ = 0 ∨ δ = 1) with rfl|rfl
  · have h := suppliedCheck_sound hn evenCells first (fun r hr => evenCells_exact (by omega) n) supplied_first_signs.1
    simpa using h
  · have h := suppliedCheck_sound hn oddCells first (fun r hr => oddCells_exact (by omega) n) supplied_first_signs.2
    simpa using h

end CentralUnimodality.Witness
