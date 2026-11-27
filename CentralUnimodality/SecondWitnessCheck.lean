module

public import CentralUnimodality.CellPrimitives

@[expose] public section

namespace CentralUnimodality.Witness

set_option maxRecDepth 100000 in
theorem second_checks :
    checkPair second 0 (7/1000000) = true ∧ checkPair second 1 (7/1000000) = true := by
  decide +kernel

theorem second_expectation {n δ : ℕ} (hδ : δ ≤ 1) (hn : 96 ≤ n+δ) :
    polyExpectation (normalizedCell n δ) 0 (coefficients second.B second.t second.roots) ≤
      -(7/1000000:ℝ) := by
  have hc : checkPair second δ (7/1000000) = true := by
    rcases (by omega : δ = 0 ∨ δ = 1) with rfl|rfl
    · exact second_checks.1
    · exact second_checks.2
  simpa using checkPair_sound second hδ hn hc

end CentralUnimodality.Witness
