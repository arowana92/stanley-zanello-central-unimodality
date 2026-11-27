module

public import CentralUnimodality.TaylorTables
import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace CentralUnimodality.Witness

open Laurent

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem blocks (b : ℕ) (hb : b < 14) : cachedBlock oddCells 1 b = true := by
  interval_cases b <;> decide +kernel

theorem oddCells_exact {r : ℕ} (hr : r ≤ 20) (n : ℕ) :
    PowerSeries.coeff (n+1) (eval (lookup oddCells r)) =
      ((1:ℚ)+1)*rawCell n 1 r := by
  exact rows_certify (by decide) oddCells_bounds (rows_from_cached (by decide) blocks) hr n

end CentralUnimodality.Witness
