module

public import CentralUnimodality.ReflectedCheck
import Mathlib.Tactic.IntervalCases

/-! Verify the small-size part of the moment comparison argument by exact
reduction. Each check includes the complete row or uses the earlier base. -/
@[expose] public section

namespace CentralUnimodality

private def reflectedBlock (k : ℕ) : Bool :=
  (List.range 4).all (fun i => reflectedCheck (4*k+i))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem reflected_blocks_checked (k : ℕ) (hk : k < 48) : reflectedBlock k = true := by
  interval_cases k <;> decide +kernel

theorem reflected_through_191 {m : ℕ} (hm : m < 192) :
    UnimodalOn (rankCount m) 0 (m*m/4) ∧
    ∀ i j : ℕ, i < j → i+j ≤ reflectedLimit m →
      rankCount m (m*m/4-i) ≤ rankCount m (m*m/4-j) := by
  have ha := List.all_eq_true.mp (reflected_blocks_checked (m/4) (by omega))
  have h := ha (m%4) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  exact reflectedCheck_sound hm (by rwa [show 4*(m/4)+m%4 = m by omega] at h)

theorem central_through_95 {n : ℕ} (hn : n ≤ 95) :
    UnimodalOn (rankCount (2*n)) 0 (n*n) ∧
    UnimodalOn (rankCount (2*n+1)) 0 (n*(n+1)) := by
  exact ⟨odd_degree n ▸ (reflected_through_191 (m := 2*n) (by omega)).1,
    even_degree n ▸ (reflected_through_191 (m := 2*n+1) (by omega)).1⟩

end CentralUnimodality
