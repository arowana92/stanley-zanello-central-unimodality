module

public import CentralUnimodality.Finite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-! Exact finite base in the induction. Every rank in each of the 126 shapes
is checked by kernel reduction on natural numbers. -/
@[expose] public section

namespace CentralUnimodality

private def wordTest (m : ℕ) : Bool := checkRow 128 m (m*m/4)

private def blockTest (k : ℕ) : Bool :=
  (List.range 8).all (fun i => wordTest (8*k+i))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem blocks_checked (k : ℕ) (hk : k < 16) : blockTest k = true := by
  interval_cases k <;> decide +kernel

theorem base_word {m : ℕ} (hm : m < 128) : UnimodalOn (rankCount m) 0 (m*m/4) := by
  have verified := List.all_eq_true.mp (blocks_checked (m/8) (by omega))
  have h := verified (m%8) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  rw [show 8*(m/8)+m%8 = m by omega] at h
  exact checkRow_sound hm h

theorem odd_degree (n : ℕ) : (2*n)*(2*n)/4 = n*n := by
  rw [show (2*n)*(2*n) = 4*(n*n) by ring]
  omega

theorem even_degree (n : ℕ) : (2*n+1)*(2*n+1)/4 = n*(n+1) := by
  rw [show (2*n+1)*(2*n+1) = 4*(n*(n+1))+1 by ring]
  omega

theorem central_through_63 {n : ℕ} (hn : n ≤ 63) :
    UnimodalOn (rankCount (2*n)) 0 (n*n) ∧ UnimodalOn (rankCount (2*n+1)) 0 (n*(n+1)) := by
  exact ⟨odd_degree n ▸ base_word (m := 2*n) (by omega),
    even_degree n ▸ base_word (m := 2*n+1) (by omega)⟩

end CentralUnimodality
