module

public import CentralUnimodality.ExcessPackedRows
public import CentralUnimodality.ExtendedPackedBase

/-! Full coefficient rows at ballot lengths 392 through 447. -/
@[expose] public section

namespace CentralUnimodality
open PackedComparisons

set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

private theorem lengths_392_447 :
    checkExcess 448 56 392 (excessLayers 449 392)=true := by decide +kernel

theorem unimodal_length_lt_448 {m : ℕ} (hm : m<448) :
    UnimodalOn (rankCount m) 0 (m*m/4) := by
  by_cases h : m<392
  · exact unimodal_length_lt_392 h
  have H := checkExcess_sound (by decide) lengths_392_447 (m-392) (by omega)
  simpa only [show 392+(m-392)=m by omega] using H

theorem central_through_223 {n : ℕ} (hn : n≤223) :
    UnimodalOn (rankCount (2*n)) 0 (n*n) ∧
    UnimodalOn (rankCount (2*n+1)) 0 (n*(n+1)) := by
  exact ⟨odd_degree n ▸ unimodal_length_lt_448 (m:=2*n) (by omega),
    even_degree n ▸ unimodal_length_lt_448 (m:=2*n+1) (by omega)⟩

end CentralUnimodality
