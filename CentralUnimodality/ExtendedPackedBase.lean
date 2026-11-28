module

public import CentralUnimodality.PackedBase

/-! Full coefficient rows at ballot lengths 384 through 391. -/
@[expose] public section

namespace CentralUnimodality
open PackedComparisons

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

private theorem lengths_384_391 :
    checkLayers 392 8 384 (packedLayers 393 384)=true := by decide +kernel

theorem unimodal_length_lt_392 {m : ℕ} (hm : m<392) :
    UnimodalOn (rankCount m) 0 (m*m/4) := by
  by_cases h : m<384
  · exact unimodal_length_lt_384 h
  have H := checkLayers_sound (by decide) lengths_384_391 (m-384) (by omega)
  simpa only [show 384+(m-384)=m by omega] using H

theorem central_through_195 {n : ℕ} (hn : n≤195) :
    UnimodalOn (rankCount (2*n)) 0 (n*n) ∧
    UnimodalOn (rankCount (2*n+1)) 0 (n*(n+1)) := by
  exact ⟨odd_degree n ▸ unimodal_length_lt_392 (m:=2*n) (by omega),
    even_degree n ▸ unimodal_length_lt_392 (m:=2*n+1) (by omega)⟩

end CentralUnimodality
