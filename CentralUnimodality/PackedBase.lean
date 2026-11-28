module

public import CentralUnimodality.PackedPeak
public import CentralUnimodality.ReflectedBase

/-! Complete rows beyond the original reflected-moment base. Each
block starts at the exact ballot layer of its indicated length. -/
@[expose] public section

namespace CentralUnimodality
open PackedComparisons

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

private theorem lengths_192_255 :
    checkLayers 256 64 192 (packedLayers 257 192)=true := by decide +kernel

private theorem lengths_256_319 :
    checkLayers 320 64 256 (packedLayers 321 256)=true := by decide +kernel

private theorem lengths_320_383 :
    checkLayers 384 64 320 (packedLayers 385 320)=true := by decide +kernel

theorem unimodal_length_lt_384 {m : ℕ} (hm : m<384) :
    UnimodalOn (rankCount m) 0 (m*m/4) := by
  by_cases h₀ : m<192
  · exact (reflected_through_191 h₀).1
  by_cases h₁ : m<256
  · have h := checkLayers_sound (by decide) lengths_192_255 (m-192) (by omega)
    simpa only [show 192+(m-192)=m by omega] using h
  by_cases h₂ : m<320
  · have h := checkLayers_sound (by decide) lengths_256_319 (m-256) (by omega)
    simpa only [show 256+(m-256)=m by omega] using h
  have h := checkLayers_sound (by decide) lengths_320_383 (m-320) (by omega)
  simpa only [show 320+(m-320)=m by omega] using h

theorem central_through_191 {n : ℕ} (hn : n≤191) :
    UnimodalOn (rankCount (2*n)) 0 (n*n) ∧
    UnimodalOn (rankCount (2*n+1)) 0 (n*(n+1)) := by
  exact ⟨odd_degree n ▸ unimodal_length_lt_384 (m:=2*n) (by omega),
    even_degree n ▸ unimodal_length_lt_384 (m:=2*n+1) (by omega)⟩

end CentralUnimodality
