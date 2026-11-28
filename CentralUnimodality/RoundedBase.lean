module

public import CentralUnimodality.FiniteRoundedPeak

/-! Certified strict slopes across the central interval in the two staircases
with 192 rows. The peaks below are indexed by distance from the top rank. -/
@[expose] public section

namespace CentralUnimodality.EndpointDeficit

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

private theorem odd_check : checkFinitePeak 103 (2^100) 384 2615=true := by decide +kernel
private theorem even_check : checkFinitePeak 103 (2^100) 385 2627=true := by decide +kernel

theorem midpoint_192 {δ : ℕ} (hδ : δ≤1) : CentralToMidpoint 192 δ := by
  rcases (show δ=0 ∨ δ=1 by omega) with rfl|rfl
  · exact finitePeak_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) odd_check
  · exact finitePeak_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) even_check

end CentralUnimodality.EndpointDeficit
