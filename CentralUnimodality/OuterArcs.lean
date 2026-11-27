module

public import CentralUnimodality.BlockVerifier
import Mathlib.Tactic.Eval
meta import CentralUnimodality.ArcEnvelope

/-! The two finite outer arcs of the central Fourier certificate. A rational
table covers every suffix length, and every positive starting height is
included in the killed-kernel estimate. -/
@[expose] public section

namespace CentralUnimodality

private def proposeEnvelope (t : ℚ) (n : ℕ) : Array ℕ :=
  ((List.range (n+1)).map (envelopeUnits t)).toArray

private def table008 : Array ℕ := eval% proposeEnvelope 0.008 216
private def table032 : Array ℕ := eval% proposeEnvelope 0.032 112

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 20000 in
private theorem verify008 : envelopeOK 0.008 table008 216 = true ∧ blockOK table008 216 0.18 = true := by
  decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 20000 in
private theorem verify032 : envelopeOK 0.032 table032 112 = true ∧ blockOK table032 112 0.172 = true := by
  decide +kernel

theorem killed_arc_008 {θ : ℝ} (hlo : 0.008 ≤ θ) (hhi : θ ≤ Real.pi) {a : ℕ} (ha : 0 < a)
    (s : Finset ℤ) : (∑ z ∈ s, ‖killedAt (θ/2) a 216 z‖)/(2:ℝ)^216 < Real.exp (-0.0078*216) := by
  have h := blockOK_sound (by norm_num) verify008.1 verify008.2 (by exact_mod_cast hlo) hhi ha s
  apply h.trans_lt
  have he := rate_lower_exp (0.0078*216) (by norm_num)
  rw [neg_mul]
  exact lt_of_lt_of_le (by norm_num) he

theorem killed_arc_032 {θ : ℝ} (hlo : 0.032 ≤ θ) (hhi : θ ≤ Real.pi) {a : ℕ} (ha : 0 < a)
    (s : Finset ℤ) : (∑ z ∈ s, ‖killedAt (θ/2) a 112 z‖)/(2:ℝ)^112 < Real.exp (-0.0155*112) := by
  have h := blockOK_sound (by norm_num) verify032.1 verify032.2 (by exact_mod_cast hlo) hhi ha s
  apply h.trans_lt
  have he := rate_lower_exp (0.0155*112) (by norm_num)
  rw [neg_mul]
  exact lt_of_lt_of_le (by norm_num) he

end CentralUnimodality
