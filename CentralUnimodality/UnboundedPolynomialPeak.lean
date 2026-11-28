module

public import CentralUnimodality.LargePeakReduction
public import CentralUnimodality.SpatialWindowCertificate
public import CentralUnimodality.ModerateSpatialTransfer

/-! Certified peak comparisons at every sufficiently large row count
for both staircase families, and their effect on the induction. -/
@[expose] public section

namespace CentralUnimodality

open Set PolynomialTrial

theorem peak_at_large_half_length {n δ : ℕ} (hs : δ≤1) (hn : 10^54≤n+δ) : ThreeFifthsPeak n δ := by
  obtain ⟨left,middle,right⟩ := compact_window_margins
  exact peak_of_trial_margins (fun x hx => le_trans (by norm_num) (left x hx))
    (fun x hx => le_trans (middle x hx) (by norm_num)) right hs hn

theorem peak_from_retained_amplitudes {n δ : ℕ} (hs : δ≤1) (hn : 150000≤n)
    (first : retainedError n δ 1≤0.176) (second : retainedError n δ 2≤148.4) : ThreeFifthsPeak n δ := by
  obtain ⟨left,middle,right⟩ := compact_window_margins
  exact peak_of_retained_errors hs hn first second left middle right

theorem conjecture34_from_bounded_peaks (hD : DyckComparisons)
    (small : ∀ n≥196, ∀ δ≤1, 2*n+δ<4096 → CentralToMidpoint n δ)
    (medium : ∀ n≥196, ∀ δ≤1, 4096≤2*n+δ → n+δ<10^54 → ThreeFifthsPeak n δ) : Conjecture34 := by
  apply conjecture34_from_196 hD small
  intro n h δ hs hm
  by_cases huge : 10^54≤n+δ
  · exact peak_at_large_half_length hs huge
  · exact medium n h δ hs hm (Nat.lt_of_not_ge huge)

end CentralUnimodality
