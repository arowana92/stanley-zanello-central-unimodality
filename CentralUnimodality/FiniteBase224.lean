module

public import CentralUnimodality.DirectPeakCertificate
public import CentralUnimodality.ExcessBase

/-! Insert the full coefficient rows through 223 into the finite peak reduction. -/
@[expose] public section

namespace CentralUnimodality

theorem conjecture34_from_224 (hD : DyckComparisons)
    (small : ∀ n≥224, ∀ δ≤1, 2*n+δ<4096 → CentralToMidpoint n δ)
    (medium : ∀ n≥224, ∀ δ≤1, 4096≤2*n+δ → n<300000 → ThreeFifthsPeak n δ) : Conjecture34 := by
  apply conjecture34_from_finite_peaks hD
  · intro n hn δ hs hm
    by_cases h : n≤223
    · apply midpoint_of_full_row (by omega) (by omega) hs
      rcases (show δ=0 ∨ δ=1 by omega) with rfl|rfl
      · simpa using (central_through_223 h).1
      · exact (central_through_223 h).2
    · exact small n (by omega) δ hs hm
  · intro n _ δ hs hm hn
    exact medium n (by omega) δ hs hm hn

end CentralUnimodality
