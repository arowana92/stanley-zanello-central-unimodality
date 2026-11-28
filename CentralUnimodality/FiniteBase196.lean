module

public import CentralUnimodality.ExtendedPackedBase
public import CentralUnimodality.ThreeFifthsReduction

/-! Insert the checked full coefficient rows through 195 into the all-size induction. -/
@[expose] public section

namespace CentralUnimodality

theorem conjecture34_from_196 (hD : DyckComparisons)
    (hsmall : ∀ n≥196, ∀ δ≤1, 2*n+δ<4096 → CentralToMidpoint n δ)
    (hbig : ∀ n≥196, ∀ δ≤1, 4096≤2*n+δ → ThreeFifthsPeak n δ) : Conjecture34 := by
  apply conjecture34_from_three_fifths hD
  · intro n hn δ hδ hm
    by_cases h : n≤195
    · apply midpoint_of_full_row (by omega) (by omega) hδ
      rcases (show δ=0 ∨ δ=1 by omega) with rfl|rfl
      · simpa using (central_through_195 h).1
      · exact (central_through_195 h).2
    · exact hsmall n (by omega) δ hδ hm
  · intro n _ δ hδ hm
    exact hbig n (by omega) δ hδ hm

end CentralUnimodality
