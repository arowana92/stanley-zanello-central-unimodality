module

public import CentralUnimodality.DyckComparisonBase
public import CentralUnimodality.WalkBlockBounds
public import CentralUnimodality.FiniteBase224

/-! Restrict the auxiliary Dyck hypothesis to the comparisons outside both
the exact semilength certificate and the uniform walk-block estimate. -/
@[expose] public section

namespace CentralUnimodality

def RemainingDyckComparisons : Prop :=
  ∀ l > 256, ∀ i j : ℕ, i < j → l/32*202 < i+j → i+j ≤ ⌈dyckLower l⌉₊ →
    (dyckPoly l).coeff i≤(dyckPoly l).coeff j

theorem dyck_comparisons_iff_remaining : DyckComparisons ↔ RemainingDyckComparisons := by
  constructor
  · intro H l _ i j hij _ hsum
    exact H l i j hij (by exact_mod_cast hsum)
  · intro H l i j hij hsum
    by_cases hl : l≤256
    · exact HeightBlock.dyck_comparisons_through_256 hl i j hij hsum
    by_cases small : i+j≤l/32*202
    · exact HeightBlock.dyck_reflected64 l i j hij (by exact_mod_cast small)
    exact H l (by omega) i j hij (by omega) (by exact_mod_cast hsum)

theorem conjecture34_from_remaining (hD : RemainingDyckComparisons)
    (small : ∀ n≥224, ∀ δ≤1, 2*n+δ<4096 → CentralToMidpoint n δ)
    (medium : ∀ n≥224, ∀ δ≤1, 4096≤2*n+δ → n<300000 → ThreeFifthsPeak n δ) : Conjecture34 :=
  conjecture34_from_224 (dyck_comparisons_iff_remaining.mpr hD) small medium

end CentralUnimodality
