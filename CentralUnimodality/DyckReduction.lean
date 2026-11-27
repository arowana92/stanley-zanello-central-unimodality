module

public import CentralUnimodality.ReflectedIntervals
public import CentralUnimodality.MidpointInduction

/-! The Dyck input may be supplied directly as inequalities on the
ordinary one-variable area polynomial. -/
@[expose] public section

namespace CentralUnimodality

/-- Only these ordinary Dyck coefficient comparisons are required of the
two-variable character argument in the written proof. -/
def DyckComparisons : Prop :=
  ∀ l, ReflectedCoeffs (dyckPoly l) (⌈dyckLower l⌉₊ : ℕ)

theorem dyck_from_comparisons (h : DyckComparisons) (l : ℕ) :
    IntervalDecomposition (dyckPoly l) (⌈dyckLower l⌉₊ : ℕ) :=
  intervalDecomposition_of_reflected (h l)

theorem central_from_comparisons (hD : DyckComparisons)
    (href : ∀ n, UnimodalOn (rankCount (2*n)) 0 (n*n) →
      ReflectedCoeffs (ballotPoly (2*n)) ⌊oddCutoff n⌋)
    (hc : ∀ n ≥ 96, ∀ δ ≤ 1, CentralToMidpoint n δ) : Conjecture34 := by
  apply central_from_midpoints _ (dyck_from_comparisons hD) _ href hc
  intro l
  simpa only [Int.cast_natCast] using Nat.le_ceil (dyckLower l)

end CentralUnimodality
