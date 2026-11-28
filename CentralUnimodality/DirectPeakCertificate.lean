module

public import CentralUnimodality.CertifiedRetainedErrors
public import CentralUnimodality.UnboundedPolynomialPeak

/-! Peak comparisons from 300,000 rows for the two original strict
partition families. The induction also requires the Dyck comparisons
and peak checks below this cutoff. -/
@[expose] public section

namespace CentralUnimodality
open PolynomialTrial

theorem peak_from_300000 {n δ : ℕ} (hs : δ≤1) (hn : 300000≤n) : ThreeFifthsPeak n δ := by
  obtain ⟨first,second⟩ := certified_retained_errors (n:=n) hs (by omega)
  exact peak_from_retained_amplitudes hs hn first second

theorem conjecture34_from_finite_peaks (hD : DyckComparisons)
    (small : ∀ n≥196, ∀ δ≤1, 2*n+δ<4096 → CentralToMidpoint n δ)
    (medium : ∀ n≥196, ∀ δ≤1, 4096≤2*n+δ → n<300000 → ThreeFifthsPeak n δ) : Conjecture34 := by
  apply conjecture34_from_bounded_peaks hD small
  intro n hn δ hs hm _
  by_cases h : 300000≤n
  · exact peak_from_300000 hs h
  · exact medium n hn δ hs hm (Nat.lt_of_not_ge h)

end CentralUnimodality
