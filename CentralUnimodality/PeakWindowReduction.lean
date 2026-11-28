module

public import CentralUnimodality.UpperHalfGrowth
public import CentralUnimodality.RightFlankReduction

/-! For large ballot lengths the central induction needs only the
shape of the peak through the three-quarter corank cutoff. -/
@[expose] public section

namespace CentralUnimodality
open MarkedExcursion.BinArithmetic

def CentralPeakWindow (n δ : ℕ) : Prop :=
  let m := 2*n+δ
  let D := n*(n+δ)
  UnimodalOn (fun k => rankCount m (D-k)) (centralStart n m) (min (D/2) ⌊(3/4)*sizeScale m⌋₊)

theorem midpoint_of_peak_window {n δ : ℕ} (hm : 4096 ≤ 2*n+δ) (hδ : δ≤1)
    (peak : CentralPeakWindow n δ) : CentralToMidpoint n δ := by
  apply midpoint_of_remaining hm hδ
  refine ⟨peak,?_⟩
  let m := 2*n+δ
  let D := n*(n+δ)
  intro k _ hk hfar
  change k<D/2 at hk
  let j := D-(k+2)
  have h₀ : j+1=D-(k+1) := by dsimp only [j]; omega
  have h₁ : j+2=D-k := by dsimp only [j]; omega
  have hdeg : staircaseDegree m=D := staircaseDegree_parity n δ hδ
  have hcor : (staircaseDegree m:ℝ)-((j:ℝ)+1)=(k:ℝ)+1 := by
    rw [hdeg]
    have he : j+1+(k+1)=D := by dsimp only [j]; omega
    have H := congrArg (fun n : ℕ => (n:ℝ)) he
    push_cast at H; linarith only [H]
  have step := far_corank_growth (j:=j) hm (by rw [hdeg]; omega) (by rw [hdeg]; omega)
    (by rw [hcor]; exact hfar.le)
  change rankCount m (D-(k+1))≤rankCount m (D-k)
  rw [← h₀,← h₁]
  exact step.le

theorem conjecture34_of_peak_windows (hD : DyckComparisons)
    (hsmall : ∀ n ≥ 96, ∀ δ ≤ 1, 2*n+δ < 4096 → CentralToMidpoint n δ)
    (hbig : ∀ n ≥ 96, ∀ δ ≤ 1, 4096 ≤ 2*n+δ → CentralPeakWindow n δ) :
    Conjecture34 := by
  apply conjecture34_of_comparisons_and_midpoints hD
  intro n hn δ hδ
  by_cases hm : 4096≤2*n+δ
  · exact midpoint_of_peak_window hm hδ (hbig n hn δ hδ hm)
  · exact hsmall n hn δ hδ (by omega)

end CentralUnimodality
