module

public import CentralUnimodality.ThreeFifthsGrowth
public import CentralUnimodality.FinitePeakReduction

/-! Remove all coranks beyond the three-fifths cutoff from the large-size
peak hypothesis in the induction for the two original staircase families. -/
@[expose] public section

namespace CentralUnimodality
open MarkedExcursion.BinArithmetic

def ThreeFifthsPeak (n δ : ℕ) : Prop :=
  let m := 2*n+δ
  let D := n*(n+δ)
  UnimodalOn (fun k => rankCount m (D-k)) (centralStart n m) (min (D/2) ⌊(3/5)*sizeScale m⌋₊)

theorem midpoint_of_three_fifths {n δ : ℕ} (hm : 4096≤2*n+δ) (hδ : δ≤1)
    (peak : ThreeFifthsPeak n δ) : CentralToMidpoint n δ := by
  let m := 2*n+δ
  let D := n*(n+δ)
  let b := min (D/2) ⌊(3/5)*sizeScale m⌋₊
  let f := fun k => rankCount m (D-k)
  obtain ⟨p,hp,hpb,hinc,hdec⟩ := peak
  change UnimodalOn f _ (D/2)
  refine ⟨p,hp,hpb.trans (min_le_left ..),hinc,?_⟩
  intro k hpk hk
  by_cases hkb : k<b
  · exact hdec k hpk hkb
  have hfloor : ⌊(3/5)*sizeScale m⌋₊≤k := by dsimp only [b] at hkb; omega
  have cut : (3/5)*sizeScale m≤(k:ℝ)+1 :=
    (Nat.lt_floor_add_one _).le.trans (by exact_mod_cast Nat.add_le_add_right hfloor 1)
  let j := D-(k+2)
  have h₀ : j+1=D-(k+1) := by dsimp only [j]; omega
  have h₁ : j+2=D-k := by dsimp only [j]; omega
  have hdeg : staircaseDegree m=D := staircaseDegree_parity n δ hδ
  have hj : j+1+(k+1)=D := by dsimp only [j]; omega
  have hcor : (staircaseDegree m:ℝ)-((j:ℝ)+1)=(k:ℝ)+1 := by
    rw [hdeg]; have H := congrArg (fun t : ℕ => (t:ℝ)) hj
    push_cast at H; linarith only [H]
  change rankCount m (D-(k+1))≤rankCount m (D-k)
  rw [← h₀,← h₁]
  exact (Peak.upper_half_three_fifths hm (by rw [hdeg]; omega) (by rw [hdeg]; omega)
    (by rw [hcor]; exact cut)).le

theorem conjecture34_from_three_fifths (hD : DyckComparisons)
    (hsmall : ∀ n≥192, ∀ δ≤1, 2*n+δ<4096 → CentralToMidpoint n δ)
    (hbig : ∀ n≥192, ∀ δ≤1, 4096≤2*n+δ → ThreeFifthsPeak n δ) : Conjecture34 := by
  apply conjecture34_of_comparisons_and_midpoints hD
  intro n h96 δ hδ
  by_cases h : n≤191
  · exact midpoint_through_191 h96 h hδ
  · by_cases hm : 4096≤2*n+δ
    · exact midpoint_of_three_fifths hm hδ (hbig n (by omega) δ hδ hm)
    · exact hsmall n (by omega) δ hδ (by omega)

end CentralUnimodality
