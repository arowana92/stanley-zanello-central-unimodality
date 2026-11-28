module

public import CentralUnimodality.RightFlankRanks
public import CentralUnimodality.ReflectedPolynomials

/-! Remove the strict-growth window from the remaining corank hypotheses
in the induction for the original conjecture. -/
@[expose] public section

namespace CentralUnimodality
open MarkedExcursion.BinArithmetic

/-- The predecessor of the rank tested by the saddle exists throughout
this upper half. Both endpoint inequalities use the corank of that rank. -/
theorem corank_flank_decreases {m k : ℕ} (hm : 4096 ≤ m) (hk : k < staircaseDegree m/2)
    (hlo : (3/4)*sizeScale m ≤ (k:ℝ)+1) (hhi : (k:ℝ)+1 ≤ 2*sizeScale m) :
    rankCount m (staircaseDegree m-(k+1)) < rankCount m (staircaseDegree m-k) := by
  let j := staircaseDegree m-(k+2)
  have h₀ : j+1=staircaseDegree m-(k+1) := by dsimp only [j]; omega
  have h₁ : j+2=staircaseDegree m-k := by dsimp only [j]; omega
  have H : (staircaseDegree m:ℝ)-((j:ℝ)+1)=(k:ℝ)+1 := by
    have he : j+1+(k+1)=staircaseDegree m := by dsimp only [j]; omega
    have he' := congrArg (fun n : ℕ => (n:ℝ)) he
    push_cast at he'; linarith only [he']
  rw [← h₀,← h₁]
  exact right_flank_growth (m:=m) (j:=j) hm (by omega) (by rwa [H]) (by rwa [H])

/-- The central interval now needs a unimodal peak window only up to the
three-quarter cut. Beyond twice the scale the weak descent is still an
input. The cuts are clamped at the midpoint. -/
def RemainingMidpoint (n δ : ℕ) : Prop :=
  let m := 2*n+δ
  let D := n*(n+δ)
  let b := min (D/2) ⌊(3/4)*sizeScale m⌋₊
  let f := fun k => rankCount m (D-k)
  UnimodalOn f (centralStart n m) b ∧
    ∀ k, b ≤ k → k < D/2 → 2*sizeScale m < (k:ℝ)+1 → f (k+1) ≤ f k

theorem midpoint_of_remaining {n δ : ℕ} (hm : 4096 ≤ 2*n+δ) (hδ : δ ≤ 1)
    (h : RemainingMidpoint n δ) : CentralToMidpoint n δ := by
  let m := 2*n+δ
  let D := n*(n+δ)
  let b := min (D/2) ⌊(3/4)*sizeScale m⌋₊
  let f := fun k => rankCount m (D-k)
  obtain ⟨⟨p,hlp,hpb,hinc,hdec⟩,tail⟩ := h
  have hb : b ≤ D/2 := min_le_left ..
  change UnimodalOn f _ (D/2)
  refine ⟨p,hlp,hpb.trans hb,hinc,?_⟩
  intro k hpk hk
  by_cases hkb : k<b
  · exact hdec k hpk hkb
  have hx : ⌊(3/4)*sizeScale m⌋₊ ≤ k := by
    have he : b ≤ k := by omega
    dsimp only [b] at he; omega
  have hlow : (3/4)*sizeScale m ≤ (k:ℝ)+1 :=
    (Nat.lt_floor_add_one _).le.trans (by exact_mod_cast Nat.add_le_add_right hx 1)
  by_cases hh : (k:ℝ)+1 ≤ 2*sizeScale m
  · have hD : staircaseDegree m=D := staircaseDegree_parity n δ hδ
    have H := corank_flank_decreases (m:=m) (k:=k) hm (by rwa [hD] : k<staircaseDegree m/2) hlow hh
    change rankCount m (D-(k+1)) ≤ rankCount m (D-k)
    simpa only [hD] using H.le
  · exact tail k (show b ≤ k from Nat.le_of_not_gt hkb) hk (lt_of_not_ge hh)

/-- A route to the full statement with the entire checked flank removed
from its hypotheses for m ≥ 4096. -/
theorem conjecture34_of_remaining_windows (hD : DyckComparisons)
    (hsmall : ∀ n ≥ 96, ∀ δ ≤ 1, 2*n+δ < 4096 → CentralToMidpoint n δ)
    (hbig : ∀ n ≥ 96, ∀ δ ≤ 1, 4096 ≤ 2*n+δ → RemainingMidpoint n δ) :
    Conjecture34 := by
  apply conjecture34_of_comparisons_and_midpoints hD
  intro n hn δ hδ
  by_cases hm : 4096 ≤ 2*n+δ
  · exact midpoint_of_remaining hm hδ (hbig n hn δ hδ hm)
  · exact hsmall n hn δ hδ (by omega)

end CentralUnimodality
