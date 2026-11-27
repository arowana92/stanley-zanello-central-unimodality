module

public import CentralUnimodality.ReflectedMoments
public import CentralUnimodality.SampledFirst
public import CentralUnimodality.SecondWitnessCheck

/-! For both staircase families the reflected corank comparisons required
in the prefix induction follow from unimodality at that same size. -/
@[expose] public section

namespace CentralUnimodality

private theorem reflectedLimit_sq {m i j : ℕ} (hij : i < j) (hc : i+j ≤ reflectedLimit m) :
    (250*(i+j+(m+1+(m+1)/2)))^2 ≤ 131^2*(2*((m+1)/2))^3 := by
  apply Nat.le_sqrt'.mp
  rw [Nat.mul_comm]
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 250)).mp
  unfold reflectedLimit at hc
  omega

/-- This is an implication at each size. Only smaller unimodal rows are
used when applying it in the prefix induction. -/
theorem reflected_of_unimodal {n δ : ℕ} (hδ : δ ≤ 1)
    (hu : UnimodalOn (rankCount (2*n+δ)) 0 (n*(n+δ))) {i j : ℕ} (hij : i < j)
    (hc : i+j ≤ reflectedLimit (2*n+δ)) :
    rankCount (2*n+δ) (n*(n+δ)-i) ≤ rankCount (2*n+δ) (n*(n+δ)-j) := by
  by_cases hn : 96 ≤ n+δ
  · refine Witness.reflected_large_of_expectations hδ hn ?_ ?_ hu hij ?_
    · exact (Witness.first_expectation hδ hn).trans_lt (by norm_num)
    · exact (Witness.second_expectation hδ hn).trans_lt (by norm_num)
    · have h := reflectedLimit_sq hij hc
      have hN : (2*n+δ+1)/2 = n+δ := by omega
      rw [hN,show i+j+(2*n+δ+1+(n+δ)) = i+j+3*(n+δ)+(1-δ) by omega] at h
      exact h
  · have h := (reflected_through_191 (m := 2*n+δ) (by omega)).2 i j hij hc
    rcases (by omega : δ = 0 ∨ δ = 1) with rfl|rfl
    · simpa only [Nat.add_zero,odd_degree] using h
    · simpa only [even_degree] using h

end CentralUnimodality
