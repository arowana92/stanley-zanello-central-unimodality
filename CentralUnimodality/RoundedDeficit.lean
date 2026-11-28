module

public import CentralUnimodality.EndpointDeficit
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Integer lower enclosures for normalized ballot counts. Rounding down after
a half-sum loses at most half a unit. The error at an endpoint after `m`
steps is at most `m/2` units, even with missing predecessors at the wall. -/
@[expose] public section

namespace CentralUnimodality.EndpointDeficit

def rounded (unit : ℕ) : ℕ → ℕ → ℤ → ℕ
  | 0, d, i => if d=0 ∧ i=0 then unit else 0
  | m+1, 0, i => rounded unit m 0 i / 2
  | m+1, d+1, i =>
    if (2 * (d + 1) ≤ m + 1) ∧ (0 ≤ i) then
      (rounded unit m (d+1) i + rounded unit m d (i-(m+1-2*(d+1):ℕ))) / 2
    else 0

/-- Doubled units express the half-unit roundoff with all-natural arithmetic. -/
def Encloses (unit m a v : ℕ) : Prop :=
  (2*a)*2^m ≤ 2*unit*v ∧ 2*unit*v ≤ (2*a+m)*2^m

private theorem encloses_zero (unit m : ℕ) : Encloses unit m 0 0 := by
  simp [Encloses]

private theorem encloses_average {unit m a b v w : ℕ}
    (ha : Encloses unit m a v) (hb : Encloses unit m b w) :
    Encloses unit (m+1) ((a+b)/2) (v+w) := by
  obtain ⟨ha₁,ha₂⟩ := ha
  obtain ⟨hb₁,hb₂⟩ := hb
  have h₁ := Nat.mul_le_mul_right (2^m) (show 2*((a+b)/2) ≤ a+b by omega)
  have h₂ := Nat.mul_le_mul_right (2^m) (show a+b ≤ 2*((a+b)/2)+1 by omega)
  unfold Encloses
  rw [pow_succ]
  constructor <;> nlinarith only [ha₁,ha₂,hb₁,hb₂,h₁,h₂]

theorem rounded_encloses (unit m d : ℕ) (i : ℤ) :
    Encloses unit m (rounded unit m d i) (count m d i) := by
  induction m generalizing d i with
  | zero =>
    cases d with
    | zero =>
      rw [count_zero_parts]; by_cases h : i=0 <;> simp [rounded,Encloses,h]
    | succ d =>
      rw [count_illegal (by omega : 0<2*(d+1))]
      simp [rounded,Encloses]
  | succ m ih =>
    cases d with
    | zero =>
      have H := encloses_average (ih 0 i) (encloses_zero unit m)
      simpa [rounded,count_zero_parts] using H
    | succ d =>
      unfold rounded
      split
      next h =>
        rw [count_step _ _ _ h.1]
        exact encloses_average (ih _ _) (ih _ _)
      next h =>
        by_cases hd : 2*(d+1)≤m+1
        · rw [count_negative (by omega : i<0)]
          exact encloses_zero _ _
        · rw [count_illegal (by omega : m+1<2*(d+1))]
          exact encloses_zero _ _

def roundedRank (unit m j : ℕ) : ℕ :=
  ∑ d ∈ Finset.range (m/2+1), rounded unit m d ((m:ℤ)*d-(d:ℤ)^2-j)

theorem roundedRank_bounds (unit m j : ℕ) :
    (2*roundedRank unit m j)*2^m ≤ 2*unit*rankCount m j ∧
      2*unit*rankCount m j ≤ (2*roundedRank unit m j+(m/2+1)*m)*2^m := by
  rw [rank_eq_sum]
  unfold roundedRank
  have h (d : ℕ) := rounded_encloses unit m d ((m:ℤ)*d-(d:ℤ)^2-j)
  have lo := Finset.sum_le_sum (s := Finset.range (m/2+1)) fun d _ => (h d).1
  have hi := Finset.sum_le_sum (s := Finset.range (m/2+1)) fun d _ => (h d).2
  simp only [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul] at lo hi
  exact ⟨lo,hi⟩

/-- Disjoint integer enclosures certify a strict comparison of literal ranks. -/
theorem rank_lt_of_separated {unit m i j : ℕ}
    (h : 2*roundedRank unit m i+(m/2+1)*m < 2*roundedRank unit m j) :
    rankCount m i < rankCount m j := by
  have H := (roundedRank_bounds unit m i).2.trans_lt
    ((Nat.mul_lt_mul_of_pos_right h (by positivity : 0<2^m)).trans_le
      (roundedRank_bounds unit m j).1)
  exact Nat.lt_of_mul_lt_mul_left H

end CentralUnimodality.EndpointDeficit
