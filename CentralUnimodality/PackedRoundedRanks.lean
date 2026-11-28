module

public import CentralUnimodality.PackedRoundedLayers
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Reassemble endpoint deficit rows at their actual coranks. The rounded
coefficients at a fixed rank sum to at most the initial unit, so addition
of the shifted endpoint integers preserves every required digit. -/
@[expose] public section

namespace CentralUnimodality.EndpointDeficit

theorem roundedRank_le (u m j : ℕ) : roundedRank u m j ≤ u := by
  have H := (roundedRank_bounds u m j).1
  have C : rankCount m j ≤ 2^m := by
    rw [rankCount_eq_card]
    exact (Finset.card_filter_le ..).trans (card_allPartitions_le m)
  have h := Nat.le_of_mul_le_mul_right (H.trans (Nat.mul_le_mul_left (2*u) C)) (Nat.two_pow_pos m)
  omega

private theorem digit_total {α : Type*} [DecidableEq α] (b : ℕ) (f : α → ℕ)
    (s : Finset α) (i : ℕ)
    (H : ∀ j≤i, ∑ d ∈ s, digit b (f d) j < 2^b) :
    digit b (∑ d ∈ s, f d) i = ∑ d ∈ s, digit b (f d) i := by
  induction s using Finset.induction_on generalizing i with
  | empty => simp [digit]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha] at H ⊢
    have subsum (j : ℕ) (hj : j≤i) :
        digit b (∑ d ∈ s, f d) j = ∑ d ∈ s, digit b (f d) j := by
      apply ih
      intro t ht
      have := H t (by omega)
      omega
    rw [digit_add (fun j hj => by rw [subsum j hj]; exact H j hj),subsum i (by omega)]

/-- Pack the endpoint rows in order of increasing actual corank. -/
def combine (w n m D : ℕ) (row : List ℕ) : ℕ :=
  ((List.range (m/2+1)).map fun d =>
    let offset := D-d*(m-d)
    if offset<n then entry row d <<< ((w+1)*offset) else 0).sum

private theorem sum_range_eq (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ d ∈ Finset.range n, f d := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem endpoint_degree_le {m d : ℕ} (hd : d≤m) : d*(m-d)≤m*m/4 := by
  rw [Nat.le_div_iff_mul_le (by decide : 0<4)]
  have h : 4*(d:ℤ)*((m:ℤ)-d) ≤ (m:ℤ)*m := by nlinarith only [sq_nonneg ((m:ℤ)-2*d)]
  zify [hd]
  linarith only [h]

theorem combine_digit {w u n m i : ℕ} (hu : u<2^w) (hi : i<n) (hD : i≤m*m/4) :
    digit (w+1) (combine w n m (m*m/4) (roundedLayers w n u m)) i =
      roundedRank u m (m*m/4-i) := by
  let D := m*m/4
  let row := roundedLayers w n u m
  let part (d : ℕ) :=
    let offset := D-d*(m-d)
    if offset<n then entry row d <<< ((w+1)*offset) else 0
  have atRank (j d : ℕ) (hj : j≤i) (hd : d∈Finset.range (m/2+1)) :
      digit (w+1) (part d) j = rounded u m d ((m:ℤ)*d-(d:ℤ)^2-(D-j:ℕ)) := by
    have hdm : d≤m := by have := Finset.mem_range.mp hd; omega
    let a := D-d*(m-d)
    have hmax := endpoint_degree_le hdm
    have ha : (a:ℤ)=(D:ℤ)-((m:ℤ)*d-(d:ℤ)^2) := by
      dsimp only [a]; rw [Int.natCast_sub hmax,Nat.cast_mul,Int.natCast_sub hdm]; ring
    have diff : (m:ℤ)*d-(d:ℤ)^2-(D-j:ℕ)=(j:ℤ)-a := by
      rw [Int.natCast_sub (by dsimp [D]; omega : j≤D)]; linarith only [ha]
    rw [diff]
    change digit (w+1) (if a<n then _ else 0) j=_
    by_cases h : a≤j
    · rw [ite_eq_left (by omega : a<n),digit_left,ite_eq_left h,roundedLayers_digit hu,
        ite_eq_left (by omega : j-a<n),Int.natCast_sub h]
    · rw [rounded_zero_of_count (count_negative (by omega : (j:ℤ)-a<0))]
      split
      · rw [digit_left,ite_eq_right h]
      · simp [digit]
  have sumAt (j : ℕ) (hj : j≤i) :
      ∑ d ∈ Finset.range (m/2+1), digit (w+1) (part d) j=roundedRank u m (D-j) :=
    Finset.sum_congr rfl (fun d hd => atRank j d hj hd)
  have small (j : ℕ) (hj : j≤i) :
      ∑ d ∈ Finset.range (m/2+1), digit (w+1) (part d) j < 2^(w+1) := by
    rw [sumAt j hj,pow_succ]
    have := roundedRank_le u m (D-j)
    omega
  rw [combine,sum_range_eq]
  change digit (w+1) (∑ d ∈ Finset.range (m/2+1), part d) i=_
  rw [digit_total _ _ _ _ small,sumAt i (by omega)]

end CentralUnimodality.EndpointDeficit
