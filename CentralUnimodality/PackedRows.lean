module

public import CentralUnimodality.Packing

/-! An executable recurrence for the exact integer containing a whole rank row. -/
@[expose] public section

namespace CentralUnimodality

def entry (row : List ℕ) (i : ℕ) : ℕ := row[i]?.getD 0

private theorem entry_range (f : ℕ → ℕ) (n i : ℕ) :
    entry ((List.range n).map f) i = if i < n then f i else 0 := by
  by_cases h : i < n <;> simp [entry, h]

def nextLayer (bits m : ℕ) (row : List ℕ) : List ℕ :=
  (List.range (m/2+1)).map fun
    | 0 => 1
    | d+1 => (entry row (d+1) + entry row d) <<< (bits*(d+1))

def packedLayers (bits : ℕ) : ℕ → List ℕ
  | 0 => [1]
  | m+1 => nextLayer bits (m+1) (packedLayers bits m)

theorem packedLayers_eq (bits m : ℕ) :
    packedLayers bits m = (List.range (m/2+1)).map (weightByLength (2^bits) m) := by
  induction m with
  | zero => simp [packedLayers, List.range_succ, weight_zero_parts]
  | succ m ih =>
    rw [packedLayers, nextLayer, ih]
    apply List.map_congr_left
    intro i hi
    have he (d : ℕ) :
        entry ((List.range (m/2+1)).map (weightByLength (2^bits) m)) d =
          weightByLength (2^bits) m d := by
      rw [entry_range]
      split
      next => rfl
      next h => exact (weight_zero_of_length (by omega)).symm
    cases i with
    | zero => exact (weight_zero_parts _ _).symm
    | succ d =>
      have hd := List.mem_range.mp hi
      simp only [he, Nat.shiftLeft_eq, Nat.pow_mul]
      exact (weight_step _ _ _ (by omega)).symm

private theorem sum_map_range (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

def packedRow (bits m : ℕ) : ℕ := (packedLayers bits m).sum

theorem packedRow_eq (bits m : ℕ) :
    packedRow bits m = ∑ l ∈ allPartitions m, (2^bits)^l.sum := by
  rw [packedRow, packedLayers_eq, sum_map_range, allPartitions, Finset.sum_biUnion]
  · rfl
  · exact fun _ _ _ _ h => disjoint_lengths h

def digit (bits value j : ℕ) : ℕ := (value >>> (bits*j)) % 2^bits

theorem packedRow_digit (bits m j : ℕ) (hm : m < bits) :
    digit bits (packedRow bits m) j = rankCount m j := by
  have hb : (allPartitions m).card < 2^bits := lt_of_le_of_lt (card_allPartitions_le m)
    (Nat.pow_lt_pow_right (by decide) hm)
  rw [digit, Nat.shiftRight_eq_div_pow, Nat.pow_mul, packedRow_eq, rankCount_eq_card]
  exact digit_weight_sum _ _ _ _ hb

end CentralUnimodality
