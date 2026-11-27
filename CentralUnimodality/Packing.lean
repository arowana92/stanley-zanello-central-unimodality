module

public import CentralUnimodality.Ranks
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort

/-! Evaluation at a power of two computes many exact coefficients in a single
natural number. The digit lemma bounds all possible carries by the number of
partitions, independently of the computation. -/
@[expose] public section

namespace CentralUnimodality

theorem lt_of_mem_of_fits {m a : ℕ} {l : List ℕ} (hf : Fits m l) (ha : a ∈ l) : a < m := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    obtain ⟨_, _, hb, ht⟩ := fits_cons.mp hf
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · exact ih ht ha

theorem card_allPartitions_le (m : ℕ) : (allPartitions m).card ≤ 2^m := by
  have hs (l : List ℕ) (hl : l ∈ allPartitions m) : l.toFinset.sort (· ≤ ·) = l := by
    have hp := (mem_allPartitions.mp hl).1
    exact (List.toFinset_sort (· ≤ ·) (hp.imp Nat.ne_of_lt)).mpr (hp.imp Nat.le_of_lt)
  have inj : Set.InjOn List.toFinset (allPartitions m : Set (List ℕ)) := by
    intro x hx y hy hxy
    rw [← hs x hx, ← hs y hy, hxy]
  have maps : Set.MapsTo List.toFinset (allPartitions m : Set (List ℕ))
      ((Finset.range m).powerset : Set (Finset ℕ)) := by
    intro l hl
    apply Finset.mem_powerset.mpr
    intro x hx
    exact Finset.mem_range.mpr (lt_of_mem_of_fits (mem_allPartitions.mp hl) (List.mem_toFinset.mp hx))
  simpa using Finset.card_le_card_of_injOn List.toFinset maps inj

/-- Digit extraction for any finite collection of nonnegative integer weights. -/
theorem digit_weight_sum {α : Type*} (s : Finset α) (w : α → ℕ) (b j : ℕ) (hb : s.card < b) :
    ((∑ x ∈ s, b^(w x)) / b^j) % b = (s.filter fun x => w x = j).card := by
  let lo := ∑ x ∈ s, if w x < j then b^(w x) else 0
  let mid := ∑ x ∈ s, if w x = j then 1 else 0
  let hi := ∑ x ∈ s, if j < w x then b^(w x-(j+1)) else 0
  have hm : mid = (s.filter fun x => w x = j).card := by
    simp [mid]
  have hmid : mid < b := hm ▸ lt_of_le_of_lt (Finset.card_filter_le _ _) hb
  have bpos : 0 < b := by omega
  have hl : lo < b^j := by
    cases j with
    | zero => simp [lo]
    | succ k =>
      calc
        _ ≤ ∑ _x ∈ s, b^k := by
          apply Finset.sum_le_sum
          intro x _
          split
          next h => exact Nat.pow_le_pow_right bpos (by omega)
          next => omega
        _ = s.card * b^k := by simp
        _ < b * b^k := Nat.mul_lt_mul_of_pos_right hb (Nat.pow_pos bpos)
        _ = _ := Nat.pow_succ'.symm
  have hsum : (∑ x ∈ s, b^(w x)) = lo + b^j * (mid + b*hi) := by
    simp only [lo, mid, hi, Nat.mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rcases lt_trichotomy (w x) j with h | h | h
    · simp [h, Nat.ne_of_lt h, Nat.not_lt_of_ge (Nat.le_of_lt h)]
    · simp [h]
    · have hw : w x = j + (1 + (w x-(j+1))) := by omega
      simp [h, Nat.not_lt_of_ge (Nat.le_of_lt h), Nat.ne_of_gt h]
      calc
        b^(w x) = b^(j + (1 + (w x-(j+1)))) := congrArg (b^·) hw
        _ = _ := by simp [Nat.pow_add]
  rw [hsum, Nat.add_mul_div_left lo _ (Nat.pow_pos bpos), Nat.div_eq_of_lt hl,
    Nat.zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hmid, hm]

def weightByLength (b m d : ℕ) : ℕ := ∑ l ∈ partitions m d, b^l.sum

theorem weight_zero_parts (b m : ℕ) : weightByLength b m 0 = 1 := by
  cases m <;> simp [weightByLength, partitions]

theorem weight_zero_of_length {b m d : ℕ} (hd : m < 2*d) : weightByLength b m d = 0 := by
  have hemp : partitions m d = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro l hl
    obtain ⟨hf, hlen⟩ := mem_partitions.mp hl
    have := fits_length_le hf
    omega
  simp [weightByLength, hemp]

theorem weight_step (b m d : ℕ) (hd : 2*(d+1) ≤ m+1) :
    weightByLength b (m+1) (d+1) =
      (weightByLength b m (d+1) + weightByLength b m d) * b^(d+1) := by
  simp only [weightByLength, partitions, ite_eq_left hd, Finset.sum_union (disjoint_step m d),
    Finset.sum_image raiseParts_injective.injOn, Finset.sum_image insertOne_injective.injOn,
    Nat.add_mul, Finset.sum_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro l hl
    rw [raiseParts_sum, (mem_partitions.mp hl).2, Nat.pow_add]
  · apply Finset.sum_congr rfl
    intro l hl
    have hs : (insertOne l).sum = l.sum + (d+1) := by
      have := (mem_partitions.mp hl).2
      simp only [insertOne, List.sum_cons, raiseParts_sum]
      omega
    rw [hs, Nat.pow_add]

end CentralUnimodality
