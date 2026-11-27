module

public import CentralUnimodality.SignedRanks
public import Mathlib.Data.Nat.Choose.Basic

/-! Exact normalization of the rank and signed-area laws. Counting the
partitions with a fixed number of parts gives the ballot triangle. -/
@[expose] public section

namespace CentralUnimodality

private def prevChoose (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | d+1 => m.choose d

private theorem prevChoose_succ (m d : ℕ) :
    prevChoose (m+1) (d+1) = prevChoose m d + prevChoose m (d+1) := by
  cases d with
  | zero => simp [prevChoose]
  | succ d => exact Nat.choose_succ_succ m d

/-- The equality also holds one place beyond the last possible length in an
odd ballot row, where the two binomial coefficients coincide. -/
private theorem card_partitions_add_prev (m d : ℕ) (hd : 2*d ≤ m+1) :
    (partitions m d).card + prevChoose m d = m.choose d := by
  induction m generalizing d with
  | zero =>
    have h : d = 0 := by omega
    simp [h, partitions, prevChoose]
  | succ m ih =>
    cases d with
    | zero => simp [partitions, prevChoose]
    | succ d =>
      by_cases ha : 2*(d+1) ≤ m+1
      · rw [partitions, ite_eq_left ha, Finset.card_union_of_disjoint (disjoint_step m d),
          Finset.card_image_of_injective _ raiseParts_injective,
          Finset.card_image_of_injective _ insertOne_injective, prevChoose_succ, Nat.choose_succ_succ]
        have h₁ := ih d (by omega)
        have h₂ := ih (d+1) ha
        simp only [Nat.succ_eq_add_one] at *
        omega
      · have hem : partitions (m+1) (d+1) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro l hl
          obtain ⟨hf, he⟩ := mem_partitions.mp hl
          have := fits_length_le hf
          omega
        rw [hem, Finset.card_empty, zero_add]
        exact Nat.choose_symm_of_eq_add (by omega : m+1 = d+(d+1))

theorem card_partitions_length (m d : ℕ) (hd : 2*(d+1) ≤ m+1) :
    (partitions m (d+1)).card + m.choose d = m.choose (d+1) :=
  card_partitions_add_prev m (d+1) hd

theorem sum_card_partitions (m d : ℕ) (hd : 2*d ≤ m+1) :
    ∑ i ∈ Finset.range (d+1), (partitions m i).card = m.choose d := by
  induction d with
  | zero => cases m <;> simp [partitions]
  | succ d ih =>
    rw [Finset.sum_range_succ, ih (by omega), Nat.add_comm, card_partitions_length m d hd]

theorem card_allPartitions (m : ℕ) : (allPartitions m).card = m.choose (m/2) := by
  rw [allPartitions, Finset.card_biUnion (fun _ _ _ _ h => disjoint_lengths h)]
  exact sum_card_partitions m (m/2) (by omega)

theorem sum_rankCount (n δ : ℕ) (hδ : δ ≤ 1) :
    (∑ j ∈ Finset.range (n*(n+δ)+1), rankCount (2*n+δ) j) = (2*n+δ).choose n := by
  have h := sum_over_ranks (fun _ => (1:ℕ)) n δ hδ
  have hm : (2*n+δ)/2 = n := by omega
  simpa [card_allPartitions, hm] using h.symm

theorem card_strictWords (n δ : ℕ) (hδ : δ ≤ 1) :
    (strictWords (2*n+δ+1)).card = 2 * (2*n+δ).choose n := by
  have h := signed_ranks (fun _ => (1:ℕ)) n δ hδ
  rw [mul_comm 2 ((2*n+δ).choose n), ← sum_rankCount n δ hδ, Finset.sum_mul]
  simpa using h

theorem card_strictWords_even (n : ℕ) : (strictWords (2*n)).card = (2*n).choose n := by
  cases n with
  | zero => decide
  | succ n =>
    have he : 2*(n+1) = (2*n+1)+1 := by omega
    rw [he, Nat.choose_succ_succ, Nat.choose_symm_half, ← two_mul]
    exact card_strictWords n 1 (by decide)

theorem card_strictWords_odd (n : ℕ) : (strictWords (2*n+1)).card = 2 * (2*n).choose n := by
  simpa using card_strictWords n 0 (by decide)

end CentralUnimodality
