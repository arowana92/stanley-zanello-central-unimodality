module

public import CentralUnimodality.Partitions
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! The literal rank counts and their exact positive recurrence. -/
@[expose] public section

namespace CentralUnimodality

def rankCountLength (m d j : ℕ) : ℕ :=
  ((partitions m d).filter fun l => l.sum = j).card

/-- Number of strict partitions of rank `j` in the staircase of ballot length `m`. -/
def rankCount (m j : ℕ) : ℕ :=
  ∑ d ∈ Finset.range (m/2+1), rankCountLength m d j

def allPartitions (m : ℕ) : Finset (List ℕ) :=
  (Finset.range (m/2+1)).biUnion (partitions m)

theorem mem_allPartitions {m : ℕ} {l : List ℕ} : l ∈ allPartitions m ↔ Fits m l := by
  constructor
  · intro h
    obtain ⟨_, _, ht⟩ := Finset.mem_biUnion.mp h
    exact (mem_partitions.mp ht).1
  · intro h
    have := fits_length_le h
    exact Finset.mem_biUnion.mpr ⟨l.length, Finset.mem_range.mpr (by omega),
      mem_partitions.mpr ⟨h, rfl⟩⟩

theorem disjoint_lengths {m d e : ℕ} (hne : d ≠ e) :
    Disjoint (partitions m d) (partitions m e) := by
  apply Finset.disjoint_left.mpr
  intro l hd he
  exact hne ((mem_partitions.mp hd).2.symm.trans (mem_partitions.mp he).2)

theorem rankCount_eq_card (m j : ℕ) :
    rankCount m j = ((allPartitions m).filter fun l => l.sum = j).card := by
  let s := Finset.range (m/2+1)
  let atRank := fun d => (partitions m d).filter fun l => l.sum = j
  have he : (allPartitions m).filter (fun l => l.sum = j) = s.biUnion atRank := by
    ext l
    simp [allPartitions, s, atRank]
    grind
  rw [he, Finset.card_biUnion]
  · rfl
  · intro a _ b _ hne
    exact (disjoint_lengths hne).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- There is a peak with weak adjacent inequalities on either side. -/
def UnimodalOn (f : ℕ → ℕ) (lo hi : ℕ) : Prop :=
  ∃ peak, lo ≤ peak ∧ peak ≤ hi ∧
    (∀ j, lo ≤ j → j < peak → f j ≤ f (j+1)) ∧
    (∀ j, peak ≤ j → j < hi → f (j+1) ≤ f j)

/-- Conjecture 3.4 with the odd-part and even-part bounding shapes, respectively. -/
def Conjecture34 : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    UnimodalOn (rankCount (2*n)) 0 (n*n) ∧
    UnimodalOn (rankCount (2*n+1)) 0 (n*(n+1))

theorem rankCountLength_zero_parts (m j : ℕ) :
    rankCountLength m 0 j = if j = 0 then 1 else 0 := by
  cases m <;> cases j <;> simp [rankCountLength, partitions, Finset.filter_singleton]

theorem rankCountLength_zero_of_length {m d j : ℕ} (h : m < 2*d) :
    rankCountLength m d j = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro l hl
  obtain ⟨hf, hlen⟩ := mem_partitions.mp (Finset.mem_filter.mp hl).1
  have := fits_length_le hf
  omega

theorem length_le_sum_of_positive {l : List ℕ} (hp : PositiveParts l) :
    l.length ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have := ih (fun b hb => hp b (List.mem_cons_of_mem _ hb))
    have := hp a (by simp)
    simp only [List.length_cons, List.sum_cons]
    omega

theorem rankCountLength_zero_of_rank {m d j : ℕ} (h : j < d) :
    rankCountLength m d j = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro l hl
  obtain ⟨hl, hs⟩ := Finset.mem_filter.mp hl
  obtain ⟨hf, hlen⟩ := mem_partitions.mp hl
  have := length_le_sum_of_positive hf.2.1
  omega

theorem disjoint_step (m d : ℕ) :
    Disjoint ((partitions m (d+1)).image raiseParts) ((partitions m d).image insertOne) := by
  apply Finset.disjoint_left.mpr
  intro l hl hr
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hr
  have hone : 1 ∈ raiseParts t := hv ▸ List.mem_cons_self
  obtain ⟨a, ha, he⟩ := List.mem_map.mp hone
  have := (mem_partitions.mp ht).1.2.1 a ha
  change a+1 = 1 at he
  omega

private theorem card_shift_image (m d j e : ℕ) (f : List ℕ → List ℕ)
    (hi : Function.Injective f) (hs : ∀ l ∈ partitions m d, (f l).sum = l.sum+e) :
    (((partitions m d).image f).filter (fun l => l.sum = j+e)).card = rankCountLength m d j := by
  rw [Finset.filter_image, Finset.card_image_of_injective _ hi]
  unfold rankCountLength
  congr 1
  apply Finset.filter_congr
  intro l hl
  rw [hs l hl]
  omega

/-- At every admissible positive length, appending a ballot step shifts the
rank of either predecessor by the new number of parts. -/
theorem rankCountLength_step (m d j : ℕ) (hd : 2*(d+1) ≤ m+1) :
    rankCountLength (m+1) (d+1) (j+(d+1)) =
      rankCountLength m (d+1) j + rankCountLength m d j := by
  conv_lhs => unfold rankCountLength
  rw [partitions, ite_eq_left hd, Finset.filter_union,
    Finset.card_union_of_disjoint ((disjoint_step m d).mono (Finset.filter_subset _ _)
      (Finset.filter_subset _ _))]
  congr 1
  · apply card_shift_image _ _ _ _ _ raiseParts_injective
    intro l hl
    rw [raiseParts_sum, (mem_partitions.mp hl).2]
  · apply card_shift_image _ _ _ _ _ insertOne_injective
    intro l hl
    have := (mem_partitions.mp hl).2
    simp only [insertOne, List.sum_cons, raiseParts_sum]
    omega

/-- The recurrence with natural-number indices, including all boundary cases. -/
theorem rankCountLength_succ (m d j : ℕ) :
    rankCountLength (m+1) (d+1) j =
      if 2*(d+1) ≤ m+1 ∧ d+1 ≤ j then
        rankCountLength m (d+1) (j-(d+1)) + rankCountLength m d (j-(d+1))
      else 0 := by
  split
  next h =>
    have H := rankCountLength_step m d (j-(d+1)) h.1
    rwa [Nat.sub_add_cancel h.2] at H
  next h =>
    by_cases hlen : m+1 < 2*(d+1)
    · exact rankCountLength_zero_of_length hlen
    · exact rankCountLength_zero_of_rank (by omega)

end CentralUnimodality
