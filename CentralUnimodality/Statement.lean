module

public import CentralUnimodality.Ranks
import Mathlib.Tactic.Ring

/-! The staircase bounds in the usual decreasing-part convention. -/
@[expose] public section

namespace CentralUnimodality

/-- In zero-based row i the bounding part is 2(n-1-i)+1+δ, where δ is
zero for (2n-1,2n-3,...,1) and one for (2n,2n-2,...,2). -/
def InsideStaircase (n δ : ℕ) (μ : List ℕ) : Prop :=
  μ.Pairwise (· > ·) ∧ PositiveParts μ ∧ μ.length ≤ n ∧
    ∀ i (hi : i < μ.length), μ[i] ≤ 2*(n-1-i)+1+δ

theorem rowBounds_iff_index (m : ℕ) (l : List ℕ) :
    RowBounds m l ↔ ∀ i (hi : i < l.length), l[i] + 2*(l.length-1-i) < m := by
  induction l with
  | nil => simp [RowBounds]
  | cons a l ih =>
    constructor
    · intro ⟨h, ht⟩ i hi
      cases i with
      | zero => simpa using h
      | succ i =>
        have hb := ih.mp ht i (by simpa using hi)
        simpa [Nat.sub_sub, Nat.add_comm] using hb
    · intro h
      refine ⟨?_, ih.mpr ?_⟩
      · have hx := h 0 (by simp)
        change a + 2*((l.length+1)-1-0) < m at hx
        simpa using hx
      · intro i hi
        have hx := h (i+1) (by simpa using hi)
        change l[i] + 2*((l.length+1)-1-(i+1)) < m at hx
        simpa [Nat.sub_sub, Nat.add_comm] using hx

theorem fits_iff_inside_reverse (n δ : ℕ) (hδ : δ ≤ 1) (l : List ℕ) :
    Fits (2*n+δ) l ↔ InsideStaircase n δ l.reverse := by
  have hpos : PositiveParts l.reverse ↔ PositiveParts l := by simp [PositiveParts]
  simp only [InsideStaircase, List.pairwise_reverse, hpos, List.length_reverse]
  constructor
  · intro hf
    have hlen := fits_length_le hf
    refine ⟨hf.1, hf.2.1, by omega, ?_⟩
    intro i hi
    have hj : l.length-1-i < l.length := by omega
    have ha := (rowBounds_iff_index _ _).mp hf.2.2 (l.length-1-i) hj
    rw [List.getElem_reverse]
    rw [show l.length - 1 - (l.length-1-i) = i by omega] at ha
    omega
  · rintro ⟨hp, hposl, hlen, hb⟩
    refine ⟨hp, hposl, (rowBounds_iff_index _ _).mpr ?_⟩
    intro i hi
    have hj : l.length-1-i < l.length := by omega
    have ha := hb (l.length-1-i) hj
    simp only [List.getElem_reverse, show l.length-1-(l.length-1-i) = i by omega] at ha
    omega

def containedPartitions (n δ : ℕ) : Finset (List ℕ) :=
  (allPartitions (2*n+δ)).image List.reverse

theorem mem_containedPartitions {n δ : ℕ} (hδ : δ ≤ 1) (μ : List ℕ) :
    μ ∈ containedPartitions n δ ↔ InsideStaircase n δ μ := by
  constructor
  · intro h
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp h
    exact (fits_iff_inside_reverse _ _ hδ _).mp (mem_allPartitions.mp hl)
  · intro h
    refine Finset.mem_image.mpr ⟨μ.reverse, mem_allPartitions.mpr ?_, List.reverse_reverse μ⟩
    apply (fits_iff_inside_reverse _ _ hδ _).mpr
    simpa using h

def staircaseRank (n δ j : ℕ) : ℕ :=
  ((containedPartitions n δ).filter fun μ => μ.sum = j).card

theorem staircaseRank_eq (n δ j : ℕ) : staircaseRank n δ j = rankCount (2*n+δ) j := by
  rw [staircaseRank, containedPartitions, Finset.filter_image,
    Finset.card_image_of_injective _ List.reverse_injective, rankCount_eq_card]
  simp

/-- A statement entirely in terms of the decreasing partitions counted by rank. -/
theorem conjecture34_iff_staircase :
    Conjecture34 ↔ ∀ n : ℕ, 1 ≤ n →
      UnimodalOn (staircaseRank n 0) 0 (n*n) ∧
      UnimodalOn (staircaseRank n 1) 0 (n*(n+1)) := by
  have he (n δ : ℕ) : staircaseRank n δ = rankCount (2*n+δ) := funext (staircaseRank_eq n δ)
  simp only [Conjecture34, he, Nat.add_zero]

/-- The complete possible degree range is bounded by the area of the staircase. -/
theorem sum_bound_length {m : ℕ} {l : List ℕ} (hf : Fits m l) :
    l.sum + l.length*l.length ≤ m*l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨_, _, hb, ht⟩ := fits_cons.mp hf
    have hs := ih ht
    simp only [List.sum_cons, List.length_cons, Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one]
    omega

theorem sum_le_staircase_area {n δ : ℕ} (hδ : δ ≤ 1) {μ : List ℕ}
    (hμ : InsideStaircase n δ μ) : μ.sum ≤ n*(n+δ) := by
  have hf : Fits (2*n+δ) μ.reverse :=
    (fits_iff_inside_reverse _ _ hδ _).mpr (by simpa using hμ)
  have hb := sum_bound_length hf
  simp only [List.length_reverse, List.sum_reverse] at hb
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hμ.2.2.1
  have hcost : n*(n+δ) + μ.length*μ.length = (2*n+δ)*μ.length + r*(r+δ) := by
    rw [hr]; ring
  omega

end CentralUnimodality
