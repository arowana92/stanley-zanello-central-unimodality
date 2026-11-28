module

public import CentralUnimodality.MarkedExcursionTail
import Mathlib.Data.Nat.Choose.Sum

/-! The total area of the positive first-return excursions of length
`2*(d+1)` equals `4^d`. Summing the exact height tails of a marked
interior Dyck path reduces the moment to half an odd binomial row. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion

private theorem sum_tail_cards (d : ℕ) :
    (marks d).card + ∑ i ∈ Finset.range d, (tail d (i+1)).card = 4^d := by
  let f := fun i : ℕ => (2*d+1).choose (d-i)
  have tails : ∀ i ∈ Finset.range d, (tail d (i+1)).card=f (i+1) := by
    intro i hi; exact card_tail (Finset.mem_range.mp hi)
  rw [card_marks,Finset.sum_congr rfl tails]
  change f 0 + ∑ i ∈ Finset.range d, f (i+1) = _
  rw [Nat.add_comm,← Finset.sum_range_succ']
  have rev := Finset.sum_range_reflect ((2*d+1).choose ·) (d+1)
  simpa [f,Nat.sum_range_choose_halfway] using rev

theorem excursion_area_sum (d : ℕ) :
    ∑ w ∈ dycks d, ((walkArea w:ℝ)+(2*d+1)) = 4^d := by
  let f := fun i : ℕ => (i:ℝ)+1
  have h := sum_height d f
  have step' (i : ℕ) : f (i+1)-f i=1 := by simp [f]
  simp only [step',mul_one,show f 0=1 by simp [f]] at h
  have total : ((marks d).card:ℝ)+∑ i ∈ Finset.range d, ((tail d (i+1)).card:ℝ)=4^d := by
    exact_mod_cast sum_tail_cards d
  rw [← total,← h]
  unfold marks
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro w hw
  have len := (mem_dycks.mp hw).1.1
  have atVertex (i : ℕ) (hi : i∈Finset.range (2*d+1)) :
      f (height (w,i)).toNat=(height (w,i):ℝ)+1 := by
    have hb := (height_bounds (Finset.mem_product.mpr ⟨hw,hi⟩ : (w,i)∈marks d)).1
    dsimp only [f]
    congr 1
    exact_mod_cast Int.toNat_of_nonneg hb
  rw [Finset.sum_congr rfl atVertex,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_range,nsmul_eq_mul,mul_one]
  have area : (∑ i ∈ Finset.range (2*d+1), (height (w,i):ℝ))=walkArea w := by
    exact_mod_cast len ▸ path_area w
  push_cast
  rw [area]

end CentralUnimodality.MarkedExcursion
