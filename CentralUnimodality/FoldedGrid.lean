module

public import CentralUnimodality.OmittedFourier

/-! Pair the two halves of an integer Fourier grid. The upper estimate
allows two copies of a Nyquist term when the grid length is even. -/
@[expose] public section

namespace CentralUnimodality

def retainedModes (Q J : ℕ) := (Finset.range Q).filter fun t => min t (Q-t) ≤ J
def omittedModes (Q J : ℕ) := (Finset.range Q).filter fun t => J < min t (Q-t)

theorem mode_split (Q J : ℕ) (g : ℕ → ℂ) :
    (∑ t ∈ Finset.range Q, g t) - (∑ t ∈ retainedModes Q J, g t) =
      ∑ t ∈ omittedModes Q J, g t := by
  unfold retainedModes omittedModes
  simp only [Finset.sum_filter]
  rw [sub_eq_iff_eq_add,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : min t (Q-t) ≤ J <;> simp [ht,lt_of_not_ge,not_lt_of_ge]

private theorem mem_positive_modes {Q J t : ℕ} (hl : J < t) (hu : t ≤ Q/2) :
    t ∈ omittedSites J (Q/2-J) := by
  apply Finset.mem_image.mpr
  exact ⟨t-J-1,Finset.mem_range.mpr (by omega),by omega⟩

theorem folded_grid_sum (Q J : ℕ) (f : ℕ → ℝ) (hn : ∀ t, 0 ≤ f t)
    (href : ∀ t < Q, f (Q-t) = f t) :
    ∑ t ∈ omittedModes Q J, f t ≤ 2*∑ t ∈ omittedSites J (Q/2-J), f t := by
  let I := omittedModes Q J
  let P := omittedSites J (Q/2-J)
  let L := I.filter fun t => t ≤ Q/2
  let H := I.filter fun t => Q/2 < t
  have hl : L ⊆ P := by
    intro t ht
    obtain ⟨hI,hu⟩ := Finset.mem_filter.mp ht
    obtain ⟨_,hmin⟩ := Finset.mem_filter.mp hI
    exact mem_positive_modes ((lt_min_iff.mp hmin).1) hu
  have hh (t : ℕ) (ht : t ∈ H) : t < Q ∧ Q-t ∈ P := by
    obtain ⟨hI,hl⟩ := Finset.mem_filter.mp ht
    obtain ⟨hq,hmin⟩ := Finset.mem_filter.mp hI
    exact ⟨Finset.mem_range.mp hq,mem_positive_modes ((lt_min_iff.mp hmin).2) (by omega)⟩
  have himg : H.image (fun t => Q-t) ⊆ P := by
    intro t ht
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
    exact (hh _ hi).2
  have hL := Finset.sum_le_sum_of_subset_of_nonneg (f := f) hl (fun t _ _ => hn t)
  have hH : (∑ t ∈ H, f t) ≤ ∑ t ∈ P, f t := by
    calc
      _ = ∑ t ∈ H, f (Q-t) := Finset.sum_congr rfl (fun t ht => (href _ (hh _ ht).1).symm)
      _ = ∑ t ∈ H.image (fun t => Q-t), f t := by
        rw [Finset.sum_image]
        intro t ht u hu he
        have h₁ := (hh _ ht).1
        have h₂ := (hh _ hu).1
        dsimp at he
        omega
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg himg (fun t _ _ => hn t)
  have hsum : (∑ t ∈ I, f t) = (∑ t ∈ L, f t)+(∑ t ∈ H, f t) := by
    simp only [L,H,Finset.sum_filter,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    by_cases ht : t ≤ Q/2 <;> simp [ht,lt_of_not_ge,not_lt_of_ge]
  rw [← show I = omittedModes Q J from rfl,hsum,two_mul]
  exact add_le_add hL hH

end CentralUnimodality
