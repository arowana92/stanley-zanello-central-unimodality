module

public import CentralUnimodality.Unimodality
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max

/-! The discrete superlevel argument behind the moment comparisons. For a
cell-centered continuous density, G at an index is its witness antiderivative
evaluated at the cell's left boundary. -/
@[expose] public section

namespace CentralUnimodality

private theorem le_from_adjacent {f : ℕ → ℕ} {a b : ℕ} (hab : a ≤ b)
    (h : ∀ j, a ≤ j → j < b → f j ≤ f (j+1)) : f a ≤ f b := by
  induction b, hab using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ k hak ih =>
    exact (ih (fun j haj hj => h j haj (by omega))).trans (h k hak (by omega))

private theorem ge_from_adjacent {f : ℕ → ℕ} {a b : ℕ} (hab : a ≤ b)
    (h : ∀ j, a ≤ j → j < b → f (j+1) ≤ f j) : f b ≤ f a := by
  induction b, hab using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ k hak ih =>
    exact (h k hak (by omega)).trans (ih (fun j haj hj => h j haj (by omega)))

theorem UnimodalOn.between {f : ℕ → ℕ} {d : ℕ} (hu : UnimodalOn f 0 d)
    {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    min (f a) (f c) ≤ f b := by
  obtain ⟨p, _, _, up, down⟩ := hu
  by_cases hbp : b ≤ p
  · exact (min_le_left _ _).trans (le_from_adjacent hab (fun j _ hj => up j (by omega) (by omega)))
  · exact (min_le_right _ _).trans (ge_from_adjacent hbc (fun j hj hjc => down j (by omega) (by omega)))

private def superlevel (f : ℕ → ℕ) (d t : ℕ) : Finset ℕ :=
  (Finset.range (d+1)).filter fun k => t < f k

private theorem mem_superlevel {f : ℕ → ℕ} {d t k : ℕ} :
    k ∈ superlevel f d t ↔ k ≤ d ∧ t < f k := by
  simp [superlevel]

/-- Every nonempty superlevel is the entire interval between its extremes. -/
private theorem superlevel_interval {f : ℕ → ℕ} {d t : ℕ} (hu : UnimodalOn f 0 d)
    (hne : (superlevel f d t).Nonempty) :
    superlevel f d t = Finset.Ico ((superlevel f d t).min' hne)
      ((superlevel f d t).max' hne + 1) := by
  let s := superlevel f d t
  have hl := mem_superlevel.mp (s.min'_mem hne)
  have hr := mem_superlevel.mp (s.max'_mem hne)
  ext k
  rw [Finset.mem_Ico]
  constructor
  · intro hk
    exact ⟨s.min'_le k hk, Nat.lt_succ_of_le (s.le_max' k hk)⟩
  · rintro ⟨hlk, hkr⟩
    have hkr' : k ≤ s.max' hne := Nat.le_of_lt_succ hkr
    exact mem_superlevel.mpr ⟨hkr'.trans hr.1,
      lt_of_lt_of_le (lt_min hl.2 hr.2) (hu.between hlk hkr' hr.1)⟩

variable {A : Type*} [AddCommGroup A] [LinearOrder A] [IsOrderedAddMonoid A]

private theorem layer_nonneg {f : ℕ → ℕ} {d i j : ℕ} (hu : UnimodalOn f 0 d)
    (hij : i < j) (hjd : j ≤ d) (hdrop : f j < f i) (G : ℕ → A)
    (short : ∀ a b, a ≤ b → b ≤ j → G a ≤ G b)
    (long : ∀ a b, a ≤ i → j < b → b ≤ d+1 → G a ≤ G b) (t : ℕ) :
    0 ≤ ∑ k ∈ superlevel f d t, (G (k+1)-G k) := by
  let s := superlevel f d t
  by_cases hne : s.Nonempty
  · let l := s.min' hne
    let r := s.max' hne
    have hlr : l ≤ r := s.min'_le _ (s.max'_mem hne)
    have hr : r ≤ d ∧ t < f r := mem_superlevel.mp (s.max'_mem hne)
    rw [superlevel_interval hu hne, Finset.sum_Ico_sub _ (Nat.le_succ_of_le hlr)]
    apply sub_nonneg.mpr
    by_cases hrj : r < j
    · exact short l (r+1) (by omega) (by omega)
    · have hjr : j ≤ r := by omega
      have hb := hu.between (Nat.le_of_lt hij) hjr hr.1
      have hc : f r ≤ f j := by omega
      have hmem : i ∈ s := mem_superlevel.mpr ⟨by omega, by omega⟩
      exact long l (r+1) (s.min'_le i hmem) (by omega) (by omega)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hne
    change 0 ≤ ∑ k ∈ s, (G (k+1)-G k)
    simp [he]

/-- A negative polynomial-witness sum forces a reflected comparison in a
unimodal row. M may be any common upper bound for all coefficients. -/
theorem reflected_of_negative_sum {f : ℕ → ℕ} {d i j M : ℕ} (hu : UnimodalOn f 0 d)
    (hij : i < j) (hjd : j ≤ d) (hM : ∀ k ≤ d, f k ≤ M) (G : ℕ → A)
    (short : ∀ a b, a ≤ b → b ≤ j → G a ≤ G b)
    (long : ∀ a b, a ≤ i → j < b → b ≤ d+1 → G a ≤ G b)
    (negative : (∑ k ∈ Finset.range (d+1), f k • (G (k+1)-G k)) < 0) : f i ≤ f j := by
  by_contra! hdrop
  have layers : 0 ≤ ∑ t ∈ Finset.range M, ∑ k ∈ superlevel f d t, (G (k+1)-G k) :=
    Finset.sum_nonneg fun t _ => layer_nonneg hu hij hjd hdrop G short long t
  simp only [superlevel, Finset.sum_filter] at layers
  rw [Finset.sum_comm] at layers
  have per (k : ℕ) (hk : k ∈ Finset.range (d+1)) :
      (∑ t ∈ Finset.range M, if t < f k then G (k+1)-G k else 0) =
        f k • (G (k+1)-G k) := by
    have hb := hM k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    have he : (Finset.range M).filter (fun t => t < f k) = Finset.range (f k) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [← Finset.sum_filter, he, Finset.sum_const, Finset.card_range]
  rw [Finset.sum_congr rfl per] at layers
  exact (not_lt_of_ge layers) negative

end CentralUnimodality
