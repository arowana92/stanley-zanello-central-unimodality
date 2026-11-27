module

public import CentralUnimodality.InnerGridTail

/-! Multiply the spacing by the number of grid points in a real interval.
The extra endpoint costs at most one spacing, including for a single point. -/
@[expose] public section

namespace CentralUnimodality

theorem grid_spacing_card (I : Finset ℕ) {Δ lo hi : ℝ} (hΔ : 0 ≤ Δ) (hwidth : lo ≤ hi)
    (h : ∀ j ∈ I, lo ≤ Δ*j ∧ Δ*j ≤ hi) : Δ*(I.card:ℝ) ≤ hi-lo+Δ := by
  rcases I.eq_empty_or_nonempty with rfl|hn
  · simpa using (by linarith only [hΔ,hwidth] : 0 ≤ hi-lo+Δ)
  let a := I.min' hn
  let b := I.max' hn
  have ha : a ∈ I := I.min'_mem hn
  have hb : b ∈ I := I.max'_mem hn
  have hab : a ≤ b := I.le_max' _ ha
  have hs : I ⊆ Finset.Icc a b := fun j hj => Finset.mem_Icc.mpr ⟨I.min'_le _ hj,I.le_max' _ hj⟩
  have hcard := Finset.card_le_card hs
  rw [Nat.card_Icc] at hcard
  have hlen : (I.card:ℝ) ≤ (b:ℝ)+1-a := by
    have h' : (I.card:ℝ)+(a:ℝ) ≤ (b:ℝ)+1 := by exact_mod_cast (by omega : I.card+a ≤ b+1)
    linarith only [h']
  have hm := mul_le_mul_of_nonneg_left hlen hΔ
  linarith only [hm,(h a ha).1,(h b hb).2]

theorem grid_arc_sum (I : Finset ℕ) {Δ S lo hi U : ℝ} (hΔ : 0 ≤ Δ) (hS : 0 ≤ S)
    (hlo : 0 ≤ lo) (hwidth : lo ≤ hi) (r : ℕ)
    (h : ∀ j ∈ I, lo*S ≤ Δ*j ∧ Δ*j ≤ hi*S)
    (f : ℕ → ℝ) (hU : 0 ≤ U) (hf : ∀ j ∈ I, f j ≤ U) :
    (∑ j ∈ I, Δ*((Δ*j)^r*f j)) ≤ ((hi-lo)*S+Δ)*(hi*S)^r*U := by
  have hpt : (∑ j ∈ I, Δ*((Δ*j)^r*f j)) ≤ ∑ _j ∈ I, Δ*((hi*S)^r*U) := by
    apply Finset.sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_left _ hΔ
    calc
      _ ≤ (Δ*j)^r*U := mul_le_mul_of_nonneg_left (hf j hj) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (h j hj).2 r) hU
  apply hpt.trans
  simp only [Finset.sum_const,nsmul_eq_mul]
  have hcard := grid_spacing_card I hΔ (mul_le_mul_of_nonneg_right hwidth hS) h
  have hHi := hlo.trans hwidth
  have hh := mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤ (hi*S)^r*U)
  linarith only [hh]

end CentralUnimodality
