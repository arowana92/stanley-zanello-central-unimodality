module

public import CentralUnimodality.GridArcEstimates

/-! Weighted absolute sums of the omitted frequencies of the conditional
signed transform, for the two finite differences used in the central window. -/
@[expose] public section

namespace CentralUnimodality

noncomputable def omittedWeight (n δ r J k : ℕ) (Δ : ℝ) :=
  (2/Real.pi)*∑ j ∈ omittedSites J k, gridWeight n δ r Δ j

private theorem three_arcs {n δ r J k : ℕ} {Δ : ℝ} (hδ : δ ≤ 1) (hn : 2049 ≤ n+δ) (hr : r ≤ 2)
    (hΔ : 0 < Δ) (hstep : Δ ≤ 1.257)
    (hπ : ∀ j ∈ omittedSites J k, Δ*j ≤ Real.pi*Witness.cellScale (n+δ)) :
    omittedWeight n δ r J k Δ ≤ spectralGridSum r J k Δ +
      (outerCap 0.008 0.032 0.0078 216 r:ℝ) + (outerCap 0.032 3.142 0.0155 112 r:ℝ) := by
  let S := Witness.cellScale (n+δ)
  let I := omittedSites J k
  let a (j : ℕ) := Δ*j ≤ 0.008*S
  let b (j : ℕ) := Δ*j ≤ 0.032*S
  let f := gridWeight n δ r Δ
  have h₁ := inner_sites (r := r) hδ hn hΔ (I.filter a) (Finset.filter_subset _ _)
    (fun j hj => (Finset.mem_filter.mp hj).2)
  have h₂ := mid_sites (r := r) hδ hn hr hΔ.le hstep (I.filter fun j => ¬a j ∧ b j)
    (fun j hj => ⟨(lt_of_not_ge (Finset.mem_filter.mp hj).2.1).le,(Finset.mem_filter.mp hj).2.2⟩)
  have h₃ := high_sites (r := r) hδ hn hr hΔ.le hstep (I.filter fun j => ¬a j ∧ ¬b j)
    (fun j hj => ⟨(lt_of_not_ge (Finset.mem_filter.mp hj).2.2).le,hπ j (Finset.mem_filter.mp hj).1⟩)
  have hsum : ∑ j ∈ I, f j = (∑ j ∈ I.filter a, f j) +
      (∑ j ∈ I.filter (fun j => ¬a j ∧ b j), f j) +
      (∑ j ∈ I.filter (fun j => ¬a j ∧ ¬b j), f j) := by
    simp only [Finset.sum_filter,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases ha : a j <;> by_cases hb : b j <;> simp [ha,hb]
  change (2/Real.pi)*(∑ j ∈ I, f j) ≤ _
  rw [hsum,mul_add,mul_add]
  exact add_le_add (add_le_add h₁ h₂) h₃

theorem omitted_two_orders {n δ J k : ℕ} {Δ : ℝ} (hδ : δ ≤ 1) (hn : 2049 ≤ n+δ)
    (hΔ : 0 < Δ) (hstep : Δ ≤ 1.257) (hJ : 2048 ≤ Δ*J)
    (hπ : ∀ j ∈ omittedSites J k, Δ*j ≤ Real.pi*Witness.cellScale (n+δ)) :
    omittedWeight n δ 1 J k Δ ≤ 0.00025 ∧ omittedWeight n δ 2 J k Δ ≤ 0.949 := by
  obtain ⟨hm₁,hh₁,hm₂,hh₂⟩ := outer_cap_values
  constructor
  · apply (three_arcs hδ hn (by decide : 1 ≤ 2) hΔ hstep hπ).trans
    apply (add_le_add (add_le_add (inner_grid_first hΔ hJ k) ((Rat.cast_le (K := ℝ)).mpr hm₁))
      ((Rat.cast_le (K := ℝ)).mpr hh₁)).trans
    norm_num
  · apply (three_arcs hδ hn (by decide : 2 ≤ 2) hΔ hstep hπ).trans
    apply (add_le_add (add_le_add (inner_grid_second hΔ hJ k) ((Rat.cast_le (K := ℝ)).mpr hm₂))
      ((Rat.cast_le (K := ℝ)).mpr hh₂)).trans
    norm_num

/-- The paper's grid has period at least five times the area scale. The
last included positive frequency can be the Nyquist frequency. -/
theorem omitted_fourier_grid {n δ Q J : ℕ} (hδ : δ ≤ 1) (hn : 2049 ≤ n+δ)
    (hQ : 5*Witness.cellScale (n+δ) ≤ Q)
    (hJ : 2048 ≤ (2*Real.pi*Witness.cellScale (n+δ)/Q)*J) :
    let Δ := 2*Real.pi*Witness.cellScale (n+δ)/Q
    omittedWeight n δ 1 J (Q/2-J) Δ ≤ 0.00025 ∧
    omittedWeight n δ 2 J (Q/2-J) Δ ≤ 0.949 := by
  let S := Witness.cellScale (n+δ)
  have hS : 0 < S := Witness.cellScale_pos (by omega)
  have hq : 0 < (Q:ℝ) := lt_of_lt_of_le (by positivity : 0 < 5*S) hQ
  have hstep : 2*Real.pi*S/Q ≤ 1.257 := by
    apply (div_le_iff₀ hq).mpr
    calc
      2*Real.pi*S ≤ (1.257*5)*S := mul_le_mul_of_nonneg_right (by linarith only [Real.pi_lt_d4]) hS.le
      _ ≤ 1.257*Q := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hQ (by norm_num)
  apply omitted_two_orders hδ hn (by positivity) hstep hJ
  intro j hj
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
  have hk := Finset.mem_range.mp hi
  have ht : 2*(J+i+1) ≤ Q := by omega
  have hc : (2:ℝ)*((J+i+1:ℕ):ℝ) ≤ Q := by exact_mod_cast ht
  change 2*Real.pi*S/Q*((J+i+1:ℕ):ℝ) ≤ Real.pi*S
  rw [div_mul_eq_mul_div,div_le_iff₀ hq]
  calc
    _ = Real.pi*S*(2*((J+i+1:ℕ):ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (by positivity)

end CentralUnimodality
