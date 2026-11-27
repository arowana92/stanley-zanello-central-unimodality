module

public import CentralUnimodality.OuterGridTail

/-! Apply the three frequency estimates to the actual signed transform on
a scaled frequency grid. -/
@[expose] public section

namespace CentralUnimodality

noncomputable def signedMagnitude (n δ : ℕ) (θ : ℝ) :=
  ‖PowerSeries.coeff (2*n+δ+1) (fairSeries (areaCharacter (θ/2)) strictWords)‖/survival ((2*n+δ+1)/2)

theorem scaled_inner_magnitude {n δ : ℕ} (hδ : δ ≤ 1) (hn : 2049 ≤ n+δ) {x : ℝ} (hx : 0 < x)
    (ht : x ≤ 0.008*Witness.cellScale (n+δ)) :
    signedMagnitude n δ (x/Witness.cellScale (n+δ)) ≤ 100*Real.exp (-(0.157*x^(2/3:ℝ))) := by
  let S := Witness.cellScale (n+δ)
  have hS : 0 < S := Witness.cellScale_pos (by omega)
  have hN : (0:ℝ) ≤ 2*((n:ℝ)+δ) := by positivity
  have hsq : S^2 = (2*((n:ℝ)+δ))^3 := by
    dsimp [S,Witness.cellScale]
    push_cast
    rw [mul_pow,Real.sq_sqrt hN]
    ring
  have hpow : S^(2/3:ℝ) = 2*((n:ℝ)+δ) := by
    rw [show (2/3:ℝ) = (2:ℝ)*(1/3) by ring,Real.rpow_mul hS.le,Real.rpow_two,hsq,
      ← Real.rpow_natCast (2*((n:ℝ)+δ)) 3,← Real.rpow_mul hN]
    norm_num
  have he : (S*(x/S))^(2/3:ℝ) = S^(2/3:ℝ)*(x/S)^(2/3:ℝ) := Real.mul_rpow hS.le (div_nonneg hx.le hS.le)
  rw [hpow,show S*(x/S) = x by field_simp] at he
  have h := signed_inner_frequency hδ hn (div_pos hx hS) ((div_le_iff₀ hS).mpr ht)
  change signedMagnitude n δ (x/S) ≤ _
  apply h.trans_eq
  congr 2
  rw [mul_assoc,← he]

noncomputable def gridWeight (n δ r : ℕ) (Δ : ℝ) (j : ℕ) :=
  Δ*((Δ*j)^r*signedMagnitude n δ (Δ*j/Witness.cellScale (n+δ)))

def omittedSites (J k : ℕ) := (Finset.range k).image fun i => J+i+1

theorem inner_sites {n δ r J k : ℕ} {Δ : ℝ} (hδ : δ ≤ 1) (hn : 2049 ≤ n+δ) (hΔ : 0 < Δ)
    (I : Finset ℕ) (hI : I ⊆ omittedSites J k)
    (hθ : ∀ j ∈ I, Δ*j ≤ 0.008*Witness.cellScale (n+δ)) :
    (2/Real.pi)*(∑ j ∈ I, gridWeight n δ r Δ j) ≤ spectralGridSum r J k Δ := by
  let f (j : ℕ) := Δ*(100*(Δ*j)^r*Real.exp (-(0.157*(Δ*j)^(2/3:ℝ))))
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2/Real.pi)
  change (∑ j ∈ I, gridWeight n δ r Δ j) ≤ ∑ i ∈ Finset.range k, f (J+i+1)
  rw [← Finset.sum_image (f := f) (g := fun i : ℕ => J+i+1) (by intro i _ l _ he; dsimp at he; omega)]
  apply le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg hI (fun j _ _ => by dsimp [f]; positivity))
  apply Finset.sum_le_sum
  intro j hj
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp (hI hj)
  have h := scaled_inner_magnitude hδ hn (by positivity) (hθ _ hj)
  unfold gridWeight
  dsimp [f]
  apply mul_le_mul_of_nonneg_left _ hΔ.le
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (Δ*((J+i+1:ℕ):ℝ))^r)
    _ = _ := by ring

theorem mid_sites {n δ r : ℕ} {Δ : ℝ} (hδ : δ ≤ 1) (hn : 2049 ≤ n+δ) (hr : r ≤ 2)
    (hΔ : 0 ≤ Δ) (hstep : Δ ≤ 1.257) (I : Finset ℕ)
    (hθ : ∀ j ∈ I, 0.008*Witness.cellScale (n+δ) ≤ Δ*j ∧ Δ*j ≤ 0.032*Witness.cellScale (n+δ)) :
    (2/Real.pi)*(∑ j ∈ I, gridWeight n δ r Δ j) ≤ (outerCap 0.008 0.032 0.0078 216 r:ℝ) := by
  have hS := Witness.cellScale_pos (by omega : 0 < n+δ)
  apply outer_grid_cap (m := 2*n+δ) hn (by omega) hr (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hΔ hstep I (by simpa using hθ)
  intro j hj
  have ⟨hl,hu⟩ := hθ j hj
  have ht := (le_div_iff₀ hS).mpr hl
  have hp : Δ*j/Witness.cellScale (n+δ) ≤ Real.pi :=
    ((div_le_iff₀ hS).mpr hu).trans (by linarith only [Real.pi_gt_three])
  simpa [signedMagnitude] using signed_outer_frequency hδ (by omega) (by decide) (by norm_num) (outer_blocks_008 ht hp)

theorem high_sites {n δ r : ℕ} {Δ : ℝ} (hδ : δ ≤ 1) (hn : 2049 ≤ n+δ) (hr : r ≤ 2)
    (hΔ : 0 ≤ Δ) (hstep : Δ ≤ 1.257) (I : Finset ℕ)
    (hθ : ∀ j ∈ I, 0.032*Witness.cellScale (n+δ) ≤ Δ*j ∧ Δ*j ≤ Real.pi*Witness.cellScale (n+δ)) :
    (2/Real.pi)*(∑ j ∈ I, gridWeight n δ r Δ j) ≤ (outerCap 0.032 3.142 0.0155 112 r:ℝ) := by
  have hS := Witness.cellScale_pos (by omega : 0 < n+δ)
  apply outer_grid_cap (m := 2*n+δ) hn (by omega) hr (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hΔ hstep I
  · intro j hj
    obtain ⟨hl,hu⟩ := hθ j hj
    constructor
    · simpa using hl
    · apply hu.trans
      apply mul_le_mul_of_nonneg_right _ hS.le
      norm_num
      linarith only [Real.pi_lt_d4]
  · intro j hj
    have ⟨hl,hu⟩ := hθ j hj
    simpa [signedMagnitude] using signed_outer_frequency hδ (by omega) (by decide) (by norm_num)
      (outer_blocks_032 ((le_div_iff₀ hS).mpr hl) ((div_le_iff₀ hS).mpr hu))

end CentralUnimodality
