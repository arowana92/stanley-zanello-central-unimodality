module

public import CentralUnimodality.FourierInversion

/-! Full-grid recovery of individual rank counts, the forward-difference
multiplier and the effect of uniform frequency error on the inverse. -/
@[expose] public section

namespace CentralUnimodality

open PowerSeries

noncomputable def siteInverse (Q : ℕ) (a : ℤ) (F : ℕ → ℂ) : ℂ :=
  (∑ r ∈ Finset.range Q, areaCharacter (halfGrid Q r) (-a)*F r) / Q

private theorem small_dvd {z : ℤ} {Q : ℕ} (hlo : -(Q:ℤ) < z) (hhi : z < Q) :
    (Q:ℤ) ∣ z ↔ z = 0 := by
  refine ⟨fun h => ?_,fun h => h ▸ dvd_zero _⟩
  rcases le_total 0 z with hz|hz
  · exact Int.eq_zero_of_dvd_of_nonneg_of_lt hz hhi h
  · have he := Int.eq_zero_of_dvd_of_nonneg_of_lt (neg_nonneg.mpr hz) (by omega : -z < Q) (dvd_neg.mpr h)
    omega

theorem recover_rank (n δ : ℕ) (hδ : δ ≤ 1) {Q : ℕ} (hQ : signedAreaAtRank n δ 0 < Q)
    (j : ℕ) (hj : j ≤ n*(n+δ)) :
    siteInverse Q (signedAreaAtRank n δ j) (fun r =>
      coeff (2*n+δ+1) (fairSeries (areaCharacter (halfGrid Q r)) strictWords)) =
      (2:ℂ)⁻¹^(2*n+δ+1)*(rankCount (2*n+δ) j:ℂ) := by
  let D := n*(n+δ)
  let a := signedAreaAtRank n δ 0
  have ha : 2*(D:ℤ) < a := by
    dsimp [a,D,signedAreaAtRank]
    omega
  have hq : a < (Q:ℤ) := hQ
  have hd : 0 ≤ (D:ℤ) := by positivity
  have hj' : (j:ℤ) ≤ D := by exact_mod_cast hj
  rw [siteInverse,periodized_ranks n δ hδ (by omega)]
  congr 1
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr (by omega))]
  · have hneg : ¬(Q:ℤ) ∣ (j:ℤ)+j-a := by
      rw [small_dvd (by omega) (by omega)]
      omega
    simp [a] at hneg
    simp [hneg]
  · intro l hl hne
    have hl' : (l:ℤ) ≤ D := by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hl))
    have hpos : ¬(Q:ℤ) ∣ (j:ℤ)-l := by
      rw [small_dvd (by omega) (by omega)]
      omega
    have hneg : ¬(Q:ℤ) ∣ (j:ℤ)+l-a := by
      rw [small_dvd (by omega) (by omega)]
      omega
    simp [a] at hneg
    simp [hpos,hneg]

theorem siteInverse_step (Q : ℕ) (a : ℤ) (F : ℕ → ℂ) :
    siteInverse Q (a+2) F-siteInverse Q a F =
      siteInverse Q a (fun r => (areaCharacter (halfGrid Q r) (-2)-1)*F r) := by
  simp only [siteInverse,← sub_div,← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [neg_add,areaCharacter_add]
  ring

theorem siteInverse_error {Q : ℕ} (hQ : 0 < Q) (a : ℤ) (F G : ℕ → ℂ) {e : ℝ}
    (h : ∀ r < Q, ‖F r-G r‖ ≤ e) : ‖siteInverse Q a F-siteInverse Q a G‖ ≤ e := by
  simp only [siteInverse,← sub_div,← Finset.sum_sub_distrib,← mul_sub,norm_div,Complex.norm_natCast]
  apply (div_le_iff₀ (by exact_mod_cast hQ : (0:ℝ) < Q)).mpr
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _r ∈ Finset.range Q, e := by
      apply Finset.sum_le_sum
      intro r hr
      simpa only [norm_mul,norm_areaCharacter,one_mul] using h r (Finset.mem_range.mp hr)
    _ = _ := by simp [mul_comm]

/-- On a grid that resolves the entire row, the convolution residual controls
the error in recovering the normalized count of any particular rank. -/
theorem rank_error_of_residual (n δ : ℕ) (hδ : δ ≤ 1) {Q : ℕ} (hQ : 0 < Q)
    (hfull : signedAreaAtRank n δ 0 < Q) (j : ℕ) (hj : j ≤ n*(n+δ))
    (V : ℕ → PowerSeries ℂ) (e : ℝ)
    (h : ∀ r < Q, ∀ k ≤ 2*n+δ+1, ‖coeff k (fairSeries (areaCharacter (halfGrid Q r)) words -
      fairSeries (areaCharacter (halfGrid Q r)) bridges * V r)‖ ≤ e) :
    ‖(2:ℂ)⁻¹^(2*n+δ+1)*(rankCount (2*n+δ) j:ℂ) -
      siteInverse Q (signedAreaAtRank n δ j) (fun r => coeff (2*n+δ+1) (V r))‖ ≤ 2*e := by
  rw [← recover_rank n δ hδ hfull j hj]
  apply siteInverse_error hQ
  intro r hr
  simpa only [map_sub] using fairSeries_residual_bound _ (areaCharacter_zero _)
    (areaCharacter_add _) (fun x => (norm_areaCharacter _ x).le) _ _ e (h r hr)

end CentralUnimodality
