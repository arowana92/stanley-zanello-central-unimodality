module

public import CentralUnimodality.FourierDifference
public import CentralUnimodality.FoldedGrid

/-! Truncating the actual conditional inverse Fourier sum changes its
scaled first and second adjacent differences by the certified reserves. -/
@[expose] public section

namespace CentralUnimodality

noncomputable def gridFrequency (Q t : ℕ) : ℝ := (2*Real.pi/Q)*t

/-- Inversion on a chosen subset of a full period, including the factor
two which recovers the conditional positive rank law from the signed law. -/
noncomputable def gridReconstruction (n δ Q : ℕ) (I : Finset ℕ) (j : ℕ) : ℂ :=
  (2/(Q:ℂ))*∑ t ∈ I, siteFourierTerm n δ (gridFrequency Q t) j

theorem difference_reconstruction (n δ Q j r : ℕ) (I : Finset ℕ) :
    (fwdDiff 1)^[r] (gridReconstruction n δ Q I) j =
      (2/(Q:ℂ))*∑ t ∈ I, (fwdDiff 1)^[r] (siteFourierTerm n δ (gridFrequency Q t)) j := by
  induction r generalizing j with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply',fwdDiff,ih,ih,← mul_sub,← Finset.sum_sub_distrib]
    simp only [Function.iterate_succ_apply',fwdDiff]

private theorem scaled_omission {n δ Q : ℕ} (hδ : δ ≤ 1) (hS : 0 < Witness.cellScale (n+δ))
    (hq : 0 < (Q:ℝ)) (j r J : ℕ) :
    Witness.cellScale (n+δ)^(r+1) *
      ‖(fwdDiff 1)^[r] (gridReconstruction n δ Q (Finset.range Q)) j -
        (fwdDiff 1)^[r] (gridReconstruction n δ Q (retainedModes Q J)) j‖ ≤
      omittedWeight n δ r J (Q/2-J) (2*Real.pi*Witness.cellScale (n+δ)/Q) := by
  let S := Witness.cellScale (n+δ)
  let Δ := 2*Real.pi*S/Q
  let d (t : ℕ) := (fwdDiff 1)^[r] (siteFourierTerm n δ (gridFrequency Q t)) j
  have hπ := Real.pi_pos
  have hb (t : ℕ) : S*gridFrequency Q t = Δ*t := by dsimp [Δ,gridFrequency]; ring
  have href (t : ℕ) (ht : t < Q) : ‖d (Q-t)‖ = ‖d t‖ := by
    have hg : gridFrequency Q (Q-t) = 2*Real.pi-gridFrequency Q t := by
      unfold gridFrequency
      rw [Nat.cast_sub ht.le]
      field_simp
    dsimp only [d]
    rw [hg,norm_difference_reflect _ _ _ _ hδ]
  have hfold := folded_grid_sum Q J (fun t => ‖d t‖) (fun t => norm_nonneg _) href
  rw [difference_reconstruction,difference_reconstruction,← mul_sub,mode_split,norm_mul,norm_div]
  simp only [Complex.norm_natCast,show ‖(2:ℂ)‖ = (2:ℝ) by norm_num]
  change S^(r+1)*((2/(Q:ℝ))*‖∑ t ∈ omittedModes Q J, d t‖) ≤ _
  have hsum := (norm_sum_le (omittedModes Q J) d).trans hfold
  calc
    _ ≤ S^(r+1)*((2/(Q:ℝ))*(2*∑ t ∈ omittedSites J (Q/2-J), ‖d t‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (by positivity)) (by positivity)
    _ = ∑ t ∈ omittedSites J (Q/2-J), (4*S^(r+1)/Q)*‖d t‖ := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ ∑ t ∈ omittedSites J (Q/2-J), (2/Real.pi)*gridWeight n δ r Δ t := by
      apply Finset.sum_le_sum
      intro t _
      have ht : 0 ≤ gridFrequency Q t := by unfold gridFrequency; positivity
      have h := norm_site_difference n δ j r ht
      apply (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 4*S^(r+1)/Q)).trans_eq
      have he : Δ*t/S = gridFrequency Q t := (div_eq_iff hS.ne').mpr (by rw [← hb]; ring)
      change 4*S^(r+1)/Q*(_^r*_) = 2/Real.pi*(Δ*((Δ*t)^r*signedMagnitude n δ (Δ*t/S)))
      rw [he,← hb,mul_pow,pow_succ]
      dsimp only [Δ]
      field_simp
      ring
    _ = _ := (Finset.mul_sum ..).symm

/-- Uniform in the target rank and in the upper half-length. The forward
second difference at rank j is the centered difference at rank j+1. -/
theorem truncation_two_orders {n δ Q J : ℕ} (hδ : δ ≤ 1) (hn : 2049 ≤ n+δ)
    (hQ : 5*Witness.cellScale (n+δ) ≤ Q)
    (hJ : 2048 ≤ (2*Real.pi*Witness.cellScale (n+δ)/Q)*J) (j : ℕ) :
    let F := gridReconstruction n δ Q (Finset.range Q)
    let T := gridReconstruction n δ Q (retainedModes Q J)
    let S := Witness.cellScale (n+δ)
    S^2*‖fwdDiff 1 F j-fwdDiff 1 T j‖ ≤ 0.00025 ∧
    S^3*‖(fwdDiff 1)^[2] F j-(fwdDiff 1)^[2] T j‖ ≤ 0.949 := by
  have hS := Witness.cellScale_pos (by omega : 0 < n+δ)
  have hq : 0 < (Q:ℝ) := lt_of_lt_of_le (by positivity : 0 < 5*Witness.cellScale (n+δ)) hQ
  have h := omitted_fourier_grid hδ hn hQ hJ
  exact ⟨(scaled_omission hδ hS hq j 1 J).trans h.1,(scaled_omission hδ hS hq j 2 J).trans h.2⟩

end CentralUnimodality
