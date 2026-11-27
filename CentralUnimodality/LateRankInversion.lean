module

public import CentralUnimodality.LateFrequencyEnvelope

/-! Lattice inversion of the rank mass jointly with a genuine late
crossing, at any integer site and at each of the three difference orders. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real MeasureTheory Set

theorem late_difference_integral (v : ℝ) (m T : ℕ) {R : ℝ} (hR : 0 ≤ R) (r : Fin 3) (k : ℤ)
    {g : ℝ → ℝ} (hg : Integrable g) (hpos : ∀ θ, 0 ≤ g θ)
    (hdom : ∀ θ ∈ Ioc (-π) π, R*‖lateRankCharacter v θ m T‖*|θ|^r.val ≤ g θ) :
    (2*π)*R*|rankDifference r k (eventSiteMass v m (lateHitEvent m T))| ≤ ∫ θ, g θ := by
  let B := (Ioc (-π) π).indicator (fun θ : ℝ => (R:ℂ)*lateRankCharacter v θ m T)
  let A := eventSiteMass v m (lateHitEvent m T)
  have hc : Continuous (fun θ : ℝ => lateRankCharacter v θ m T) := by
    unfold lateRankCharacter phase; fun_prop
  have he (j : ℤ) : (fun θ : ℝ => B θ*phase (-θ*((j:ℝ)-0))) =
      (Ioc (-π) π).indicator (fun θ : ℝ => (R:ℂ)*(lateRankCharacter v θ m T*phase (-θ*(j:ℝ)))) := by
    funext θ; by_cases h : θ ∈ Ioc (-π) π <;> simp [B,h,mul_assoc]
  have hi (j : ℤ) : Integrable (fun θ : ℝ => B θ*phase (-θ*((j:ℝ)-0))) := by
    rw [he,integrable_indicator_iff measurableSet_Ioc]
    apply Continuous.integrableOn_Icc _ |>.mono_set Ioc_subset_Icc_self
    unfold phase; fun_prop
  have inv (j : ℤ) : (∫ θ : ℝ, B θ*phase (-θ*((j:ℝ)-0))) = (((2*π)*R*A j:ℝ):ℂ) := by
    rw [he,integral_indicator measurableSet_Ioc,← intervalIntegral.integral_of_le (by linarith only [pi_pos] : -π ≤ π),
      intervalIntegral.integral_const_mul]
    have H := word_rank_inversion (lateHitEvent m T) (signMass v (v*m)) 0 j
    simp only [sub_zero] at H
    change (R:ℂ)*(∫ θ in -π..π, lateRankCharacter v θ m T*phase (-θ*(j:ℝ))) = _
    rw [show (∫ θ in -π..π, lateRankCharacter v θ m T*phase (-θ*(j:ℝ))) =
      ((2*π:ℝ):ℂ)*(A j:ℂ) from H]
    push_cast; ring
  have H := lattice_difference_integral B 0 (fun j => (2*π)*R*A j) hi inv r k hg (fun θ => by
    by_cases h : θ ∈ Ioc (-π) π
    · simpa [B,h,abs_of_nonneg hR] using hdom θ h
    · simpa [B,h] using hpos θ)
  have hA : (fun j => (2*π)*R*A j) = ((2*π)*R) • A := rfl
  simpa only [hA,map_smul,smul_eq_mul,abs_mul,abs_of_nonneg hR,abs_of_pos (by positivity : 0<2*π)] using H

end CentralUnimodality.MarkedExcursion
