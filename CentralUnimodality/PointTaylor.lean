module

public import CentralUnimodality.PointAmplitude
public import CentralUnimodality.CosineTaylor

/-! Every even point-moment table supplies a uniform enclosure for the
actual Fourier amplitude at every real frequency in both families. -/
@[expose] public section

namespace CentralUnimodality.Witness
open Real Laurent

private theorem rankMean_mul (n δ : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    rankMean n δ (fun i => c*f i)=c*rankMean n δ f := by
  unfold rankMean
  rw [← mul_div_assoc,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _; ring

private theorem rankMean_sum (n δ t : ℕ) (f : ℕ → ℕ → ℝ) :
    rankMean n δ (fun i => ∑ j ∈ Finset.range t, f j i)=
      ∑ j ∈ Finset.range t, rankMean n δ (f j) := by
  simp only [rankMean,Finset.mul_sum,← Finset.sum_div]
  rw [Finset.sum_comm]

private theorem rankMean_sub (n δ : ℕ) (f g : ℕ → ℝ) :
    rankMean n δ (fun i => f i-g i)=rankMean n δ f-rankMean n δ g := by
  simp only [rankMean,mul_sub,Finset.sum_sub_distrib,sub_div]

private theorem rankMean_bound (n δ : ℕ) (f g : ℕ → ℝ)
    (h : ∀ i∈Finset.range (n*(n+δ)+1), |f i|≤g i) :
    |rankMean n δ f|≤rankMean n δ g := by
  have hm : (0:ℝ)<(massFactor n δ:ℝ) := by exact_mod_cast massFactor_pos n δ
  unfold rankMean
  rw [abs_div,abs_of_pos hm]
  apply div_le_div_of_nonneg_right _ hm.le
  apply (Finset.abs_sum_le_sum_abs ..).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul,Nat.abs_cast]
  exact mul_le_mul_of_nonneg_left (h i hi) (Nat.cast_nonneg _)

noncomputable def momentTaylor (n δ h : ℕ) (ξ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (h+1), (cosineCoefficient j:ℝ)*ξ^(2*j)*pointMoment n δ (2*j)

private theorem rankMean_taylor (n δ h : ℕ) (ξ : ℝ) :
    rankMean n δ (fun i => cosineTaylor h (ξ*scaledSite n δ i))=momentTaylor n δ h ξ := by
  simp only [cosineTaylor,mul_pow,← mul_assoc,rankMean_sum,rankMean_mul,rankMean_power,momentTaylor]

theorem point_amplitude_remainder (n δ h : ℕ) (hδ : δ≤1) (ξ : ℝ) :
    |signedAmplitude n δ (ξ/cellScale (n+δ))-momentTaylor n δ h ξ| ≤
      (|ξ|^(2*(h+1))/(2*(h+1)).factorial)*pointMoment n δ (2*(h+1)) := by
  rw [signedAmplitude_mean _ _ hδ,← rankMean_taylor,← rankMean_sub,← rankMean_power,← rankMean_mul]
  apply rankMean_bound
  intro i _
  apply (cosine_remainder h (ξ*scaledSite n δ i)).trans_eq
  rw [abs_mul,mul_pow,← abs_pow (scaledSite n δ i),abs_of_nonneg ((even_two_mul (h+1)).pow_nonneg (scaledSite n δ i))]
  ring

end CentralUnimodality.Witness
