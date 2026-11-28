module

public import CentralUnimodality.PointMoments
public import CentralUnimodality.RetainedPairs

/-! Express the actual signed Fourier amplitude and its even moments
using the same normalized positive-branch partition distribution. -/
@[expose] public section

namespace CentralUnimodality.Witness
open Laurent Real PowerSeries

noncomputable def rankMean (n δ : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range (n*(n+δ)+1), (rankCount (2*n+δ) i:ℝ)*f i)/(massFactor n δ:ℝ)

noncomputable def scaledSite (n δ i : ℕ) : ℝ := (halfAreaSite n δ i:ℝ)/cellScale (n+δ)

theorem rankMean_power (n δ r : ℕ) :
    rankMean n δ (fun i => (scaledSite n δ i)^r)=pointMoment n δ r := by
  simp only [rankMean,scaledSite,pointMoment,rawPoint,Rat.cast_sum,Rat.cast_mul,Rat.cast_natCast,
    Rat.cast_pow,div_pow,← mul_div_assoc,← Finset.sum_div]
  ring

private theorem survival_times_paths (n δ : ℕ) (hδ : δ≤1) :
    (2:ℝ)^(2*n+δ+1)*survival ((2*n+δ+1)/2)=2*(massFactor n δ:ℝ) := by
  rcases (by omega : δ=0 ∨ δ=1) with rfl|rfl
  · rw [show (2*n+0+1)/2=n by omega]
    simp [survival,massFactor,pow_succ,pow_mul]
    field_simp
    ring
  · rw [show 2*n+1+1=2*(n+1) by omega,show 2*(n+1)/2=n+1 by omega]
    simp [survival,massFactor,pow_mul]
    field_simp
    norm_num
    ring

theorem signedAmplitude_mean (n δ : ℕ) (hδ : δ≤1) (ξ : ℝ) :
    signedAmplitude n δ (ξ/cellScale (n+δ)) =
      rankMean n δ (fun i => cos (ξ*scaledSite n δ i)) := by
  let L := 2*n+δ+1
  let θ := ξ/cellScale (n+δ)
  let S := ∑ i ∈ Finset.range (n*(n+δ)+1),
    (rankCount (2*n+δ) i:ℝ)*cos (ξ*scaledSite n δ i)
  have sites (i : ℕ) (hi : i∈Finset.range (n*(n+δ)+1)) :
      (θ/2)*(signedAreaAtRank n δ i:ℝ)=ξ*scaledSite n δ i := by
    have le : i≤n*(n+δ) := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    simp only [signedAreaAtRank,scaledSite,halfAreaSite,θ,Rat.cast_add,Rat.cast_sub,
      Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,Rat.cast_one,Rat.cast_ofNat,Nat.cast_sub le]
    push_cast
    ring
  have C := fourier_signed_ranks (θ/2) n δ hδ
  have row : coeff L (fairSeries (areaCharacter (θ/2)) strictWords)=
      (((2:ℝ)⁻¹^L*(2*S):ℝ):ℂ) := by
    rw [show L=2*n+δ+1 by rfl,C]
    simp only [S,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_pow,Complex.ofReal_ofNat,
      Complex.ofReal_sum,Complex.ofReal_natCast,Finset.mul_sum,nsmul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [sites i hi]; ring
  have realRow := congrArg Complex.re row
  rw [Complex.ofReal_re] at realRow
  have normal := survival_times_paths n δ hδ
  change (2:ℝ)^L*survival (L/2)=2*(massFactor n δ:ℝ) at normal
  change (coeff L (fairSeries (areaCharacter (θ/2)) strictWords)).re/survival (L/2)=
    S/(massFactor n δ:ℝ)
  rw [realRow,inv_pow]
  field_simp [(survival_pos _).ne',show (massFactor n δ:ℝ)≠0 by exact_mod_cast (massFactor_pos n δ).ne']
  linear_combination -S*normal

end CentralUnimodality.Witness
