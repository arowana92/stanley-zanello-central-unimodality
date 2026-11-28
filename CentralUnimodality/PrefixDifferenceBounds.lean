module

public import CentralUnimodality.GaussianMixtureBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Equation (3) for the actual rank law, conditional on the three
uniform local approximation errors for the unrestricted suffix. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

/-- Uniform lattice errors at orders zero, one (forward), and two (centered). -/
def FreeSuffixApproximation (c : ℝ) (M : ℕ) (σ : ℝ)
    (ε₀ : ℝ := 5/1000) (ε₁ : ℝ := 7/1000) (ε₂ : ℝ := 10/1000) : Prop := ∀ k : ℤ,
  let A := freeRankMass c M
  let y := ((k:ℝ)-meanRank c M)/σ
  |σ*A k-normalHeight*bell y| ≤ ε₀ ∧
  |σ^2*(A (k+1)-A k)+normalHeight*y*bell y| ≤ ε₁ ∧
  |σ^3*(A (k-1)+A (k+1)-2*A k)-normalHeight*(y^2-1)*bell y| ≤ ε₂

private noncomputable def prefixAverage (c u : ℝ) (L : ℕ) : (↥(ballots L) → ℝ) →ₗ[ℝ] ℝ :=
  (live c u L 1)⁻¹ • ∑ w : ballots L, signMass c u w • LinearMap.proj w

private theorem average_apply (c u : ℝ) (L : ℕ) (g : ↥(ballots L) → ℝ) :
    prefixAverage c u L g = (∑ w : ballots L, signMass c u w*g w)/live c u L 1 := by
  simp [prefixAverage,LinearMap.sum_apply,div_eq_inv_mul]

private theorem average_mono (c u : ℝ) (L : ℕ) : Monotone (prefixAverage c u L) := by
  intro f g h
  rw [average_apply,average_apply]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i)
    (signMass_pos ..).le)) (live_nonneg ..)

private theorem average_one (c u : ℝ) (L : ℕ) (hp : 0 < live c u L 1) : prefixAverage c u L 1=1 := by
  rw [average_apply]
  simp only [Pi.one_apply,mul_one,Finset.sum_coe_sort,← live_ballots,div_self hp.ne']

/-- Write the variance allowance explicitly so that the three conclusions
refer to the same scale and the same prefix. -/
noncomputable def varianceLimit (m : ℕ) (c f σ : ℝ) :=
  let d := tanh (c*m)
  ((m:ℝ)^3/(4*σ^2))*(f+(1+d)/(1-f)*(f^2+1/(2*m*d^2)))

theorem conditional_prefix_allowances {ε₀ ε₁ ε₂ : ℝ} {m L : ℕ} (hm : 0 < m) {c f σ : ℝ} (hc : 0 < c)
    (hf : 0 ≤ f) (hf' : f < 1) (hL : (L:ℝ) ≤ f*m) (hσ : 0 < σ)
    (hs : FreeSuffixApproximation c (m-L) σ ε₀ ε₁ ε₂) {j : ℤ} (hj : meanRank c m=j) :
    let P := live c (c*m) L 1
    let A := fun k => prefixSiteMass c m L k/P
    let B := varianceLimit m c f σ
    3989/10000*exp (-B/2)-ε₀ ≤ σ*A j ∧ |σ^2*(A (j+1)-A j)| ≤ 97/400+ε₁ ∧
      σ^3*(A (j-1)+A (j+1)-2*A j) ≤ normalHeight*(B/(1+B/2)-exp (-B/2))+ε₂ := by
  dsimp only
  let M := m-L
  let u := c*m
  let P := live c u L 1
  let F := prefixAverage c u L
  let S := fun (k : ℤ) (w : ballots L) => freeRankMass c M (k-shiftedPrefixRank M w)
  let y := fun (w : ballots L) => (((j-shiftedPrefixRank M w:ℤ):ℝ)-meanRank c M)/σ
  let B := varianceLimit m c f σ
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  have ht : L ≤ m := by
    have : (L:ℝ) ≤ m := by nlinarith only [hL,mul_nonneg (sub_nonneg.mpr hf'.le) hm'.le]
    exact_mod_cast this
  have hu : 0 < u := mul_pos hc hm'
  have hv : 0 < (1-f)*u := mul_pos (by linarith) hu
  have hP : 0 < P := by
    have h := live_lower c u ((1-f)*u) L 1 (fun i hi => by
      have h' : (i:ℝ) ≤ L := by exact_mod_cast hi.le
      dsimp only [u]; nlinarith only [mul_le_mul_of_nonneg_left (h'.trans hL) hc.le])
    simp only [pow_one] at h
    exact (sub_pos.mpr (exp_lt_one_iff.mpr (by linarith only [hv]))).trans_le h
  have hmass (k : ℤ) : F (S k) = prefixSiteMass c m L k/P := by
    rw [average_apply,prefixSiteMass_mixture c ht k]
    dsimp only [S,P,u,M]
    rw [Finset.sum_coe_sort (ballots L) (fun w => signMass c (c*m) w*freeRankMass c (m-L) (k-shiftedPrefixRank (m-L) w))]
  have hY : F (fun w => (y w)^2) ≤ B := by
    rw [average_apply]
    have he (w : ballots L) : (y w)^2 = (centeredRank c u m w)^2/σ^2 := by
      dsimp only [y,M,u]
      rw [saddle_suffix_site c ht hj w.property,div_pow,neg_sq]
    simp_rw [he,mul_div_assoc']
    rw [← Finset.sum_div,Finset.sum_coe_sort (ballots L) (fun w => signMass c u w*(centeredRank c u m w)^2),
      div_div,mul_comm (σ^2)]
    exact conditional_prefix_variance hm hc hf hf' hL hσ
  have hB : 0 ≤ B := by
    dsimp only [B,varianceLimit]
    have hd : 0 ≤ tanh (c*m) := by
      rw [tanh_eq_sinh_div_cosh]; exact div_nonneg (sinh_nonneg_iff.mpr hu.le) (cosh_pos _).le
    positivity
  let g₀ := σ • S j
  let g₁ := σ^2 • (S (j+1)-S j)
  let g₂ := σ^3 • (S (j-1)+S (j+1)-(2:ℝ) • S j)
  have h₀ (i : ballots L) : |g₀ i-normalHeight*bell (y i)| ≤ ε₀ := (hs _).1
  have h₁ (i : ballots L) : |g₁ i+normalHeight*y i*bell (y i)| ≤ ε₁ := by
    have H := (hs (j-shiftedPrefixRank M i)).2.1
    simpa only [g₁,S,y,M,Pi.smul_apply,Pi.sub_apply,smul_eq_mul,
      show ∀ a : ℤ, j+1-a=j-a+1 by omega] using H
  have h₂ (i : ballots L) : |g₂ i-normalHeight*((y i)^2-1)*bell (y i)| ≤ ε₂ := by
    have H := (hs (j-shiftedPrefixRank M i)).2.2
    simpa only [g₂,S,y,M,Pi.smul_apply,Pi.sub_apply,Pi.add_apply,smul_eq_mul,
      show ∀ a : ℤ, j+1-a=j-a+1 by omega,show ∀ a : ℤ, j-1-a=j-a-1 by omega] using H
  have h := gaussian_difference_allowances F (average_mono ..) (average_one _ _ _ hP)
    y g₀ g₁ g₂ hB hY h₀ h₁ h₂
  simpa only [g₀,g₁,g₂,map_smul,map_add,map_sub,smul_eq_mul,hmass] using h

theorem conditional_prefix_differences {m L : ℕ} (hm : 0 < m) {c f σ : ℝ} (hc : 0 < c)
    (hf : 0 ≤ f) (hf' : f < 1) (hL : (L:ℝ) ≤ f*m) (hσ : 0 < σ)
    (hs : FreeSuffixApproximation c (m-L) σ) {j : ℤ} (hj : meanRank c m=j) :
    let P := live c (c*m) L 1
    let A := fun k => prefixSiteMass c m L k/P
    let B := varianceLimit m c f σ
    3989/10000*exp (-B/2)-5/1000 ≤ σ*A j ∧ |σ^2*(A (j+1)-A j)| < 1/4 ∧
      σ^3*(A (j-1)+A (j+1)-2*A j) ≤ normalHeight*(B/(1+B/2)-exp (-B/2))+10/1000 := by
  obtain ⟨H₀,H₁,H₂⟩ := conditional_prefix_allowances hm hc hf hf' hL hσ hs hj
  exact ⟨H₀,H₁.trans_lt (by norm_num),H₂⟩

end CentralUnimodality.MarkedExcursion
