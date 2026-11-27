module

public import CentralUnimodality.AmplitudeErrors

/-! An a posteriori transform certificate for the actual rank differences.
The input consists of residual bounds on the free/bridge convolutions and
optional additional errors in the real conditional amplitudes. -/
@[expose] public section

namespace CentralUnimodality

open PowerSeries

noncomputable def residualAmplitude (m : ℕ) (V : PowerSeries ℂ) : ℝ :=
  (coeff (m+1) V).re/survival ((m+1)/2)

theorem amplitude_of_residual (n δ : ℕ) (θ : ℝ) (V : PowerSeries ℂ) (e : ℝ)
    (h : ∀ i ≤ 2*n+δ+1, ‖coeff i (fairSeries (areaCharacter (θ/2)) words -
      fairSeries (areaCharacter (θ/2)) bridges * V)‖ ≤ e) :
    |signedAmplitude n δ θ-residualAmplitude (2*n+δ) V| ≤ 2*e/survival ((2*n+δ+1)/2) := by
  have hE := fairSeries_residual_bound _ (areaCharacter_zero _) (areaCharacter_add _)
    (fun x => (norm_areaCharacter _ x).le) V (2*n+δ+1) e h
  rw [map_sub] at hE
  unfold signedAmplitude residualAmplitude
  rw [← sub_div,abs_div,abs_of_pos (survival_pos _),← Complex.sub_re]
  exact div_le_div_of_nonneg_right ((Complex.abs_re_le_norm _).trans hE) (survival_pos _).le

noncomputable def spectralAllowance (G : ℝ) (Q J r : ℕ) (e : ℕ → ℝ) : ℝ :=
  (4*G/Q)*∑ t ∈ positiveModes J, (G*gridFrequency Q t)^r*e t

private theorem scaled_amplitude_error {n δ Q J : ℕ} (hδ : δ ≤ 1) (hQ : 2*J < Q)
    {G : ℝ} (hG : 0 ≤ G) (j r : ℕ) (a e : ℕ → ℝ)
    (he : ∀ t ∈ positiveModes J, |signedAmplitude n δ (gridFrequency Q t)-a t| ≤ e t) :
    G^(r+1)*‖(fwdDiff 1)^[r] (gridReconstruction n δ Q (retainedModes Q J)) j -
      (fwdDiff 1)^[r] (cosineInverse n δ Q J a) j‖ ≤ spectralAllowance G Q J r e := by
  rw [exact_cosine_inverse hδ hQ]
  apply (mul_le_mul_of_nonneg_left (cosine_inverse_error (by omega) n δ J j r _ _ _ he)
    (pow_nonneg hG _)).trans_eq
  simp only [spectralAllowance,mul_pow,mul_assoc,← Finset.mul_sum,pow_succ]
  ring

theorem certified_rank_differences {n δ Q J j : ℕ} (hδ : δ ≤ 1) (hn : 2049 ≤ n+δ)
    (hmax : n+δ ≤ 300000) (hj : j+2 ≤ n*(n+δ)) (hNy : 2*J < Q)
    (hQ : 5*Witness.cellScale (n+δ) ≤ Q)
    (hJ : 2048 ≤ (2*Real.pi*Witness.cellScale (n+δ)/Q)*J)
    (hx : ((n*(n+δ)-j:ℕ):ℝ)+(3*n+2*δ+1)/2 ≤ 0.63*Witness.cellScale (n+δ))
    {G : ℝ} (hG : 0 ≤ G) (hGS : G ≤ Witness.cellScale (n+δ))
    (a e : ℕ → ℝ) (he : ∀ t ∈ positiveModes J, |signedAmplitude n δ (gridFrequency Q t)-a t| ≤ e t) :
    let P := rankProbability n δ
    let T := cosineInverse n δ Q J a
    G^2*‖fwdDiff 1 P j-fwdDiff 1 T j‖ ≤ 0.00026+spectralAllowance G Q J 1 e ∧
    G^3*‖(fwdDiff 1)^[2] P j-(fwdDiff 1)^[2] T j‖ ≤ 0.95+spectralAllowance G Q J 2 e := by
  let P := rankProbability n δ
  let F := gridReconstruction n δ Q (retainedModes Q J)
  let T := cosineInverse n δ Q J a
  let S := Witness.cellScale (n+δ)
  have h (r : ℕ) (c : ℝ) (hc : S^(r+1)*‖(fwdDiff 1)^[r] P j-(fwdDiff 1)^[r] F j‖ ≤ c) :
      G^(r+1)*‖(fwdDiff 1)^[r] P j-(fwdDiff 1)^[r] T j‖ ≤ c+spectralAllowance G Q J r e := by
    have hsc := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hG hGS (r+1))
      (norm_nonneg ((fwdDiff 1)^[r] P j-(fwdDiff 1)^[r] F j))
    have ht := norm_sub_le_norm_sub_add_norm_sub ((fwdDiff 1)^[r] P j) ((fwdDiff 1)^[r] F j) ((fwdDiff 1)^[r] T j)
    apply (mul_le_mul_of_nonneg_left ht (pow_nonneg hG _)).trans
    rw [mul_add]
    exact add_le_add (hsc.trans hc) (scaled_amplitude_error hδ hNy hG j r a e he)
  have hc := rank_truncation_two_orders hδ hn hmax hj hQ hJ hx
  exact ⟨h 1 _ hc.1,h 2 _ hc.2⟩

/-- A real amplitude may also include interpolation or conversion error.
The certificate uses only the coefficients of each residual through the
actual walk length. -/
theorem residual_rank_differences {n δ Q J j : ℕ} (hδ : δ ≤ 1) (hn : 2049 ≤ n+δ)
    (hmax : n+δ ≤ 300000) (hj : j+2 ≤ n*(n+δ)) (hNy : 2*J < Q)
    (hQ : 5*Witness.cellScale (n+δ) ≤ Q)
    (hJ : 2048 ≤ (2*Real.pi*Witness.cellScale (n+δ)/Q)*J)
    (hx : ((n*(n+δ)-j:ℕ):ℝ)+(3*n+2*δ+1)/2 ≤ 0.63*Witness.cellScale (n+δ))
    {G : ℝ} (hG : 0 ≤ G) (hGS : G ≤ Witness.cellScale (n+δ))
    (V : ℕ → PowerSeries ℂ) (a b e : ℕ → ℝ)
    (hres : ∀ t ∈ positiveModes J, ∀ i ≤ 2*n+δ+1,
      ‖coeff i (fairSeries (areaCharacter (gridFrequency Q t/2)) words -
        fairSeries (areaCharacter (gridFrequency Q t/2)) bridges * V t)‖ ≤ b t)
    (hfit : ∀ t ∈ positiveModes J, |residualAmplitude (2*n+δ) (V t)-a t| ≤ e t) :
    let E := fun t => 2*b t/survival ((2*n+δ+1)/2)+e t
    let P := rankProbability n δ
    let T := cosineInverse n δ Q J a
    G^2*‖fwdDiff 1 P j-fwdDiff 1 T j‖ ≤ 0.00026+spectralAllowance G Q J 1 E ∧
    G^3*‖(fwdDiff 1)^[2] P j-(fwdDiff 1)^[2] T j‖ ≤ 0.95+spectralAllowance G Q J 2 E := by
  apply certified_rank_differences hδ hn hmax hj hNy hQ hJ hx hG hGS
  intro t ht
  apply (abs_sub_le _ (residualAmplitude (2*n+δ) (V t)) _).trans
  exact add_le_add (amplitude_of_residual _ _ _ _ _ (hres _ ht)) (hfit _ ht)

end CentralUnimodality
