module

public import CentralUnimodality.OmittedFourier
public import CentralUnimodality.FourierInversion
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Algebra.Group.ForwardDiff

/-! The exact finite-difference multiplier and its symmetry on the signed
half-area lattice. The site phase cancels the possible half-integer shift. -/
@[expose] public section

namespace CentralUnimodality

open PowerSeries

noncomputable def siteFourierTerm (n δ : ℕ) (θ : ℝ) (j : ℕ) : ℂ :=
  areaCharacter (θ/2) (-signedAreaAtRank n δ j) *
    coeff (2*n+δ+1) (fairSeries (areaCharacter (θ/2)) strictWords) / (survival ((2*n+δ+1)/2):ℂ)

theorem norm_site_fourier (n δ j : ℕ) (θ : ℝ) :
    ‖siteFourierTerm n δ θ j‖ = signedMagnitude n δ θ := by
  simp [siteFourierTerm,signedMagnitude,norm_areaCharacter,abs_of_pos (survival_pos _)]

private theorem twice_character (θ : ℝ) (v : ℤ) :
    areaCharacter (θ/2) (2*v) = areaCharacter θ v := by
  unfold areaCharacter
  congr 2
  push_cast
  ring

theorem site_fourier_step (n δ j : ℕ) (θ : ℝ) :
    siteFourierTerm n δ θ (j+1) = siteFourierTerm n δ θ j * areaCharacter θ 1 := by
  have he : -signedAreaAtRank n δ (j+1) = -signedAreaAtRank n δ j+2*1 := by
    simp [signedAreaAtRank]
    ring
  unfold siteFourierTerm
  rw [he,areaCharacter_add,twice_character]
  ring

theorem site_fourier_difference (n δ j r : ℕ) (θ : ℝ) :
    (fwdDiff 1)^[r] (siteFourierTerm n δ θ) j =
      siteFourierTerm n δ θ j * (areaCharacter θ 1-1)^r := by
  induction r generalizing j with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply',fwdDiff,ih,ih,site_fourier_step,pow_succ]
    ring

theorem norm_site_difference (n δ j r : ℕ) {θ : ℝ} (ht : 0 ≤ θ) :
    ‖(fwdDiff 1)^[r] (siteFourierTerm n δ θ) j‖ ≤ θ^r*signedMagnitude n δ θ := by
  have hu : ‖areaCharacter θ 1-1‖ ≤ θ := by
    simpa [areaCharacter,mul_comm Complex.I,Real.norm_eq_abs,abs_of_nonneg ht]
      using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ))
  rw [site_fourier_difference,norm_mul,norm_pow,norm_site_fourier,mul_comm]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hu r) (div_nonneg (norm_nonneg _) (survival_pos _).le)

private theorem reflected_character (θ : ℝ) (v : ℤ) :
    areaCharacter (2*Real.pi-θ) v = (starRingEnd ℂ) (areaCharacter θ v) := by
  unfold areaCharacter
  rw [← Complex.exp_conj]
  push_cast
  rw [show (2*(Real.pi:ℂ)-θ)*v*Complex.I = v*(2*Real.pi*Complex.I)+(θ*v)*(-Complex.I) by ring,
    Complex.exp_add,Complex.exp_int_mul_two_pi_mul_I,one_mul]
  simp

private theorem site_expansion (n δ j : ℕ) (hδ : δ ≤ 1) (θ : ℝ) :
    siteFourierTerm n δ θ j =
      ((2:ℂ)⁻¹^(2*n+δ+1)/(survival ((2*n+δ+1)/2):ℂ)) *
        ∑ l ∈ Finset.range (n*(n+δ)+1), (rankCount (2*n+δ) l:ℂ) *
          (areaCharacter θ ((j:ℤ)-l) + areaCharacter θ ((j:ℤ)+l-signedAreaAtRank n δ 0)) := by
  let A := signedAreaAtRank n δ
  unfold siteFourierTerm
  rw [coeff_walkSeries,signed_ranks _ n δ hδ]
  simp only [nsmul_eq_mul]
  rw [show ∀ (p w x s : ℂ), p*(w*x)/s = (w/s)*(p*x) by intros; ring,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  have h₁ : -A j+A l = 2*((j:ℤ)-l) := by dsimp [A,signedAreaAtRank]; ring
  have h₂ : -A j+ -A l = 2*((j:ℤ)+l-A 0) := by dsimp [A,signedAreaAtRank]; ring
  change _*(_*(areaCharacter _ (A l)+areaCharacter _ (-A l))) = _
  rw [mul_left_comm,mul_add,← areaCharacter_add,← areaCharacter_add]
  rw [h₁,h₂,twice_character,twice_character]

theorem site_fourier_reflect (n δ j : ℕ) (hδ : δ ≤ 1) (θ : ℝ) :
    siteFourierTerm n δ (2*Real.pi-θ) j = (starRingEnd ℂ) (siteFourierTerm n δ θ j) := by
  simp [site_expansion n δ j hδ,reflected_character,map_ofNat]

theorem norm_difference_reflect (n δ j r : ℕ) (hδ : δ ≤ 1) (θ : ℝ) :
    ‖(fwdDiff 1)^[r] (siteFourierTerm n δ (2*Real.pi-θ)) j‖ =
      ‖(fwdDiff 1)^[r] (siteFourierTerm n δ θ) j‖ := by
  rw [site_fourier_difference,site_fourier_difference,site_fourier_reflect _ _ _ hδ,reflected_character,
    ← map_one (starRingEnd ℂ),← map_sub,← map_pow,← map_mul,Complex.norm_conj,map_one]

end CentralUnimodality
