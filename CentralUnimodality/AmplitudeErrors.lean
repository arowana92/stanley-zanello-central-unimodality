module

public import CentralUnimodality.RetainedPairs

/-! Propagate enclosures for individual retained conditional amplitudes
through the inverse, using the small difference multiplier at each mode. -/
@[expose] public section

namespace CentralUnimodality

noncomputable def cosineInverse (n δ Q J : ℕ) (a : ℕ → ℝ) (j : ℕ) : ℂ :=
  (2/(Q:ℂ))*(siteFourierTerm n δ 0 j + ∑ t ∈ positiveModes J,
    (2:ℂ)*(amplitudeTerm n δ (gridFrequency Q t) (a t) j).re)

theorem exact_cosine_inverse {n δ Q J : ℕ} (hδ : δ ≤ 1) (hQ : 2*J < Q) :
    gridReconstruction n δ Q (retainedModes Q J) =
      cosineInverse n δ Q J (fun t => signedAmplitude n δ (gridFrequency Q t)) := by
  funext j
  exact retained_inverse_pairs hδ hQ j

theorem amplitude_cosine (n δ j : ℕ) (θ a : ℝ) :
    (amplitudeTerm n δ θ a j).re = a*Real.cos ((θ/2)*signedAreaAtRank n δ j) := by
  rw [amplitudeTerm,Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,areaCharacter,
    Int.cast_neg,mul_neg,Complex.exp_ofReal_mul_I_re,Real.cos_neg]
  ring

private noncomputable def modeError (n δ Q : ℕ) (a b : ℕ → ℝ) (r t j : ℕ) : ℂ :=
  amplitudeTerm n δ (gridFrequency Q t) (a t-b t) j*(areaCharacter (gridFrequency Q t) 1-1)^r

private theorem mode_error_step (n δ Q j t r : ℕ) (a b : ℕ → ℝ) :
    modeError n δ Q a b r t (j+1) - modeError n δ Q a b r t j =
      modeError n δ Q a b (r+1) t j := by
  have he : -signedAreaAtRank n δ (j+1) = -signedAreaAtRank n δ j+2 := by
    simp [signedAreaAtRank]
    ring
  have hc (θ : ℝ) : areaCharacter (θ/2) 2 = areaCharacter θ 1 := by
    unfold areaCharacter
    norm_num
  simp only [modeError,amplitudeTerm,he,areaCharacter_add,hc,pow_succ]
  ring

private theorem inverse_error_formula (n δ Q J j r : ℕ) (a b : ℕ → ℝ) :
    (fwdDiff 1)^[r] (cosineInverse n δ Q J a) j - (fwdDiff 1)^[r] (cosineInverse n δ Q J b) j =
      (4/(Q:ℂ))*∑ t ∈ positiveModes J, ((modeError n δ Q a b r t j).re:ℂ) := by
  induction r generalizing j with
  | zero =>
    simp only [Function.iterate_zero_apply,cosineInverse,modeError,pow_zero,mul_one,← mul_sub,add_sub_add_left_eq_sub,
      ← Finset.sum_sub_distrib]
    rw [show (4/(Q:ℂ)) = (2/Q)*2 by ring,mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    have he : ∀ θ x y, amplitudeTerm n δ θ (x-y) j = amplitudeTerm n δ θ x j-amplitudeTerm n δ θ y j := by
      intros; simp [amplitudeTerm,mul_sub]
    rw [he,Complex.sub_re,Complex.ofReal_sub]
  | succ r ih =>
    simp only [Function.iterate_succ_apply',fwdDiff]
    rw [show ∀ x y z w : ℂ, (x-y)-(z-w) = (x-z)-(y-w) by intros; ring,ih,ih,← mul_sub,← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    rw [← Complex.ofReal_sub,← Complex.sub_re,mode_error_step]

/-- For either adjacent difference, the error contributed by a retained
mode scales with its own frequency, for any real amplitude approximations. -/
theorem cosine_inverse_error {Q : ℕ} (hq : 0 < Q) (n δ J j r : ℕ) (a b e : ℕ → ℝ)
    (he : ∀ t ∈ positiveModes J, |a t-b t| ≤ e t) :
    ‖(fwdDiff 1)^[r] (cosineInverse n δ Q J a) j - (fwdDiff 1)^[r] (cosineInverse n δ Q J b) j‖ ≤
      (4/(Q:ℝ))*∑ t ∈ positiveModes J, (gridFrequency Q t)^r*e t := by
  rw [inverse_error_formula,norm_mul,norm_div,Complex.norm_natCast]
  have hfour : ‖(4:ℂ)‖ = (4:ℝ) := by norm_num
  rw [hfour]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_sum_le ..).trans
  apply Finset.sum_le_sum
  intro t ht
  have hθ : 0 ≤ gridFrequency Q t := by unfold gridFrequency; positivity
  have hm : ‖areaCharacter (gridFrequency Q t) 1-1‖ ≤ gridFrequency Q t := by
    simpa [areaCharacter,mul_comm Complex.I,Real.norm_eq_abs,abs_of_nonneg hθ]
      using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := gridFrequency Q t))
  rw [Complex.norm_real,Real.norm_eq_abs]
  apply (Complex.abs_re_le_norm _).trans
  simp only [modeError,amplitudeTerm,norm_mul,norm_areaCharacter,one_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  rw [mul_comm]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hm r) (he t ht) (abs_nonneg _) (by positivity)

end CentralUnimodality
