module

public import CentralUnimodality.RankTruncation

/-! Exact pairing for the retained modes below Nyquist, including the
normalization on the zero mode. -/
@[expose] public section

namespace CentralUnimodality

def positiveModes (J : ℕ) := Finset.Icc 1 J

private theorem retained_split {Q J : ℕ} (hQ : 2*J < Q) :
    retainedModes Q J = insert 0 (positiveModes J ∪ (positiveModes J).image (fun t => Q-t)) := by
  ext t
  simp only [retainedModes,Finset.mem_filter,Finset.mem_range,Finset.mem_insert,Finset.mem_union,
    positiveModes,Finset.mem_Icc,Finset.mem_image,min_le_iff]
  constructor
  · rintro ⟨ht,hl|hr⟩
    · by_cases he : t = 0
      · exact Or.inl he
      · exact Or.inr (Or.inl ⟨by omega,hl⟩)
    · exact Or.inr (Or.inr ⟨Q-t,⟨by omega,hr⟩,by omega⟩)
  · rintro (rfl|⟨ht,hj⟩|⟨i,⟨hi,hj⟩,rfl⟩) <;> omega

theorem sum_retained_pairs {Q J : ℕ} (hQ : 2*J < Q) (f : ℕ → ℂ) :
    (∑ t ∈ retainedModes Q J, f t) =
      f 0 + ∑ t ∈ positiveModes J, (f t + f (Q-t)) := by
  have hmem (t : ℕ) : t ∈ positiveModes J ↔ 1 ≤ t ∧ t ≤ J := Finset.mem_Icc
  have hz : 0 ∉ positiveModes J ∪ (positiveModes J).image (fun t => Q-t) := by
    simp only [Finset.mem_union,Finset.mem_image,hmem]
    omega
  have hdis : Disjoint (positiveModes J) ((positiveModes J).image fun t => Q-t) := by
    apply Finset.disjoint_left.mpr
    intro t ht hu
    obtain ⟨u,huPos,rfl⟩ := Finset.mem_image.mp hu
    have := (hmem _).mp ht
    have := (hmem _).mp huPos
    omega
  rw [retained_split hQ,Finset.sum_insert hz,Finset.sum_union hdis,Finset.sum_image,Finset.sum_add_distrib]
  intro i hi j hj he
  have := (hmem _).mp hi
  have := (hmem _).mp hj
  dsimp at he
  omega

noncomputable def signedAmplitude (n δ : ℕ) (θ : ℝ) : ℝ :=
  (PowerSeries.coeff (2*n+δ+1) (fairSeries (areaCharacter (θ/2)) strictWords)).re / survival ((2*n+δ+1)/2)

private theorem signed_amplitude_real {n δ : ℕ} (hδ : δ ≤ 1) (θ : ℝ) :
    (signedAmplitude n δ θ:ℂ) =
      PowerSeries.coeff (2*n+δ+1) (fairSeries (areaCharacter (θ/2)) strictWords) / (survival ((2*n+δ+1)/2):ℂ) := by
  unfold signedAmplitude
  rw [Complex.ofReal_div]
  congr 1
  rw [fourier_signed_ranks _ n δ hδ]
  have he : ∀ r : ℂ, (starRingEnd ℂ) r = r → (r.re:ℂ) = r := by
    intro r hr
    apply Complex.ext
    · rfl
    have hi := congrArg Complex.im hr
    simp only [Complex.conj_im] at hi
    simp only [Complex.ofReal_im]
    linarith only [hi]
  apply he
  simp only [map_inv₀,map_ofNat,map_pow,map_mul,map_sum,map_nsmul,Complex.conj_ofReal]

noncomputable def amplitudeTerm (n δ : ℕ) (θ a : ℝ) (j : ℕ) : ℂ :=
  areaCharacter (θ/2) (-signedAreaAtRank n δ j) * (a:ℂ)

theorem exact_amplitude_term {n δ : ℕ} (hδ : δ ≤ 1) (θ : ℝ) (j : ℕ) :
    siteFourierTerm n δ θ j = amplitudeTerm n δ θ (signedAmplitude n δ θ) j := by
  unfold siteFourierTerm amplitudeTerm
  rw [signed_amplitude_real hδ]
  ring

/-- Twice the real part of the paired inverse, as used in the cosine
evaluation of the Fourier certificate. The constant term cancels in
all differences of positive order. -/
theorem retained_inverse_pairs {n δ Q J : ℕ} (hδ : δ ≤ 1) (hQ : 2*J < Q) (j : ℕ) :
    gridReconstruction n δ Q (retainedModes Q J) j =
      (2/(Q:ℂ))*(siteFourierTerm n δ 0 j +
        ∑ t ∈ positiveModes J, (2:ℂ)*(amplitudeTerm n δ (gridFrequency Q t)
          (signedAmplitude n δ (gridFrequency Q t)) j).re) := by
  rw [gridReconstruction,sum_retained_pairs hQ,show gridFrequency Q 0 = 0 by simp [gridFrequency]]
  congr 2
  apply Finset.sum_congr rfl
  intro t ht
  have hu := Finset.mem_Icc.mp ht
  have hq : (Q:ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have hg : gridFrequency Q (Q-t) = 2*Real.pi-gridFrequency Q t := by
    simp only [gridFrequency,Nat.cast_sub (by omega : t ≤ Q)]
    field_simp
  rw [hg,site_fourier_reflect _ _ _ hδ,exact_amplitude_term hδ,Complex.add_conj]
  push_cast
  ring

end CentralUnimodality
