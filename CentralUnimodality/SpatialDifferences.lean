module

public import CentralUnimodality.FourierWindowSigns
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! A first difference is a derivative at a point between adjacent sites;
a second difference is a second derivative between the three sites. The
second statement applies the mean value theorem to the translated
difference, avoiding any assumption on the locations of two separate
one-step witnesses. -/
@[expose] public section

namespace CentralUnimodality

private theorem mean_step {f g : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (g x) x) (x h : ℝ) (hh : 0 < h) :
    ∃ u ∈ Set.Ioo x (x+h), f (x+h)-f x = h*g u := by
  obtain ⟨u,hu,he⟩ := exists_hasDerivAt_eq_slope f g (by linarith : x < x+h)
    ((continuous_iff_continuousAt.mpr fun t => (hf t).continuousAt).continuousOn) (fun t _ => hf t)
  refine ⟨u,hu,?_⟩
  rw [show x+h-x = h by ring] at he
  rw [(eq_div_iff hh.ne').mp he |>.symm,mul_comm]

theorem second_mean_step {f g d : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (g x) x)
    (hg : ∀ x, HasDerivAt g (d x) x) (x h : ℝ) (hh : 0 < h) :
    ∃ u ∈ Set.Ioo x (x+2*h), f (x+2*h)-2*f (x+h)+f x = h^2*d u := by
  have ht (z : ℝ) : HasDerivAt (fun y => f (y+h)-f y) (g (z+h)-g z) z :=
    (HasDerivAt.comp_add_const z h (hf (z+h))).sub (hf z)
  obtain ⟨v,hv,he⟩ := mean_step ht x h hh
  obtain ⟨u,hu,hd⟩ := mean_step hg v h hh
  refine ⟨u,⟨hv.1.trans hu.1,by linarith only [hu.2,hv.2]⟩,?_⟩
  rw [show x+h+h = x+2*h by ring,hd] at he
  linarith only [he]

/-- Scale and sample the trigonometric polynomial at a rank. The site
moves to the left by one divided by the group scale as rank increases. -/
noncomputable def spatialSite (n δ j : ℕ) (G : ℝ) : ℝ := (signedAreaAtRank n δ j:ℝ)/(2*G)

noncomputable def spatialCosine (Q J : ℕ) (G : ℝ) (A : ℕ → ℝ) (x : ℝ) : ℝ :=
  (4*G/Q)*∑ t ∈ positiveModes J, A t*Real.cos (G*gridFrequency Q t*x)

private theorem site_step (n δ j : ℕ) (G : ℝ) :
    spatialSite n δ (j+1) G = spatialSite n δ j G-1/G := by
  have he : signedAreaAtRank n δ (j+1) = signedAreaAtRank n δ j-2 := by simp [signedAreaAtRank]; ring
  simp only [spatialSite,he,Int.cast_sub,Int.cast_ofNat]
  ring

private theorem spatial_sample (n δ Q J : ℕ) {G : ℝ} (hG : 0 < G) (A : ℕ → ℝ) (j : ℕ) :
    G*(cosineInverse n δ Q J A j).re =
      G*(2/Q)*(siteFourierTerm n δ 0 0).re + spatialCosine Q J G A (spatialSite n δ j G) := by
  have hz : siteFourierTerm n δ 0 j = siteFourierTerm n δ 0 0 := by simp [siteFourierTerm,areaCharacter]
  have hphase (t : ℕ) : G*gridFrequency Q t*spatialSite n δ j G =
      (gridFrequency Q t/2)*signedAreaAtRank n δ j := by
    unfold spatialSite
    field_simp
  rw [cosineInverse,hz]
  simp only [spatialCosine,hphase,Complex.mul_re,Complex.add_re,Complex.re_sum,Complex.ofReal_re,
    show (2:ℂ).re = 2 by norm_num,Complex.ofReal_im,mul_zero,sub_zero,amplitude_cosine]
  have hQ : (2/(Q:ℂ)) = ((2/(Q:ℝ):ℝ):ℂ) := by push_cast; rfl
  rw [hQ]
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,← Finset.mul_sum]
  ring

theorem spatial_first_difference {n δ Q J : ℕ} {G : ℝ} (hG : 0 < G) (A : ℕ → ℝ) (j : ℕ)
    {g : ℝ → ℝ} (hg : ∀ x, HasDerivAt (spatialCosine Q J G A) (g x) x) :
    ∃ u ∈ Set.Ioo (spatialSite n δ (j+1) G) (spatialSite n δ j G),
      G^2*(fwdDiff 1 (cosineInverse n δ Q J A) j).re = -g u := by
  let x := spatialSite n δ (j+1) G
  have he : x+1/G = spatialSite n δ j G := by dsimp [x]; rw [site_step]; ring
  obtain ⟨u,hu,hm⟩ := mean_step hg x (1/G) (by positivity)
  rw [he] at hu hm
  refine ⟨u,hu,?_⟩
  have h₀ := spatial_sample n δ Q J hG A j
  have h₁ := spatial_sample n δ Q J hG A (j+1)
  dsimp only [x] at hm
  simp only [fwdDiff,Complex.sub_re]
  field_simp at hm
  linear_combination G*h₁ - G*h₀ - hm

theorem spatial_second_difference {n δ Q J : ℕ} {G : ℝ} (hG : 0 < G) (A : ℕ → ℝ) (j : ℕ)
    {g d : ℝ → ℝ} (hg : ∀ x, HasDerivAt (spatialCosine Q J G A) (g x) x)
    (hd : ∀ x, HasDerivAt g (d x) x) :
    ∃ u ∈ Set.Ioo (spatialSite n δ (j+2) G) (spatialSite n δ j G),
      G^3*((fwdDiff 1)^[2] (cosineInverse n δ Q J A) j).re = d u := by
  let x := spatialSite n δ (j+2) G
  have h₁ : x+1/G = spatialSite n δ (j+1) G := by dsimp [x]; rw [site_step n δ (j+1)]; ring
  have h₂ : x+2*(1/G) = spatialSite n δ j G := by
    rw [show x+2*(1/G) = (x+1/G)+1/G by ring,h₁,site_step]; ring
  obtain ⟨u,hu,hm⟩ := second_mean_step hg hd x (1/G) (by positivity)
  rw [h₂] at hu hm
  rw [h₁] at hm
  refine ⟨u,hu,?_⟩
  dsimp only [x] at hm
  have ha := spatial_sample n δ Q J hG A j
  have hb := spatial_sample n δ Q J hG A (j+1)
  have hc := spatial_sample n δ Q J hG A (j+2)
  change G^3*((fwdDiff 1 (fwdDiff 1 (cosineInverse n δ Q J A)) j).re) = d u
  simp only [fwdDiff,Complex.sub_re]
  field_simp at hm
  linear_combination G^2*ha - 2*G^2*hb + G^2*hc + hm

end CentralUnimodality
