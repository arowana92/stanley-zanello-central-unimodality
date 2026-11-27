module

public import CentralUnimodality.SignedArcBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Bound the sum of the inner Fourier envelope beyond a lattice cutoff.
Use y = ξ^(1/3). The decrease of an explicit elementary function pays for
each whole lattice interval, so the estimate also covers finite grids. -/
@[expose] public section

namespace CentralUnimodality

noncomputable def spectralTerm (c : ℝ) (p : ℕ) (x : ℝ) := x^p*Real.exp (-c*x^2)

private theorem spectral_derivative (c : ℝ) (p : ℕ) (x : ℝ) :
    HasDerivAt (spectralTerm c (p+1)) (spectralTerm c p x*((p:ℝ)+1-2*c*x^2)) x := by
  have h := (hasDerivAt_pow (p+1) x).mul (((hasDerivAt_pow 2 x).const_mul (-c)).exp)
  convert h using 1
  · rfl
  · simp [spectralTerm,pow_succ]
    ring

theorem spectral_antitone {c A : ℝ} {p : ℕ} (hc : 0 ≤ c) (hA : 0 ≤ A) (hp : 0 < p)
    (hs : (p:ℝ) ≤ 2*c*A^2) : AntitoneOn (spectralTerm c p) (Set.Ici A) := by
  obtain ⟨p,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  have d := spectral_derivative c p
  have hd : Differentiable ℝ (spectralTerm c (p+1)) := fun x => (d x).differentiableAt
  apply antitoneOn_of_deriv_nonpos (convex_Ici _) hd.continuous.continuousOn hd.differentiableOn
  intro x hx
  have hAx : A ≤ x := interior_subset hx
  rw [(d x).deriv]
  apply mul_nonpos_of_nonneg_of_nonpos
  · unfold spectralTerm
    exact mul_nonneg (pow_nonneg (hA.trans hAx) _) (Real.exp_pos _).le
  · push_cast at hs
    have h := (sq_le_sq₀ hA (hA.trans hAx)).mpr hAx
    nlinarith only [hs,mul_le_mul_of_nonneg_left h hc]

theorem spectral_step {c C A B : ℝ} {p : ℕ} (hc : 0 ≤ c) (hA : 0 ≤ A) (hAB : A ≤ B)
    (hp : 0 < p) (hs : (p:ℝ) ≤ 2*c*A^2) (hK : 0 ≤ 2*c*C-3)
    (hmargin : C*((p:ℝ)+1) ≤ (2*c*C-3)*A^2) :
    (B^3-A^3)*spectralTerm c p B ≤ C*(spectralTerm c (p+1) A-spectralTerm c (p+1) B) := by
  let f (x : ℝ) := C*spectralTerm c (p+1) x + x^3*spectralTerm c p B
  have hd (x : ℝ) : HasDerivAt f (C*(spectralTerm c p x*((p:ℝ)+1-2*c*x^2))+
      (3*x^2)*spectralTerm c p B) x :=
    ((spectral_derivative c p x).const_mul C).add ((hasDerivAt_pow 3 x).mul_const _)
  have hdiff : Differentiable ℝ f := fun x => (hd x).differentiableAt
  have hm : AntitoneOn f (Set.Icc A B) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc ..) hdiff.continuous.continuousOn hdiff.differentiableOn
    intro x hx
    obtain ⟨hAx,hxB⟩ := (interior_subset hx : x ∈ Set.Icc A B)
    have hmono := spectral_antitone hc hA hp hs hAx hAB hxB
    have hsq := (sq_le_sq₀ hA (hA.trans hAx)).mpr hAx
    have hm := hmargin.trans (mul_le_mul_of_nonneg_left hsq hK)
    have hn : 0 ≤ spectralTerm c p x := mul_nonneg (pow_nonneg (hA.trans hAx) _) (Real.exp_pos _).le
    rw [(hd x).deriv]
    nlinarith only [mul_le_mul_of_nonneg_right hm hn,mul_le_mul_of_nonneg_left hmono (sq_nonneg x)]
  have h := hm (Set.left_mem_Icc.mpr hAB) (Set.right_mem_Icc.mpr hAB) hAB
  dsimp [f] at h
  linarith only [h]

/-- A grid may stop at any finite upper frequency. The right endpoint of
each interval supplies its summand. -/
theorem spectral_grid {c C A Δ : ℝ} {p : ℕ} (hc : 0 ≤ c) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hp : 0 < p) (hs : (p:ℝ) ≤ 2*c*A^2) (hK : 0 ≤ 2*c*C-3)
    (hmargin : C*((p:ℝ)+1) ≤ (2*c*C-3)*A^2) (y : ℕ → ℝ) (hy : A ≤ y 0)
    (hmono : Monotone y) (hΔ : ∀ i, (y (i+1))^3-(y i)^3 = Δ) (k : ℕ) :
    ∑ i ∈ Finset.range k, Δ*spectralTerm c p (y (i+1)) ≤ C*spectralTerm c (p+1) A := by
  have step (i : ℕ) : Δ*spectralTerm c p (y (i+1)) ≤
      C*(spectralTerm c (p+1) (y i)-spectralTerm c (p+1) (y (i+1))) := by
    have h := hy.trans (hmono (Nat.zero_le i))
    have hsq := (sq_le_sq₀ hA (hA.trans h)).mpr h
    rw [← hΔ i]
    exact spectral_step hc (hA.trans h) (hmono (Nat.le_succ i)) hp
      (hs.trans (mul_le_mul_of_nonneg_left hsq (by positivity))) hK (hmargin.trans (mul_le_mul_of_nonneg_left hsq hK))
  have hsum : ∑ i ∈ Finset.range k, Δ*spectralTerm c p (y (i+1)) ≤
      C*(spectralTerm c (p+1) (y 0)-spectralTerm c (p+1) (y k)) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      linarith only [ih,step k]
  have hsp : (p+1:ℕ) ≤ 2*c*A^2 := by
    push_cast
    by_contra! h
    have he := mul_le_mul_of_nonneg_left h.le hC
    have hz := sq_nonneg A
    by_cases hz' : A=0
    · rw [hz'] at hs
      simp at hs
      omega
    · nlinarith only [hmargin,he,sq_pos_of_ne_zero hz']
  have hinit := spectral_antitone hc hA (Nat.zero_lt_succ p) hsp (le_refl A) hy hy
  have hn : 0 ≤ spectralTerm c (p+1) (y k) := mul_nonneg (pow_nonneg ((hA.trans hy).trans
    (hmono (Nat.zero_le k))) _) (Real.exp_pos _).le
  apply hsum.trans
  exact mul_le_mul_of_nonneg_left (by linarith only [hinit,hn]) hC

end CentralUnimodality
