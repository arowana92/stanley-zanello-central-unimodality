module

public import CentralUnimodality.DyadicResidual
public import Mathlib.RingTheory.PowerSeries.Expand

/-! The verifier stores the two parities in separate real arrays indexed
by half-length. Bridge coefficients at odd word lengths vanish, so each
residual is an ordinary convolution with the same even bridge array. -/
@[expose] public section

namespace CentralUnimodality

open PowerSeries

noncomputable def halfSeries (δ : ℕ) (F : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun i => coeff (2*i+δ) F

noncomputable def interleaveSeries (A B : PowerSeries ℂ) : PowerSeries ℂ :=
  expand 2 (by decide) A + expand 2 (by decide) B * X

private theorem interleave_even (A B : PowerSeries ℂ) (i : ℕ) :
    coeff (2*i) (interleaveSeries A B) = coeff i A := by
  rw [interleaveSeries,map_add,coeff_expand_mul]
  cases i with
  | zero => simp
  | succ i =>
    rw [show 2*(i+1) = (2*i+1)+1 by omega,← pow_one (X : PowerSeries ℂ),coeff_mul_X_pow,
      coeff_expand_of_not_dvd (h := by omega),add_zero]

private theorem interleave_odd (A B : PowerSeries ℂ) (i : ℕ) :
    coeff (2*i+1) (interleaveSeries A B) = coeff i B := by
  rw [interleaveSeries,map_add,coeff_expand_of_not_dvd (h := by omega),zero_add,
    ← pow_one (X : PowerSeries ℂ),coeff_mul_X_pow,coeff_expand_mul]

private theorem half_coeff (δ i : ℕ) (F : PowerSeries ℂ) : coeff i (halfSeries δ F) = coeff (2*i+δ) F :=
  coeff_mk ..

private theorem interleave_halves (F : PowerSeries ℂ) :
    interleaveSeries (halfSeries 0 F) (halfSeries 1 F) = F := by
  ext1 i
  rcases (by omega : i = 2*(i/2) ∨ i = 2*(i/2)+1) with he|he
  · conv_lhs => rw [he,interleave_even,half_coeff,Nat.add_zero,← he]
  · conv_lhs => rw [he,interleave_odd,half_coeff,← he]

private theorem even_bridge (θ : ℝ) : fairSeries (areaCharacter (θ/2)) bridges =
    expand 2 (by decide) (halfSeries 0 (fairSeries (areaCharacter (θ/2)) bridges)) := by
  let B := fairSeries (areaCharacter (θ/2)) bridges
  have he : halfSeries 1 B = 0 := by
    ext1 i
    rw [half_coeff]
    have hb : bridges (2*i+1) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      obtain ⟨hl,hz⟩ := Finset.mem_filter.mp hw
      have hm := mem_words.mp hl
      have h := bridge_length hz
      omega
    simp [B,coeff_walkSeries,hb]
  have h := interleave_halves B
  rw [he,interleaveSeries,map_zero,zero_mul,add_zero] at h
  exact h.symm

theorem interleaved_residual (θ : ℝ) (A B : PowerSeries ℂ) :
    let F := fairSeries (areaCharacter (θ/2)) words
    let R := fairSeries (areaCharacter (θ/2)) bridges
    F - R*interleaveSeries A B = interleaveSeries
      (halfSeries 0 F - halfSeries 0 R * A) (halfSeries 1 F - halfSeries 0 R * B) := by
  dsimp only
  conv_lhs => lhs; rw [← interleave_halves (fairSeries (areaCharacter (θ/2)) words)]
  conv_lhs => rhs; lhs; rw [even_bridge]
  simp only [interleaveSeries,map_sub,map_mul]
  ring

/-- Residuals measured separately on the two half-length arrays control
the signed conditional amplitude at the required strict word length. -/
theorem half_length_amplitude (n δ : ℕ) (hδ : δ ≤ 1) (θ : ℝ) (V : ℕ → PowerSeries ℂ) (e : ℝ)
    (h : ∀ σ ≤ 1, ∀ i ≤ n+δ, ‖coeff i (
      halfSeries σ (fairSeries (areaCharacter (θ/2)) words) -
      halfSeries 0 (fairSeries (areaCharacter (θ/2)) bridges) * V σ)‖ ≤ e) :
    |signedAmplitude n δ θ-(coeff (n+δ) (V (1-δ))).re/survival (n+δ)| ≤ 2*e/survival (n+δ) := by
  have he := amplitude_of_residual n δ θ (interleaveSeries (V 0) (V 1)) e (by
    intro i hi
    rw [interleaved_residual]
    rcases (by omega : i = 2*(i/2) ∨ i = 2*(i/2)+1) with hEven|hOdd
    · conv_lhs => rw [hEven,interleave_even]
      exact h 0 (by decide) _ (by omega)
    · conv_lhs => rw [hOdd,interleave_odd]
      exact h 1 (by decide) _ (by omega))
  unfold residualAmplitude at he
  rcases (by omega : δ = 0 ∨ δ = 1) with rfl|rfl
  · simpa only [Nat.add_zero,interleave_odd,show (2*n+1)/2 = n by omega,Nat.sub_zero] using he
  · simpa only [show 2*n+1+1 = 2*(n+1) by omega,interleave_even,Nat.mul_div_cancel_left _ (by decide : 0 < 2),
      Nat.sub_self] using he

end CentralUnimodality
