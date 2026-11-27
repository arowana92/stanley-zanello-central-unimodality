module

public import CentralUnimodality.PairedFourier

/-! Quantitative cancellation in the paired unrestricted block, at all
frequencies. The telescoping formula also holds at multiples of π. -/
@[expose] public section

namespace CentralUnimodality

noncomputable def blockSines (θ : ℝ) (l : ℕ) : ℝ :=
  ∑ i ∈ Finset.range l, (Real.sin ((θ/2)*(2*i+1)))^2

private theorem factor_le_exp (x : ℝ) :
    (1+|Real.cos x|)/2 ≤ Real.exp (-(Real.sin x)^2/4) := by
  apply le_trans _ (Real.add_one_le_exp _)
  nlinarith only [Real.sin_sq_add_cos_sq x,sq_abs (Real.cos x),sq_nonneg (1-|Real.cos x|)]

theorem pairFactor_exp (θ : ℝ) (l : ℕ) : pairFactor (θ/2) l ≤ Real.exp (-blockSines θ l/4) := by
  induction l with
  | zero => simp [pairFactor,blockSines]
  | succ l ih =>
    have h := mul_le_mul ih (factor_le_exp ((θ/2)*(2*l+1))) (by positivity) (Real.exp_pos _).le
    rw [← Real.exp_add] at h
    simpa only [pairFactor,blockSines,Finset.prod_range_succ,Finset.sum_range_succ,neg_add_rev,
      add_div,add_comm] using h

private theorem sine_telescope (x θ : ℝ) :
    4*Real.sin θ*(Real.sin (x/2))^2 =
      2*Real.sin θ-(Real.sin (x+θ)-Real.sin (x-θ)) := by
  rw [Real.sin_sub_sin,show (x+θ-(x-θ))/2 = θ by ring,show (x+θ+(x-θ))/2 = 2*(x/2) by ring,
    Real.cos_two_mul_eq_one_sub]
  ring

theorem blockSines_identity (θ : ℝ) (l : ℕ) :
    4*Real.sin θ*blockSines θ l = 2*l*Real.sin θ-Real.sin (2*l*θ) := by
  induction l with
  | zero => simp [blockSines]
  | succ l ih =>
    rw [blockSines,Finset.sum_range_succ,mul_add,← blockSines,ih]
    have h := sine_telescope ((2*l+1)*θ) θ
    rw [show (2*(l:ℝ)+1)*θ/2 = θ/2*(2*l+1) by ring,
      show (2*(l:ℝ)+1)*θ+θ = 2*((l:ℝ)+1)*θ by ring,
      show (2*(l:ℝ)+1)*θ-θ = 2*l*θ by ring] at h
    rw [Nat.cast_succ]
    linarith only [h]

theorem blockSines_middle {θ : ℝ} {l : ℕ} (hl : 0 < l) (hs : 1/(l:ℝ) ≤ Real.sin θ) :
    (l:ℝ)/4 ≤ blockSines θ l := by
  have hl' : (0:ℝ) < l := by exact_mod_cast hl
  have hpos : 0 < Real.sin θ := lt_of_lt_of_le (by positivity) hs
  have hprod := (div_le_iff₀ hl').mp hs
  apply (le_of_mul_le_mul_left _ (show 0 < 4*Real.sin θ by positivity))
  nlinarith only [blockSines_identity θ l,Real.sin_le_one (2*l*θ),hprod]

end CentralUnimodality
