module

public import CentralUnimodality.FreeSuffixArcs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-! Fourier bounds for the displacement of the independent middle block.
Each down-step has unit weight, regardless of its original rank label. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real MeasureTheory

noncomputable def downTransform (c u : ℝ) (t : ℕ) (θ : ℝ) :=
  ∑ w ∈ words t, (signMass c u w:ℂ)*phase (θ*((wordParts w).length:ℝ))

noncomputable def downMass (c u : ℝ) (t : ℕ) (j : ℤ) :=
  ∑ w ∈ words t, if ((wordParts w).length:ℤ)=j then signMass c u w else 0

private theorem down_step (c u θ : ℝ) (t : ℕ) : downTransform c u (t+1) θ =
    ((upChance u:ℂ)+(upChance (-u):ℂ)*phase θ)*downTransform c (u-c) t θ := by
  rw [downTransform,sum_cons_words,downTransform,add_mul,Finset.mul_sum,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro w _
  · simp [signMass,step,upChance,wordParts,mul_assoc]
  · simp only [signMass,step,wordParts,Int.cast_neg,Int.cast_one,mul_neg,mul_one,List.length_append,
      List.length_singleton,Nat.cast_add,Nat.cast_one,mul_add,phase_add,Complex.ofReal_mul]
    unfold upChance
    rw [cosh_neg]; ring

theorem down_transform_bound (c u θ : ℝ) (t : ℕ) {p : ℝ}
    (hp : ∀ i < t, p ≤ upChance (-(u-c*i))*upChance (u-c*i)) :
    ‖downTransform c u t θ‖ ≤ exp (-2*p*t*sin (θ/2)^2) := by
  induction t generalizing u with
  | zero => simp [downTransform,words,signMass,wordParts]
  | succ t ih =>
    let q := upChance (-u)
    have hq : 1-q=upChance u := by dsimp [q]; linarith only [up_total u]
    have he : bernoulliFactor q θ = phase (-q*θ)*((upChance u:ℂ)+(q:ℂ)*phase θ) := by
      change (1-(q:ℂ))*phase (-q*θ)+(q:ℂ)*phase ((1-q)*θ) = _
      rw [show (1-q)*θ=(-q*θ)+θ by ring,phase_add,← hq]; push_cast; ring
    have h := bernoulli_modulus q θ
    rw [he,norm_mul,phase_norm,one_mul,hq] at h
    have h₀ : p ≤ q*upChance u := by simpa [q] using hp 0 (by omega)
    have hp' (i : ℕ) (hi : i < t) : p ≤ upChance (-((u-c)-c*i))*upChance ((u-c)-c*i) := by
      have H := hp (i+1) (by omega)
      simpa [Nat.cast_add,mul_add,sub_sub,add_comm] using H
    rw [down_step,norm_mul]
    apply (mul_le_mul h (ih (u-c) hp') (norm_nonneg _) (exp_pos _).le).trans
    rw [← exp_add]
    apply exp_le_exp.mpr
    push_cast; nlinarith only [mul_le_mul_of_nonneg_right h₀ (sq_nonneg (sin (θ/2)))]

theorem down_mass_inverse (c u : ℝ) (t : ℕ) (j : ℤ) :
    (∫ θ in -π..π, downTransform c u t θ*phase (-θ*j)) = (((2*π)*downMass c u t j:ℝ):ℂ) := by
  simp only [downTransform,Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · rw [downMass,Complex.ofReal_mul,Complex.ofReal_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    let z := ((wordParts w).length:ℤ)
    have he (θ : ℝ) : (signMass c u w:ℂ)*phase (θ*((wordParts w).length:ℝ))*phase (-θ*j) =
        (signMass c u w:ℂ)*phase (θ*((z-j:ℤ):ℝ)) := by
      rw [mul_assoc,← phase_add,Int.cast_sub]; dsimp [z]; push_cast; ring_nf
    simp_rw [he]
    rw [intervalIntegral.integral_const_mul,integral_lattice_phase]
    by_cases h : z=j
    · rw [ite_eq_left (sub_eq_zero.mpr h),ite_eq_left (show ((wordParts w).length:ℤ)=j from h),mul_comm]
    · rw [ite_eq_right (sub_ne_zero.mpr h),ite_eq_right (show ((wordParts w).length:ℤ) ≠ j from h)]; simp
  · intro w _
    apply Continuous.intervalIntegrable
    dsimp [phase]; fun_prop

theorem down_modulus_arcs (c u θ : ℝ) (t : ℕ) (hπ : |θ| ≤ π)
    (hp : ∀ i < t, 119/500 ≤ upChance (-(u-c*i))*upChance (u-c*i)) :
    ‖downTransform c u t θ‖ ≤ exp (-(119/1440)*t*θ^2)+exp (-(119/360)*t) := by
  have H := down_transform_bound c u θ t hp
  have hsin : sin (θ/2)^2=sin (|θ|/2)^2 := by
    rcases le_total 0 θ with h|h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h,neg_div,sin_neg,neg_sq]
  rw [hsin] at H
  by_cases h : |θ| ≤ 2
  · have h₁ := sine_chord_one (x := |θ|/2) (by positivity) (by linarith)
    have h₂ := pow_le_pow_left₀ (by positivity : 0 ≤ 161/192*(|θ|/2)) h₁ 2
    have hh : (25/144)*θ^2 ≤ sin (|θ|/2)^2 := by
      simp only [mul_pow,div_pow,sq_abs] at h₂
      nlinarith only [h₂,sq_nonneg θ]
    apply H.trans (le_trans (exp_le_exp.mpr _) (le_add_of_nonneg_right (exp_pos _).le))
    nlinarith only [mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg (α:=ℝ) t)]
  · have h₁ := sine_chord_one (x := 1) (by norm_num) le_rfl
    have hm := strictMonoOn_sin.monotoneOn (a := (1:ℝ)) (b := |θ|/2)
      (show 1 ∈ Set.Icc (-(π/2)) (π/2) from ⟨by linarith only [pi_pos],by linarith only [Real.pi_gt_three]⟩)
      (show |θ|/2 ∈ Set.Icc (-(π/2)) (π/2) from ⟨by linarith only [pi_pos,abs_nonneg θ],by linarith only [hπ]⟩)
      (by linarith only [le_of_not_ge h])
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5/6) ((by linarith only [h₁] : 5/6 ≤ sin 1).trans hm) 2
    apply H.trans (le_trans (exp_le_exp.mpr _) (le_add_of_nonneg_left (exp_pos _).le))
    nlinarith only [mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg (α:=ℝ) t)]

end CentralUnimodality.MarkedExcursion
