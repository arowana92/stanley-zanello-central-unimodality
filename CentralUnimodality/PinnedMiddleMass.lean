module

public import CentralUnimodality.PinnedMiddleTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Real.Pi.Bounds

/-! The middle block of a pinned first-hit prefix has probability at most
1/√t at a prescribed displacement for t≥80 and site variances at least .238. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real Set MeasureTheory

private theorem middle_integral_budget {t : ℝ} (ht : 80 ≤ t) :
    (√(π/(119/1440*t))+2*π*exp (-(119/360)*t))*√t ≤ 2*π := by
  have ht' : 0 < t := by linarith
  have hroot : √(π/(119/1440*t))*√t ≤ (99/100)*(2*π) := by
    rw [← Real.sqrt_mul (by positivity),div_mul_eq_mul_div]
    have he : π*t/(119/1440*t)=π/(119/1440) := by field_simp
    rw [he,Real.sqrt_le_iff]
    refine ⟨by positivity,?_⟩
    nlinarith only [mul_le_mul_of_nonneg_right pi_gt_d2.le pi_pos.le]
  have hs : √t ≤ t/8 := by
    apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
    rw [sq_sqrt ht'.le]; nlinarith only [mul_le_mul_of_nonneg_right ht ht'.le]
  have h := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ 119/360*t) 4
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  have he : exp (-(119/360)*t)*√t ≤ 1/100 := by
    rw [neg_mul,exp_neg,← div_eq_inv_mul,div_le_iff₀ (exp_pos _)]
    have h₁ := mul_le_mul_of_nonneg_right ht (sq_nonneg t)
    have h₂ := mul_le_mul_of_nonneg_right ht ht'.le
    nlinarith only [h,hs,h₁,h₂,ht,sq_nonneg t]
  nlinarith only [hroot,mul_le_mul_of_nonneg_left he pi_pos.le]

theorem down_mass_bound (c u : ℝ) {t : ℕ} (ht : 80 ≤ t) (j : ℤ)
    (hp : ∀ i < t, 119/500 ≤ upChance (-(u-c*i))*upChance (u-c*i)) :
    downMass c u t j ≤ 1/√t := by
  let G (θ : ℝ) := exp (-(119/1440*(t:ℝ))*θ^2)
  let C := exp (-(119/360)*(t:ℝ))
  let I := Ioc (-π) π
  have ht' : (80:ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0:ℝ) < t := by linarith
  have hg : Integrable G := integrable_exp_neg_mul_sq (by positivity)
  have hi : IntegrableOn (fun _ : ℝ => C) I := integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hsum : IntegrableOn (fun θ => G θ+C) I := hg.integrableOn.add hi
  have H := norm_integral_le_of_norm_le (μ := volume.restrict I) hsum
    (f := fun θ : ℝ => downTransform c u t θ*phase (-θ*j)) (by
      filter_upwards [ae_restrict_mem (measurableSet_Ioc (a := -π) (b := π))] with θ hθ
      rw [norm_mul,phase_norm,mul_one]
      simpa only [G,C,neg_mul] using down_modulus_arcs c u θ t (abs_le.mpr ⟨hθ.1.le,hθ.2⟩) hp)
  have hπ : -π ≤ π := by linarith only [pi_pos]
  have hr := down_mass_inverse c u t j
  rw [intervalIntegral.integral_of_le hπ] at hr
  have hm : 0 ≤ downMass c u t j := Finset.sum_nonneg fun w _ => by
    split <;> first | exact (signMass_pos ..).le | exact le_rfl
  rw [hr,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity) hm),
    integral_add hg.integrableOn hi,setIntegral_const,Real.volume_real_Ioc_of_le hπ,smul_eq_mul] at H
  have hg' := setIntegral_le_integral (s := I) hg (Filter.Eventually.of_forall (fun θ => (exp_pos _).le))
  unfold G at hg'
  rw [integral_gaussian] at hg'
  have h := middle_integral_budget ht'
  apply (le_div_iff₀ (sqrt_pos.mpr ht0)).mpr
  apply le_of_mul_le_mul_left (a := 2*π) _ (by positivity)
  dsimp only [C] at H
  have h' : (2*π)*downMass c u t j ≤ √(π/(119/1440*t))+2*π*exp (-(119/360)*t) := by
    dsimp only [G] at H
    linarith only [H,hg']
  rw [← mul_assoc,mul_one]
  exact (mul_le_mul_of_nonneg_right h' (sqrt_nonneg _)).trans h

/-- The same uniform estimate for the signed height displacement, including
parity-incompatible endpoints. -/
theorem middle_displacement_bound (c u : ℝ) {t : ℕ} (ht : 80 ≤ t) (h : ℤ)
    (hp : ∀ i < t, 119/500 ≤ upChance (-(u-c*i))*upChance (u-c*i)) :
    (∑ w ∈ (words t).filter (fun w => displacement w=h), signMass c u w) ≤ 1/√t := by
  apply le_trans _ (down_mass_bound c u ht (((t:ℤ)-h)/2) hp)
  rw [Finset.sum_filter,downMass]
  apply Finset.sum_le_sum
  intro w hw
  have H := displacement_length w
  rw [mem_words.mp hw] at H
  split_ifs <;> first | exact le_rfl | exact (signMass_pos ..).le | omega

end CentralUnimodality.MarkedExcursion
