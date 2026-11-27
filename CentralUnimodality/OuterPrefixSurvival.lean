module

public import CentralUnimodality.TiltedPrefixSurvival
public import CentralUnimodality.MarkedHitBound
public import CentralUnimodality.RankArcBounds
import CentralUnimodality.DyckRecurrence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Survival on the outer pieces of a pinned first-hit prefix. The fair
bound retains its sharp 4/5 constant at both parities. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

theorem fair_live_exact (t : ℕ) : live 0 0 t 1 = survival ((t+1)/2) := by
  rw [live_ballots,← ballot_survival]
  have he (w : List Bool) (hw : w ∈ ballots t) : signMass 0 0 w = 1/(2:ℝ)^t := by
    have h := signMass_density 0 0 w
    simp [coshProduct,(mem_ballots.mp hw).1] at h
    exact (eq_div_iff (by positivity)).mpr h
  rw [Finset.sum_congr rfl he,Finset.sum_const,nsmul_eq_mul,← mul_div_assoc,mul_one]
  have hs : survivors 1 t=ballots t := by ext w; simp [survivors,ballots,positive_one_iff]
  rw [← hs,survivors_one_card]

theorem fair_live_upper {t : ℕ} (ht : 0 < t) : live 0 0 t 1 ≤ (4/5)/√t := by
  let n := (t+1)/2
  have hh : (t:ℝ) ≤ 2*n := by exact_mod_cast (by dsimp [n]; omega : t ≤ 2*n)
  have ht' : (0:ℝ) < t := by exact_mod_cast ht
  rw [fair_live_exact,le_div_iff₀ (Real.sqrt_pos.mpr ht')]
  exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hh) (survival_pos n).le).trans (survival_scaled_lt n).le

/-- Drift reversal suppresses the probability of a surviving negative-drift path
by at least a factor cosh(u)^(-t) relative to the fair law. -/
theorem negative_live_factor {u : ℝ} (hu : 0 ≤ u) (t : ℕ) : live 0 (-u) t 1*(cosh u)^t ≤ live 0 0 t 1 := by
  rw [live_ballots,live_ballots,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro w hw
  have hn : (0:ℝ) ≤ displacement w := by exact_mod_cast ballot_endpoint_nonneg (mem_ballots.mp hw).2
  have h := signMass_density 0 (-u) w
  have f := signMass_density 0 0 w
  simp only [coshProduct,zero_mul,sub_zero,cosh_neg,Finset.prod_const,Finset.card_range,
    (mem_ballots.mp hw).1,add_zero,cosh_zero,one_pow,mul_one,exp_zero] at h f
  have he : exp (-u*(displacement w:ℝ)) ≤ 1 := exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) hn)
  apply le_of_mul_le_mul_right (a := (2:ℝ)^t) _ (by positivity)
  linarith only [h,f,he]

private theorem inverse_cosh (u : ℝ) : (cosh u)⁻¹ ≤ exp (-(tanh u)^2/2) := by
  apply (sq_le_sq₀ (inv_pos.mpr (cosh_pos u)).le (exp_pos _).le).mp
  rw [← exp_nat_mul]
  have hi : ((cosh u)⁻¹)^2 = 1-(tanh u)^2 := by
    rw [tanh_eq_sinh_div_cosh]; field_simp [(cosh_pos u).ne']
    nlinarith only [cosh_sq_sub_sinh_sq u]
  rw [hi]
  convert Real.add_one_le_exp (-((tanh u)^2)) using 1 <;> push_cast <;> ring_nf

/-- Homogeneous survival estimate, retaining the tail improvement at
positive drift. The weaker 2u+.8/√t follows immediately. -/
theorem homogeneous_live_upper {u : ℝ} (hu : 0 ≤ u) {t : ℕ} (ht : 0 < t) :
    live 0 u t 1 ≤ 2*tanh u + (4/5)/√t*exp (-((t:ℝ)*(tanh u)^2/2)) := by
  have hd : 0 ≤ tanh u := by
    rw [tanh_eq_sinh_div_cosh]; exact div_nonneg (sinh_nonneg_iff.mpr hu) (cosh_pos _).le
  have hq : 1 ≤ 1+tanh u := by linarith
  have hid : exp (-2*u)*(1+tanh u)=1-tanh u := by
    have hu₁ := up_total u
    have hu₂ := up_drift u
    have he := up_ratio u
    rw [show 1+tanh u=2*upChance u by linarith only [hu₁,hu₂],
      show 1-tanh u=2*upChance (-u) by linarith only [hu₁,hu₂],he]; ring
  have hconst : 1-exp (-2*u) ≤ 2*tanh u := by
    apply le_of_mul_le_mul_right (a := 1+tanh u) _ (by linarith only [hd])
    nlinarith only [hid,sq_nonneg (tanh u)]
  have hh := (negative_live_factor hu t).trans (fair_live_upper ht)
  have hc : 0 < cosh u^t := pow_pos (cosh_pos _) _
  have hf := (le_div_iff₀ hc).mpr hh
  rw [div_eq_mul_inv,← inv_pow] at hf
  have he := pow_le_pow_left₀ (inv_pos.mpr (cosh_pos u)).le (inverse_cosh u) t
  rw [← exp_nat_mul] at he
  have he' : ((cosh u)⁻¹)^t ≤ exp (-((t:ℝ)*(tanh u)^2/2)) := by convert he using 2; ring
  rw [homogeneous_live,pow_one]
  apply add_le_add hconst
  apply (mul_le_of_le_one_left (live_nonneg ..) (exp_le_one_iff.mpr (by linarith only [hu]))).trans
  exact hf.trans (mul_le_mul_of_nonneg_left he' (by positivity))

/-- The maximum natural parameter on an inhomogeneous block suffices for
the unweighted survival term of the three-block first-hit estimate. -/
theorem live_upper_of_cap {c u b : ℝ} (hb : 0 ≤ b) {t : ℕ} (ht : 0 < t)
    (hcap : ∀ i < t, u-c*i ≤ b) : live c u t 1 ≤ 2*b+(4/5)/√t := by
  have H := live_parameters c u 0 b t 1 (by simpa using hcap)
  apply H.trans (le_trans (homogeneous_live_upper hb ht) _)
  apply add_le_add (by linarith only [tanh_le_linear hb])
  apply mul_le_of_le_one_right (by positivity)
  apply exp_le_one_iff.mpr
  have := mul_nonneg (Nat.cast_nonneg (α:=ℝ) t) (sq_nonneg (tanh b))
  linarith

end CentralUnimodality.MarkedExcursion
