module

public import CentralUnimodality.SpatialInnerTail
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The part of the true spatial integral outside the small-frequency
range, through its exact lattice period. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

open Real Set intervalIntegral Witness

theorem long_scale_from_5000 {N : ℕ} (hn : 5000≤N) :
    4096≤0.008*cellScale N ∧ 0.008*cellScale N≤π*cellScale N ∧ π*cellScale N≤16*(N:ℝ)^2 := by
  have big : (5000:ℝ)≤N := by exact_mod_cast hn
  have one : (1:ℝ)≤2*N := by linarith only [big]
  have lo : (64:ℝ)≤sqrt (2*N) := Real.le_sqrt_of_sq_le (by linarith only [big])
  have up : sqrt (2*N)≤2*N := (sqrt_le_left (by positivity)).mpr
    (by nlinarith only [one,mul_nonneg (sub_nonneg.mpr one) (show 0≤2*(N:ℝ) by positivity)])
  have ns : 0≤(2:ℝ)*N := by positivity
  have h₀ := mul_le_mul_of_nonneg_left lo ns
  have h₁ := mul_le_mul_of_nonneg_left up ns
  change 4096≤0.008*(2*(N:ℝ)*sqrt (2*N)) ∧ _ ∧ _
  refine ⟨by linarith only [h₀,big],mul_le_mul_of_nonneg_right (by linarith only [pi_gt_three])
    (cellScale_pos (by omega)).le,?_⟩
  unfold cellScale
  exact (mul_le_mul pi_lt_four.le h₁ (by positivity) (by norm_num)).trans_eq (by ring)

theorem long_scale_from_150000 {N : ℕ} (hn : 150000≤N) :
    4096≤0.008*cellScale N ∧ 0.008*cellScale N≤π*cellScale N ∧ π*cellScale N≤16*(N:ℝ)^2 :=
  long_scale_from_5000 (by omega)

theorem long_scale_from_300000 {N : ℕ} (hn : 300000≤N) :
    4096≤0.008*cellScale N ∧ 0.008*cellScale N≤π*cellScale N ∧ π*cellScale N≤16*(N:ℝ)^2 :=
  long_scale_from_5000 (by omega)

theorem long_scale {N : ℕ} (hn : 10^54≤N) :
    4096≤0.008*cellScale N ∧ 0.008*cellScale N≤π*cellScale N ∧ π*cellScale N≤16*(N:ℝ)^2 :=
  long_scale_from_5000 (by omega)

private theorem outer_budget {N U T : ℝ} (big : 5000≤N) (hT : 0≤T) (hu : T≤U)
    (cap : U≤16*N^2) : (144/exp (N/67)*U^2)*(U-T)≤1/1000 := by
  have nn : 0≤N := by linarith only [big]
  have u0 := hT.trans hu
  have s := mul_le_mul_of_nonneg_left (sub_le_self U hT) (by positivity : 0≤144/exp (N/67)*U^2)
  apply s.trans
  rw [show 144/exp (N/67)*U^2*U=144*U^3/exp (N/67) by ring,div_le_iff₀ (exp_pos _)]
  have e := pow_div_factorial_le_exp (x:=N/67) (show 0≤N/67 by positivity) 70
  have power : (5000:ℝ)^64≤N^64 := pow_le_pow_left₀ (by norm_num) big 64
  have coeff : 144*16^3≤(1/1000:ℝ)*N^64/(67^70*(Nat.factorial 70:ℝ)) := by
    norm_num [Nat.factorial]; linarith only [power]
  have total := mul_le_mul_of_nonneg_right coeff (pow_nonneg nn 6)
  have c := pow_le_pow_left₀ u0 cap 3
  norm_num [Nat.factorial] at e
  linarith only [e,total,c]

theorem outer_rank_tail_from_5000 {n δ r : ℕ} (hs : δ≤1) (hn : 5000≤n+δ) (hr : r≤2) (x : ℝ) :
    |∫ ξ in 0.008*cellScale (n+δ)..π*cellScale (n+δ), rankKernel n δ r x ξ|≤1/1000 := by
  let N := n+δ
  let S := cellScale N
  let T := 0.008*S
  let U := π*S
  have pos : 0<S := cellScale_pos (by dsimp [N]; omega)
  have big : (5000:ℝ)≤N := by exact_mod_cast hn
  have ⟨hT,ord,hU⟩ := long_scale_from_5000 hn
  have one : 1≤U := by dsimp [U,S,N]; linarith only [hT,ord]
  have e2 : exp 2≤9 := by
    have h := pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_three.le 2
    rw [← exp_nat_mul] at h; norm_num at h; exact h
  have point (ξ : ℝ) (hξ : ξ∈uIoc T U) :
      ‖rankKernel n δ r x ξ‖≤144/exp ((N:ℝ)/67)*U^2 := by
    rw [uIoc_of_le ord] at hξ
    have ht : 0.008≤ξ/S := (le_div_iff₀ pos).mpr hξ.1.le
    have hp : ξ/S≤π := (div_le_iff₀ pos).mpr hξ.2
    have A := (amplitude_le_magnitude n δ _).trans
      (signed_outer_frequency hs (by omega) (by decide) (by norm_num) (outer_blocks_008 ht hp))
    have expArg : 0.0078*216-0.0078*(63/64)*(2*(n:ℝ)+δ) ≤ 2-N/67 := by
      dsimp only [N]; push_cast
      have d : (δ:ℝ)≤1 := by exact_mod_cast hs
      linarith only [Nat.cast_nonneg (α:=ℝ) n,d]
    have decay := exp_le_exp.mpr expArg
    rw [exp_sub 2] at decay
    have A' : |signedAmplitude n δ (ξ/S)|≤144/exp ((N:ℝ)/67) := by
      push_cast at A
      apply A.trans
      apply (mul_le_mul_of_nonneg_left (decay.trans (div_le_div_of_nonneg_right e2 (exp_pos _).le))
        (by norm_num : (0:ℝ)≤16)).trans_eq
      ring
    have nn : 0≤ξ := by have := hξ.1.le; change 0.008*S≤ξ at this; linarith only [this,pos]
    have powers := (pow_le_pow_left₀ nn hξ.2 r).trans (pow_le_pow_right₀ one hr)
    rw [Real.norm_eq_abs,rankKernel,abs_mul,abs_mul,abs_pow,abs_of_nonneg nn]
    apply (mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (pow_nonneg nn _)) (abs_cos_le_one _)).trans
    exact mul_le_mul A' powers (pow_nonneg nn _) (by positivity)
  have bound := norm_integral_le_of_norm_le_const point
  rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr ord)] at bound
  exact bound.trans (outer_budget big (show 0≤T by dsimp [T]; positivity) ord hU)

theorem outer_rank_tail_from_150000 {n δ r : ℕ} (hs : δ≤1) (hn : 150000≤n+δ) (hr : r≤2) (x : ℝ) :
    |∫ ξ in 0.008*cellScale (n+δ)..π*cellScale (n+δ), rankKernel n δ r x ξ|≤1/1000 :=
  outer_rank_tail_from_5000 hs (by omega) hr x

theorem outer_rank_tail_from_300000 {n δ r : ℕ} (hs : δ≤1) (hn : 300000≤n+δ) (hr : r≤2) (x : ℝ) :
    |∫ ξ in 0.008*cellScale (n+δ)..π*cellScale (n+δ), rankKernel n δ r x ξ|≤1/1000 :=
  outer_rank_tail_from_5000 hs (by omega) hr x

theorem outer_rank_tail {n δ r : ℕ} (hs : δ≤1) (hn : 10^54≤n+δ) (hr : r≤2) (x : ℝ) :
    |∫ ξ in 0.008*cellScale (n+δ)..π*cellScale (n+δ), rankKernel n δ r x ξ|≤1/1000 :=
  outer_rank_tail_from_5000 hs (by omega) hr x

end CentralUnimodality.PolynomialTrial
