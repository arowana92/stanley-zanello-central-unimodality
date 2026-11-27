module

public import CentralUnimodality.PointMassPeak
import Mathlib.Analysis.Complex.ExponentialBounds

/-! A parity-lattice Gaussian bound from adjacent binomial ratios. A common
upper bound on their denominators makes the exponents telescope. -/
@[expose] public section

namespace CentralUnimodality

private theorem spatial_step (a d : ℕ) :
    pointMass (a+2) d = pointMass a (d+1)*(((d:ℝ)+1)/(a+d+2)) := by
  let j := a+2+2*d
  have h := Nat.choose_succ_right_eq j d
  rw [show j-d = a+d+2 by dsimp [j]; omega] at h
  have he : (j.choose (d+1):ℝ)*((d:ℝ)+1) = (j.choose d:ℝ)*((a:ℝ)+d+2) := by exact_mod_cast h
  rw [pointMass,pointMass,show a+2*(d+1) = j by dsimp [j]; omega]
  change (j.choose d:ℝ)/2^j = _
  field_simp
  linarith only [he]

private theorem gaussian_step (a d : ℕ) (T : ℝ) (hT : 2*((a:ℝ)+d+2) ≤ T) :
    pointMass (a+2) d ≤ pointMass a (d+1)*Real.exp (-(2*((a:ℝ)+1))/T) := by
  have hp : 0 < (a:ℝ)+d+2 := by positivity
  have hpos : 0 < T := lt_of_lt_of_le (by positivity) hT
  rw [spatial_step]
  apply mul_le_mul_of_nonneg_left _ (pointMass_pos ..).le
  have hr : ((d:ℝ)+1)/(a+d+2) = 1 - (2*(a+1))/(2*(a+d+2)) := by field_simp; ring
  rw [hr]
  have hh := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2*((a:ℝ)+1))
    (by positivity : 0 < 2*((a:ℝ)+d+2)) hT
  rw [neg_div]
  linarith only [hh,Real.add_one_le_exp (-(2*((a:ℝ)+1)/T))]

theorem pointMass_gaussian (p k d : ℕ) (T : ℝ)
    (hT : 2*((p:ℝ)+2*k+d) ≤ T) :
    pointMass (p+2*k) d ≤ pointMass p (d+k)*Real.exp (-(((p:ℝ)+2*k)^2-p^2)/(2*T)) := by
  induction k generalizing d with
  | zero => simp
  | succ k ih =>
    push_cast at hT ⊢
    have h := gaussian_step (p+2*k) d T (by push_cast; linarith only [hT])
    have ha := ih (d+1) (by push_cast; linarith only [hT])
    rw [show p+2*(k+1) = p+2*k+2 by omega,show d+(k+1) = d+1+k by omega]
    apply h.trans
    apply (mul_le_mul_of_nonneg_right ha (Real.exp_pos _).le).trans_eq
    rw [mul_assoc,← Real.exp_add]
    congr 2
    push_cast
    ring

theorem survival_sq_three (n : ℕ) : (3*(n:ℝ)+1)*(survival n)^2 ≤ 1 := by
  induction n with
  | zero => norm_num [survival]
  | succ n ih =>
    rw [survival_succ,Nat.cast_succ,mul_pow,div_pow,← mul_div_assoc,← mul_div_assoc,div_le_one (by positivity)]
    have he : (3*((n:ℝ)+1)+1)*(2*n+1)^2 ≤ (3*n+1)*(2*(n+1))^2 := by nlinarith only [Nat.cast_nonneg (α := ℝ) n]
    have h₁ := mul_le_mul_of_nonneg_right he (sq_nonneg (survival n))
    have h₂ := mul_le_mul_of_nonneg_right ih (sq_nonneg (2*((n:ℝ)+1)))
    linarith only [h₁,h₂]

private theorem exp_reserve : Real.exp (-(63/64):ℝ) < 3/8 := by
  have hx : (63/64:ℝ) ≤ Real.exp (-(1/64):ℝ) := by linarith only [Real.add_one_le_exp (-(1/64):ℝ)]
  have he := mul_le_mul (le_of_lt Real.exp_one_gt_d9) hx (by norm_num) (Real.exp_pos _).le
  rw [← Real.exp_add] at he
  rw [Real.exp_neg,inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 3/8)]
  norm_num at he ⊢
  linarith only [he]

theorem point_half_large {a : ℕ} (ha : 64 ≤ a) :
    (a:ℝ)*pointMass a (a.choose 2) ≤ 1/2 := by
  let k := a/2
  let p := a%2
  let d := a.choose 2
  let j := a^2
  let N := (j+1)/2
  have hp : p ≤ 1 := by dsimp [p]; omega
  have hk : p+2*k = a := by dsimp [p,k]; omega
  have ht : a+2*d = j := peak_time a
  have hmid : d+k = j/2 := by omega
  have hmid' : p+2*(d+k) = j := by omega
  have hc : pointMass p (d+k) = survival N := by rw [pointMass,hmid',hmid,ballot_survival]
  have hT : 0 < (j:ℝ)+a := by
    have ha' : (0:ℝ) < a := by exact_mod_cast (by omega : 0 < a)
    positivity
  have hstep := pointMass_gaussian p k d ((j:ℝ)+a) (by exact_mod_cast (by omega : 2*(p+2*k+d) ≤ j+a))
  rw [hk,hc] at hstep
  have hk' : (p:ℝ)+2*k = a := by exact_mod_cast hk
  rw [hk'] at hstep
  have hs : (p:ℝ)^2 ≤ 1 := by rcases (by omega : p = 0 ∨ p = 1) with h|h <;> norm_num [h]
  have he : -((a:ℝ)^2-p^2)/(2*(j+a)) ≤ -(63/128) := by
    apply (div_le_iff₀ (by positivity)).mpr
    have h := mul_nonneg (sub_nonneg.mpr (by exact_mod_cast ha) : 0 ≤ (a:ℝ)-64)
      (by positivity : 0 ≤ (a:ℝ)+1)
    dsimp [j] at *
    push_cast
    nlinarith only [hs,h]
  have hm := hstep.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (survival_pos _).le)
  have hN : j ≤ 2*N := by dsimp [N]; omega
  have hn : (a:ℝ)^2 ≤ 2*(N:ℝ) := by exact_mod_cast hN
  have hsur := survival_sq_three N
  have hx : ((a:ℝ)*survival N)^2 ≤ 2/3 := by
    nlinarith only [hsur,mul_le_mul_of_nonneg_right hn (sq_nonneg (survival N)),sq_nonneg (survival N)]
  have hf := (sq_le_sq₀ (pointMass_pos ..).le (mul_nonneg (survival_pos _).le (Real.exp_pos _).le)).mpr hm
  have hh := mul_le_mul_of_nonneg_left hf (sq_nonneg (a:ℝ))
  have hpow : (Real.exp (-(63/128):ℝ))^2 = Real.exp (-(63/64):ℝ) := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [mul_pow,hpow] at hh
  have hb := mul_le_mul hx exp_reserve.le (Real.exp_pos _).le (by norm_num)
  apply (sq_le_sq₀ (mul_nonneg (Nat.cast_nonneg _) (pointMass_pos ..).le) (by norm_num : (0:ℝ) ≤ 1/2)).mp
  nlinarith only [hh,hb]

end CentralUnimodality
