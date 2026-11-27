module

public import CentralUnimodality.FirstReturnMass
public import CentralUnimodality.FourierResidual

/-! The common survival probability at lengths 2n and 2n+1, the mass of
the first return at length 2n, and elementary bounds for the normalizer. -/
@[expose] public section

namespace CentralUnimodality

noncomputable def survival (n : ℕ) : ℝ := n.centralBinom / (4:ℝ)^n

theorem survival_pos (n : ℕ) : 0 < survival n := by
  unfold survival
  exact div_pos (by exact_mod_cast Nat.centralBinom_pos n) (by positivity)

theorem survival_even (n : ℕ) :
    (strictWords (2*n)).card / (2:ℝ)^(2*n) = survival n := by
  rw [card_strictWords_even, pow_mul]
  norm_num [survival, Nat.centralBinom]

theorem survival_odd (n : ℕ) :
    (strictWords (2*n+1)).card / (2:ℝ)^(2*n+1) = survival n := by
  rw [card_strictWords_odd, pow_succ, pow_mul, Nat.cast_mul, Nat.cast_ofNat]
  change 2 * (n.centralBinom:ℝ) / ((2^2:ℝ)^n*2) = n.centralBinom / (4:ℝ)^n
  norm_num
  ring

theorem survival_succ (n : ℕ) :
    survival (n+1) = survival n * ((2*(n:ℝ)+1)/(2*((n:ℝ)+1))) := by
  have h : ((n:ℝ)+1) * (n+1).centralBinom = 2*(2*(n:ℝ)+1)*n.centralBinom := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  unfold survival
  rw [pow_succ]
  field_simp
  linarith only [h]

theorem firstReturn_probability (n : ℕ) :
    (firstReturns (2*(n+1))).card / (2:ℝ)^(2*(n+1)) = survival (n+1) / (2*n+1) := by
  rw [pow_mul]
  have h : (2*(n:ℝ)+1) * (firstReturns (2*(n+1))).card = (n+1).centralBinom := by
    exact_mod_cast card_firstReturns_even n
  unfold survival
  norm_num
  rw [← h]
  field_simp

theorem survival_sq_upper (n : ℕ) : ((n:ℝ)+1)*(survival n)^2 ≤ 1 := by
  induction n with
  | zero => simp [survival]
  | succ n ih =>
    rw [survival_succ, Nat.cast_succ, mul_pow, div_pow]
    have hd : 0 < (2*((n:ℝ)+1))^2 := by positivity
    have hc : ((n:ℝ)+1+1)*(2*n+1)^2 ≤ (n+1)*(2*(n+1))^2 := by
      nlinarith only [show 0 ≤ (n:ℝ) by positivity]
    rw [← mul_div_assoc, ← mul_div_assoc, div_le_one hd]
    have h₁ := mul_le_mul_of_nonneg_right hc (sq_nonneg (survival n))
    have h₂ := mul_le_mul_of_nonneg_right ih hd.le
    linarith only [h₁, h₂]

theorem survival_sq_lower {n : ℕ} (hn : 1 ≤ n) : 1 ≤ 4*(n:ℝ)*(survival n)^2 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [survival, Nat.centralBinom, Nat.choose]
  | succ n _ ih =>
    rw [survival_succ, Nat.cast_succ, mul_pow, div_pow, ← mul_div_assoc, ← mul_div_assoc]
    have hd : 0 < (2*((n:ℝ)+1))^2 := by positivity
    apply (le_div_iff₀ hd).mpr
    have h₁ := mul_le_mul_of_nonneg_right ih hd.le
    have hc : 4*(n:ℝ)*(2*(n+1))^2 ≤ 4*(n+1)*(2*n+1)^2 := by
      nlinarith only [show 0 ≤ (n:ℝ) by positivity]
    have h₂ := mul_le_mul_of_nonneg_right hc (sq_nonneg (survival n))
    linarith only [h₁,h₂]

end CentralUnimodality
