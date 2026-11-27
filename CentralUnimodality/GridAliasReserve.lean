module

public import CentralUnimodality.AliasTail
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! The periodization reserve for first and second differences on the
finite central Fourier windows, with exact rational constants. -/
@[expose] public section

namespace CentralUnimodality

private theorem exp_neg_110 : Real.exp (-110) < (10:ℝ)⁻¹^43 := by
  have he : (2.5:ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.5) he 110
  have h : (10:ℝ)^43 < Real.exp 110 := by
    rw [← Real.exp_nat_mul] at hp
    simp only [Nat.cast_ofNat,mul_one] at hp
    exact lt_of_lt_of_le (by norm_num : (10:ℝ)^43 < 2.5^110) hp
  rw [Real.exp_neg,inv_pow]
  exact inv_lt_inv₀ (Real.exp_pos _) (by positivity) |>.mpr h

theorem scaled_tail_reserve {n δ r : ℕ} (hδ : δ ≤ 1) (hN : 2049 ≤ n+δ)
    (hmax : n+δ ≤ 300000) (hr : r ≤ 2) :
    (2*Witness.cellScale (n+δ))^(r+1) *
      ((corankTail n δ (4.3*Witness.cellScale (n+δ)):ℝ)/((2*n+δ).choose n:ℝ)) <
      1/10^12 := by
  let N := n+δ
  let S := Witness.cellScale N
  let W : ℝ := squareWeights (2*n+δ)
  have hpos : 0 < S := Witness.cellScale_pos (by omega : 0 < N)
  have hm : 0 < 2*n+δ := by omega
  have hw : 0 < W := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    dsimp [W]
    rw [hk,squareWeights_succ]
    positivity
  have he : -2*(4.3*S)^2/W ≤ -110 := by
    apply (div_le_iff₀ hw).mpr
    have ha := gaussian_grid_rate (N := N) (by omega : 2*n+δ ≤ 2*N) (by omega)
    change (599/100:ℝ)*W ≤ 2*S^2 at ha
    nlinarith only [ha,hw.le]
  have hN' : (N:ℝ) ≤ 300000 := by exact_mod_cast hmax
  have hroot : Real.sqrt (2*(N:ℝ)) ≤ 800 := Real.sqrt_le_iff.mpr ⟨by norm_num,by linarith⟩
  have hnroot : Real.sqrt (N:ℝ) ≤ 550 := Real.sqrt_le_iff.mpr ⟨by norm_num,by linarith⟩
  have hs : 2*S ≤ 10^9 := by
    have hh := mul_le_mul (by linarith : 2*(N:ℝ) ≤ 600000) hroot (Real.sqrt_nonneg _) (by norm_num)
    change 2*(2*(N:ℝ)*Real.sqrt (2*N)) ≤ _
    linarith only [hh]
  have hpow : (2*S)^(r+1) ≤ ((10:ℝ)^9)^3 :=
    (pow_le_pow_left₀ (by positivity) hs _).trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have hprob := normalized_corankTail hδ hm (by positivity : 0 ≤ 4.3*S)
  have hbound : ((corankTail n δ (4.3*S):ℝ)/((2*n+δ).choose n:ℝ)) ≤ 1100*(10:ℝ)⁻¹^43 := by
    apply hprob.trans
    apply mul_le_mul _ ((Real.exp_le_exp.mpr he).trans exp_neg_110.le) (Real.exp_pos _).le (by norm_num)
    change 2*Real.sqrt ((n:ℝ)+δ) ≤ 1100
    simpa [N] using (show 2*Real.sqrt (N:ℝ) ≤ 1100 by linarith)
  exact lt_of_le_of_lt (mul_le_mul hpow hbound (by positivity) (by positivity)) (by norm_num)

/-- Applies at each site or neighboring site satisfying the center bound.
The power of two includes the absolute multipliers of the differences. -/
theorem grid_alias_reserve {n δ r Q j : ℕ} (hδ : δ ≤ 1) (hN : 2049 ≤ n+δ)
    (hmax : n+δ ≤ 300000) (hr : r ≤ 2) (hj : j ≤ n*(n+δ))
    (hgrid : 5*Witness.cellScale (n+δ) ≤ Q)
    (hsite : ((n*(n+δ)-j:ℕ):ℝ)+(3*n+2*δ+1)/2 ≤ 0.63*Witness.cellScale (n+δ)) :
    (2*Witness.cellScale (n+δ))^(r+1) *
      (((periodicCount n δ Q j:ℝ)-rankCount (2*n+δ) j)/((2*n+δ).choose n:ℝ)) < 1/10^12 := by
  let N := n+δ
  let S := Witness.cellScale N
  have hn : (2049:ℝ) ≤ N := by exact_mod_cast hN
  have hs : 0 < S := Witness.cellScale_pos (by omega : 0 < N)
  have h64 : (64:ℝ) ≤ Real.sqrt (2*(N:ℝ)) := by
    apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by positivity)]
    linarith
  have hd : (3*(n:ℝ)+2*δ+1)/2 ≤ 0.012*S := by
    have h := mul_le_mul_of_nonneg_left h64 (by positivity : 0 ≤ 2*(N:ℝ))
    change _ ≤ 0.012*(2*(N:ℝ)*Real.sqrt (2*N))
    have hN' : (N:ℝ) = (n:ℝ)+δ := by simp [N]
    linarith [Nat.cast_nonneg (α := ℝ) δ]
  have hcut : 2*(n*(n+δ)-j)+(3*n+2*δ+1) < Q := by
    change _ ≤ 0.63*S at hsite
    change 5*S ≤ _ at hgrid
    exact_mod_cast (show 2*((n*(n+δ)-j:ℕ):ℝ)+(3*n+2*δ+1) < Q by linarith only [hsite,hgrid,hs])
  have he := excess_le_tail hj hcut (x := 4.3*S) (by
    change _ ≤ 0.63*S at hsite
    change 5*S ≤ _ at hgrid
    linarith only [hd,hsite,hgrid,hs])
  have he' : (periodicCount n δ Q j:ℝ) ≤ (rankCount (2*n+δ) j:ℝ)+(corankTail n δ (4.3*S):ℝ) := by
    exact_mod_cast he
  apply lt_of_le_of_lt _ (scaled_tail_reserve hδ hN hmax hr)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact div_le_div_of_nonneg_right (by linarith only [he']) (by positivity)

end CentralUnimodality
