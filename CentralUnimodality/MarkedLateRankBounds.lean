module

public import CentralUnimodality.MarkedRankBudget
public import CentralUnimodality.ReflectedSuffixRuin

/-! The two-harmonic Fourier budget, the height reflection and the discounted
prefix survival apply together to the rank-resolved late crossing event. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real BinArithmetic FrequencyGrid

noncomputable def reflectedLateFactor (b : ℝ) (n : ℕ) : ℝ := min 1 ((21/25)/(b*√n))
noncomputable def liveCap (U : ℝ) (L : ℕ) : ℝ :=
  2*tanh U+(4/5)/√L*exp (-((L:ℝ)*(tanh U)^2/2))

theorem marked_late_rank_bound {c z b U σ : ℝ} {m : ℕ} (hm : 4096≤m)
    (hc : 0≤c) (hz : 0≤z) (hb : 0<b) (hb' : b≤6/25) (hU : 0≤U) (hU' : U≤6/25)
    (hcap : (c+z)*m-b≤U) (hcut : b*m≤(tanh (c*m)/m+z)*prefixLabels m (timeCut m (37/40)))
    (hσ : 0≤σ) (hσ' : σ≤(259/1000)*sizeScale m) (r : Fin 3) (j : ℤ) :
    let L := timeCut m (3/40)
    let T := timeCut m (37/40)
    σ^(r.val+1)*rankChange c z (meanRank c m) m*
      |rankDifference r j (eventSiteMass (c+z) m (lateHitEvent m T))| ≤
      exp (z^2*labelSquares m/2-m*b^2/2)*reflectedLateFactor b (m-T)*liveCap U L*(markedLimit r:ℝ) := by
  let v := c+z
  let L := timeCut m (3/40)
  let T := timeCut m (37/40)
  let Q := reflectedLateFactor b (m-T)
  have hv : 0≤v := add_nonneg hc hz
  have hQ : 0≤Q := le_min (by norm_num) (by positivity)
  have hM : (4096:ℝ)≤m := by exact_mod_cast hm
  have hT : (T:ℝ)<37/40*m+1 := by simpa [T,timeCut] using Nat.ceil_lt_add_one (by positivity : 0≤(37/40:ℝ)*m)
  have hL : (3/40:ℝ)*m≤L := by simpa [L,timeCut] using Nat.le_ceil ((3/40:ℝ)*m)
  have hTm : T≤m := by exact_mod_cast (show (T:ℝ)≤m by linarith only [hT,hM])
  have hLp : 0<L := by exact_mod_cast (show (0:ℝ)<L by linarith only [hL,hM])
  have hn : 255≤m-T := by
    have he : (255:ℝ)+T≤m := by linarith only [hT,hM]
    exact Nat.le_sub_of_add_le (by exact_mod_cast he)
  have hr (h : ℕ) : ruin v (m-T) h ≤ exp (-b*h)*(exp ((m-T:ℕ)*b^2/2)*Q) := by
    rw [← mul_assoc,← exp_add]
    by_cases hf : 1≤(21/25)/(b*√(m-T:ℕ))
    · rw [show Q=1 from min_eq_left hf,mul_one]
      apply (suffix_ruin hv hb.le (m-T) h).trans (exp_le_exp.mpr _)
      linarith only [hb]
    · rw [show Q=(21/25)/(b*√(m-T:ℕ)) from min_eq_right (le_of_not_ge hf)]
      exact reflected_suffix_ruin hv hb hb' hn h
  have C := mul_nonneg (exp_pos (z^2*labelSquares m/2-m*b^2/2)).le hQ
  have H := marked_rank_budget_of_row hm hv hb' hU' hcap (rankChange_pos c z (meanRank c m) m).le C
    (fun θ => late_rank_character_of_ruin hc hQ hb.le θ (by omega) hTm hcut hr) hσ hσ' r j
  have Hpre := (live_parameters v (v*m-b) 0 U L 1 (by
    intro i _; simp only [zero_mul,sub_zero]
    linarith only [hcap,mul_nonneg hv (Nat.cast_nonneg (α:=ℝ) i)])).trans (homogeneous_live_upper hU hLp)
  apply H.trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hpre C) (by fin_cases r <;> norm_num [markedLimit])

end CentralUnimodality.MarkedExcursion
