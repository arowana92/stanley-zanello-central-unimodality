module

public import CentralUnimodality.GaussianLogError
public import CentralUnimodality.ZeroFrequencySymbols

/-! Absolute Gaussian errors in the actual free and normalized bridge
coefficients, including the zero-frequency coefficient. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit
open Real PowerSeries

private theorem exp_dist_ordered {x y : ℝ} (h : x≤y) (hy : y≤0) :
    exp y-exp x≤y-x := by
  have ee : exp y≤1 := exp_le_one_iff.mpr hy
  have first := add_one_le_exp (x-y)
  have second := mul_le_mul_of_nonneg_left (by linarith only [first] : 1-exp (x-y)≤y-x) (exp_nonneg y)
  have third := mul_le_mul_of_nonneg_right ee (sub_nonneg.mpr h)
  rw [mul_sub,mul_one,← exp_add,show y+(x-y)=x by ring] at second
  linarith only [second,third]

theorem exp_dist_nonpos {x y : ℝ} (hx : x≤0) (hy : y≤0) :
    |exp x-exp y|≤|x-y| := by
  rcases le_total x y with h|h
  · rw [abs_of_nonpos (sub_nonpos.mpr (exp_le_exp.mpr h)),abs_of_nonpos (sub_nonpos.mpr h)]
    linarith only [exp_dist_ordered h hy]
  · rw [abs_of_nonneg (sub_nonneg.mpr (exp_le_exp.mpr h)),abs_of_nonneg (sub_nonneg.mpr h)]
    exact exp_dist_ordered h hx

theorem free_gaussian {ω : ℝ} {t : ℕ} (ha : |ω| * t≤1) :
    ‖coeff t (fairSeries (areaCharacter ω) words)-(exp (-freeExponent ω t):ℂ)‖ ≤
      3/4*ω^4*fourthSum t := by
  rw [freeSymbol_log ω ha,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have bound := norm_coeff_fairSeries _ (fun a => (norm_areaCharacter ω a).le) words t
  rw [freeSymbol_log ω ha,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (exp_pos _),card_words] at bound
  push_cast at bound
  rw [div_self (by positivity)] at bound
  have gauss : 0≤freeExponent ω t := by unfold freeExponent; positivity
  apply (exp_dist_nonpos (exp_le_one_iff.mp bound) (neg_nonpos.mpr gauss)).trans
  simpa using freeLog_error ω ha

theorem bridge_log_all {ω : ℝ} {j : ℕ} (ha : |ω| * (2*j:ℝ)≤1) :
    coeff (2*j) (fairSeries (areaCharacter ω) bridges) =
      ((survival j*exp (bridgeLog ω j):ℝ):ℂ) := by
  by_cases h : ω=0
  · subst ω; simp [fair_bridge_zero_frequency,bridgeLog]
  · exact bridgeSymbol_log h ha

private theorem bridge_mass (j : ℕ) : (bridges (2*j)).card/(2:ℝ)^(2*j)=survival j := by
  apply Complex.ofReal_injective
  push_cast
  rw [← fair_bridge_zero_frequency,coeff_walkSeries]
  simp [areaCharacter,div_eq_inv_mul]

theorem bridge_gaussian {ω : ℝ} {j : ℕ} (ha : |ω| * (2*j:ℝ)≤1) :
    ‖coeff (2*j) (fairSeries (areaCharacter ω) bridges)/(survival j:ℂ)-
      (exp (-bridgeExponent ω j):ℂ)‖ ≤ 8/5*ω^4*fourthSum j := by
  have nonzero : (survival j:ℂ)≠0 := by exact_mod_cast (survival_pos j).ne'
  have exactValue : coeff (2*j) (fairSeries (areaCharacter ω) bridges)/(survival j:ℂ)=
      (exp (bridgeLog ω j):ℂ) := by
    rw [bridge_log_all ha,Complex.ofReal_mul]; field_simp
  rw [exactValue,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have bound := norm_coeff_fairSeries _ (fun a => (norm_areaCharacter ω a).le) bridges (2*j)
  rw [bridge_mass,bridge_log_all ha,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (mul_pos (survival_pos j) (exp_pos _))] at bound
  have blog : bridgeLog ω j≤0 := exp_le_one_iff.mp
    ((mul_le_mul_iff_of_pos_left (survival_pos j)).mp (by simpa only [mul_one] using bound))
  have gauss : 0≤bridgeExponent ω j := by unfold bridgeExponent; positivity
  apply (exp_dist_nonpos blog (neg_nonpos.mpr gauss)).trans
  simpa using bridgeLog_error ω ha

end CentralUnimodality.ReturnSplit
