module

public import CentralUnimodality.ScaledQuarticInputs
public import CentralUnimodality.LatticeCubicInputs
import CentralUnimodality.ScaledPrefixSurvival

/-! Local second-order errors for the actual discrete symbols after
removing the first smooth quartic correction. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit
open Real PowerSeries

private theorem exponential_transfer {w a b L τ : ℝ} (ht : 0≤τ*b)
    (lo : 0≤ -w-a-τ*b) (hi : -w-a-τ*b≤τ^2*L) :
    |exp w-exp (-a)*(1-τ*b)|≤τ^2*(exp (-a)*L+exp (-a)*b^2/2) := by
  let d := -w-a-τ*b
  have eq : w= -a+(-(τ*b)-d) := by dsimp only [d]; ring
  have lower := add_one_le_exp (-(τ*b)-d)
  have upper := (exp_le_exp.mpr (show -(τ*b)-d≤ -(τ*b) by linarith only [lo])).trans
    (MarkedExcursion.negative_exp_quadratic ht)
  rw [eq,exp_add,← mul_sub,abs_mul,abs_of_pos (exp_pos _)]
  have noise : |exp (-(τ*b)-d)-(1-τ*b)|≤τ^2*L+(τ*b)^2/2 := by
    rw [abs_le]
    constructor <;> linarith only [lower,upper,(show d≤τ^2*L from hi),(show 0≤d from lo),sq_nonneg (τ*b)]
  exact (mul_le_mul_of_nonneg_left noise (exp_pos _).le).trans_eq (by ring)

theorem free_corrected_symbol {ω τ : ℝ} {j σ : ℕ} (hs : σ≤1) (hτ : 0≤τ) (hω : ω^2=τ^3/32)
    (ha : |ω| *(2*j+σ)≤9/8) (v : ℝ) (hv : v=j*τ) :
    ‖coeff (2*j+σ) (fairSeries (areaCharacter ω) words)-
      (freeCurve v*(1-τ*freeLogCorrection σ v):ℝ)‖≤
    τ^2*(freeCurve v*freeLogRemainder v τ+freeCurve v*(freeLogCorrection σ v)^2/2) := by
  rw [freeSymbol_log_wide ω (by push_cast; exact ha),← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have h := free_log_scaled hs hτ hω ha v hv
  have nn : 0≤τ*freeLogCorrection σ v := by rw [hv]; unfold freeLogCorrection; positivity
  exact exponential_transfer nn h.1 h.2

theorem bridge_corrected_symbol {ω τ : ℝ} {j : ℕ} (hτ : 0≤τ) (hω : ω^2=τ^3/32)
    (ha : |ω| *(2*j)≤9/8) (v : ℝ) (hv : v=j*τ) :
    ‖coeff (2*j) (fairSeries (areaCharacter ω) bridges)/(survival j:ℂ)-
      (bridgeCurve v*(1-τ*bridgeLogCorrection v):ℝ)‖≤
    τ^2*(bridgeCurve v*bridgeLogRemainder v τ+bridgeCurve v*(bridgeLogCorrection v)^2/2) := by
  have exactValue : coeff (2*j) (fairSeries (areaCharacter ω) bridges) =
      ((survival j*exp (bridgeLog ω j):ℝ):ℂ) := by
    by_cases hz : ω=0
    · subst ω; simp [fair_bridge_zero_frequency,bridgeLog]
    · exact bridgeSymbol_log_wide hz ha
  rw [exactValue,Complex.ofReal_mul,mul_div_cancel_left₀ _ (by exact_mod_cast (survival_pos j).ne' : (survival j:ℂ)≠0),
    ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have h := bridge_log_scaled hτ hω ha v hv
  have nn : 0≤τ*bridgeLogCorrection v := by rw [hv]; unfold bridgeLogCorrection; positivity
  exact exponential_transfer nn h.1 h.2

end CentralUnimodality.ReturnSplit
