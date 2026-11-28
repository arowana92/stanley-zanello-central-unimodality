module

public import CentralUnimodality.ExactTrialConvolution

/-! Supremum bounds for the exact base convolution residual and its derivative. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem residual_budgets :
    rowBudget residualCandidate*10^17 ≤ 2*residualDen*145 ∧
    rowBudget (derivativeRow 0 residualCandidate)*10^16 ≤ 2*residualDen*128*3595 := by
  decide +kernel

theorem residualDen_pos : 0 < (residualDen:ℝ) := by
  exact_mod_cast (show 0 < residualDen by decide +kernel)

theorem base_hasDeriv (v : ℝ) : HasDerivAt baseResidual (deriv baseResidual v) v :=
  ((value_hasDerivAt residualCandidate v).const_mul (2^120/(residualDen:ℝ))).differentiableAt.hasDerivAt

theorem base_bounds {v : ℝ} (hv : v∈Set.Icc (0:ℝ) 256) :
    |baseResidual v|≤145/10^17 ∧ |deriv baseResidual v|≤3595/10^16 := by
  let d := derivativeRow 0 residualCandidate
  have D : deriv baseResidual v=(2^120/(residualDen:ℝ))*(-value d v/128) :=
    ((value_hasDerivAt residualCandidate v).const_mul _).deriv
  have hz := residualDen_pos
  have h₀ : (rowBudget residualCandidate:ℝ)*10^17 ≤ 2*residualDen*145 := by
    exact_mod_cast residual_budgets.1
  have h₁ : (rowBudget d:ℝ)*10^16 ≤ 2*residualDen*128*3595 := by
    exact_mod_cast residual_budgets.2
  rw [D,baseResidual,abs_mul,abs_mul,abs_of_pos (by positivity : 0<(2^120/(residualDen:ℝ))),
    abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<128)]
  constructor
  · rw [div_mul_eq_mul_div,div_le_iff₀ hz]
    linarith only [value_bound residualCandidate hv,h₀]
  · rw [div_mul_eq_mul_div,div_le_iff₀ hz]
    linarith only [value_bound d hv,h₁]

end CentralUnimodality.PolynomialTrial
