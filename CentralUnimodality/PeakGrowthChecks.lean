module

public import CentralUnimodality.PeakGrowthNumbers

/-! Kernel checks of the dimensionless budget for every refined growth
bin, with the same positive rational slack in all seven bins. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic.Peak

def binOK (i : Fin 7) : Prop :=
  let B := tabulated i
  goodPrefix B ∧ lateOK (lateBin i)=true ∧
    (∀ j : Fin (timeBins i), timeOK B (timeBin i j)=true) ∧
    earlyTotal i + lateTotal i + 22/1000 < prefixMargin B

instance (i : Fin 7) : Decidable (binOK i) := by unfold binOK; infer_instance

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 500000 in
theorem checked_growth_budgets (i : Fin 7) : binOK i := by
  fin_cases i <;> decide +kernel

end CentralUnimodality.MarkedExcursion.BinArithmetic.Peak
