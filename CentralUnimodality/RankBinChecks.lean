module

public import CentralUnimodality.RankBinNumbers

/-! Finite rational comparison at each bin. These declarations concern
the explicit arithmetic bounds; their application to changing staircase
lengths also needs the analytic bounds for every parameter in a bin. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem growth_bin_checks (i : Fin 9) : checkSigns false i=true := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem curvature_bin_checks (i : Fin 7) : checkSigns true i=true := by
  fin_cases i <;> decide +kernel

end CentralUnimodality.MarkedExcursion.BinArithmetic
