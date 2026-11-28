module

public import CentralUnimodality.IntegerCellChecks

/-! Check all neighboring split pairs for cells 204 through 248. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option Elab.async false

check_bool_range maxima_block_2 cellMaxTest 204 45

end CentralUnimodality.PolynomialTrial
