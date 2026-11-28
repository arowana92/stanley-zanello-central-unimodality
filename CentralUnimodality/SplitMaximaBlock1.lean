module

public import CentralUnimodality.IntegerCellChecks

/-! Check all neighboring split pairs for cells 144 through 203. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option Elab.async false

check_bool_range maxima_block_1 cellMaxTest 144 60

end CentralUnimodality.PolynomialTrial
