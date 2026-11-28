module

public import CentralUnimodality.IntegerCellChecks

/-! Check all neighboring split pairs for cells 249 through 287. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option Elab.async false

check_bool_range maxima_block_3 cellMaxTest 249 39

end CentralUnimodality.PolynomialTrial
