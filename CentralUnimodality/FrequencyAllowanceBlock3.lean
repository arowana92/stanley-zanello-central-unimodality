module

public import CentralUnimodality.FrequencyChargeData

/-! Verify the retained allowances of cells 249 through 287. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option Elab.async false

check_bool_range allowance_block_3 allowanceCheck 249 39

end CentralUnimodality.PolynomialTrial
