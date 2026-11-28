module

public import CentralUnimodality.FrequencyChargeData

/-! Verify the retained allowances of cells 144 through 203. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option Elab.async false

check_bool_range allowance_block_1 allowanceCheck 144 60

end CentralUnimodality.PolynomialTrial
