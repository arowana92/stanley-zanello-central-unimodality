module

public import CentralUnimodality.FrequencyChargeData

/-! Verify the retained allowances of cells 0 through 143. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option Elab.async false

check_bool_range allowance_block_0 allowanceCheck 0 144

end CentralUnimodality.PolynomialTrial
