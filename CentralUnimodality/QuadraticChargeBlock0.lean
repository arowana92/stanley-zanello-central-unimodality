module

public import CentralUnimodality.QuadraticChargeData

/-! Return-time allowances for frequency cells 0 through 99. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option Elab.async false

check_bool_range quadratic_charge_block_0 quadraticAllowanceCheck 0 100

end CentralUnimodality.PolynomialTrial
