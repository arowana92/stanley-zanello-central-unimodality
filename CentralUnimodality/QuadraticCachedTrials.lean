module

public import CentralUnimodality.SecondResidualRows
public import CentralUnimodality.RationalRowCache
public meta import CentralUnimodality.SecondResidualRows
public meta import CentralUnimodality.RationalRowCache

/-! The large physical-time inputs shared by the two signed residuals. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial.QuadraticInputs
open RationalPolyRow

set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option Elab.async false

cache_rational_row bridge bridge_exact := physicalRow rawBridge
cache_rational_row trial trial_exact := physicalRow rawTrial
cache_rational_row free free_exact := physicalRow rawFree
cache_rational_row evenM evenM_exact := physicalRow evenRawM
cache_rational_row oddM oddM_exact := physicalRow oddRawM

end CentralUnimodality.PolynomialTrial.QuadraticInputs
