module

public import CentralUnimodality.QuadraticCachedTrials
public meta import CentralUnimodality.QuadraticCachedTrials
public meta import CentralUnimodality.RationalRowCache

/-! Cache the signed lattice factors and the two corrected amplitudes before
performing their factorial convolutions. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial.QuadraticInputs
open RationalPolyRow

set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option Elab.async false

cache_rational_row bOne bOne_exact := scale (-1) 1 (mul bridge bridgeLogRow)
cache_rational_row bTwo bTwo_exact := mul bridge (secondMultiplierRow bridgeLogRow bridgeLogSecondRow)
cache_rational_row pEven pEven_exact := mul free (secondMultiplierRow (freeLogRow 0) (freeLogSecondRow 0))
cache_rational_row pOdd pOdd_exact := mul free (secondMultiplierRow (freeLogRow 1) (freeLogSecondRow 1))
cache_rational_row gEven gEven_exact := linear 1 1 evenM (halfDriftRow trial)
cache_rational_row gOdd gOdd_exact := linear 1 1 oddM (halfDriftRow trial)

end CentralUnimodality.PolynomialTrial.QuadraticInputs
