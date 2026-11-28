module

public import CentralUnimodality.QuadraticCachedFactors
public import CentralUnimodality.CacheWeightedJet
public meta import CentralUnimodality.QuadraticCachedFactors
public meta import CentralUnimodality.RationalRowCache

/-! The three weighted jets in the second binomial correction to the leading bridge product. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial.QuadraticInputs

set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option Elab.async false

cache_weighted_jet third12 third12_exact 3 1 2 bridge trial
cache_weighted_jet third21 third21_exact 3 2 1 bridge trial
cache_weighted_jet fourth22 fourth22_exact 4 2 2 bridge trial

end CentralUnimodality.PolynomialTrial.QuadraticInputs
