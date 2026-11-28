module

public import CentralUnimodality.QuadraticCachedFactors
public import CentralUnimodality.CacheWeightedJet
public meta import CentralUnimodality.QuadraticCachedFactors
public meta import CentralUnimodality.RationalRowCache

/-! The quadratic jets in the first binomial corrections to the mixed products. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial.QuadraticInputs

set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option Elab.async false

cache_weighted_jet secondBF secondBF_exact 2 1 1 bOne trial
cache_weighted_jet secondEven secondEven_exact 2 1 1 bridge gEven
cache_weighted_jet secondOdd secondOdd_exact 2 1 1 bridge gOdd

end CentralUnimodality.PolynomialTrial.QuadraticInputs
