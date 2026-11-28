module

public import CentralUnimodality.LocalJetChecks

/-! Main-trial and correction derivatives in bins 0 through 71. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

set_option maxRecDepth 40000
set_option maxHeartbeats 0
set_option Elab.async false

check_jet_range jet_block_0 0 72

end CentralUnimodality.PolynomialTrial
