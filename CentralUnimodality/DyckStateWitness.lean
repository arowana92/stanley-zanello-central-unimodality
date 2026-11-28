module

public meta import Lean.Elab.Term
public meta import CentralUnimodality.PairedDyckColumn

/-! Propose a literal transfer column. The finite certificate checks
each proposed column against the preceding one by kernel reduction. -/
public meta section

namespace CentralUnimodality.HeightBlock
open Lean Elab Term

elab "dyck_column% " b:num e:num H:num n:num : term => do
  let bits := b.getNat
  let modulus := 2^(bits*(e.getNat+1))
  return toExpr (pairedRows bits modulus H.getNat n.getNat)

end CentralUnimodality.HeightBlock
