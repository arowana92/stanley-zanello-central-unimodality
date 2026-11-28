module

public import CentralUnimodality.QuadraticCachedTrials
public meta import CentralUnimodality.RationalRowCache

/-! Check every summand of a signed beta jet separately, then assemble the
sum with the binomial coefficients from the symbolic quadrature. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial.QuadraticInputs
open Lean RationalPolyRow

macro "cache_weighted_jet " name:ident proofName:ident r:num a:num b:num p:ident q:ident : command => do
  let mut cmds := #[]
  let mut steps := #[]
  let mut actual ← `(term| RationalPolyRow.zero)
  let mut cached ← `(term| RationalPolyRow.zero)
  for i in [:r.getNat+1] do
    let idx := Syntax.mkNumLit (toString i)
    let tName := mkIdent (name.getId.appendAfter ("Term"++toString i))
    let proof := mkIdent (tName.getId.appendAfter "_exact")
    let term ← `(term| weighted $a $b (diff $idx $p) (diff ($r-$idx) $q))
    let scalar ← `(term| (Nat.choose $r $idx : ℤ)*(-1)^($r-$idx))
    let enc := mkIdent (tName.getId.appendAfter "Encoding")
    let data ← `(noncomputable def $enc : List ℤ × ℕ := eval% encode $term)
    let saved ← `(noncomputable def $tName := decode $enc)
    let cert ← `(private theorem $proof : $term=$tName := by
      have h : encode $term=$enc := by decide +kernel
      exact (decode_encode _).symm.trans (congrArg decode h))
    cmds := cmds.push data.raw |>.push saved.raw |>.push cert.raw
    actual ← `(term| linear 1 1 $actual (scale $scalar 1 $term))
    cached ← `(term| linear 1 1 $cached (scale $scalar 1 $tName))
    steps := steps.push (← `(tactic| rw [($proof)]))
  let sumName := mkIdent (proofName.getId.appendAfter "_sum")
  let enc := mkIdent (name.getId.appendAfter "Encoding")
  let data ← `(def $enc : List ℤ × ℕ := eval% encode (weightedJetRow $r $a $b $p $q))
  let saved ← `(def $name := decode $enc)
  let sum ← `(private theorem $sumName : $cached=$name := by
    have h : encode $cached=$enc := by decide +kernel
    exact (decode_encode _).symm.trans (congrArg decode h))
  let check ← `(theorem $proofName : weightedJetRow $r $a $b $p $q=$name := by
    change $actual=_
    $[$steps:tactic]*
    exact $sumName)
  return ⟨mkNullNode (cmds.push data.raw |>.push saved.raw |>.push sum.raw |>.push check.raw)⟩

end CentralUnimodality.PolynomialTrial.QuadraticInputs
