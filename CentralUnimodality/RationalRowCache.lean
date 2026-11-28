module

public import CentralUnimodality.RationalPolynomialRows
public import Mathlib.Tactic.Eval

/-! Cache integer lists between successive polynomial operations. Each proof
identifies the saved list and denominator by kernel reduction. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial.RationalPolyRow

def encode (p : RationalPolyRow) : List ℤ × ℕ := (p.numer,(p.denom:ℕ)-1)
def decode (d : List ℤ × ℕ) : RationalPolyRow := ⟨d.1,⟨d.2+1,by omega⟩⟩

theorem decode_encode (p : RationalPolyRow) : decode (encode p)=p := by
  rcases p with ⟨a,⟨n,pos⟩⟩
  cases n with
  | zero => omega
  | succ t => rfl

open Lean in
macro "cache_rational_row " nc:("noncomputable")? name:ident proofName:ident " := " e:term : command => do
  let dataName := mkIdent (name.getId.appendAfter "Encoding")
  let checked := mkIdent (proofName.getId.appendAfter "_encoding")
  let data ← if nc.isSome then `(noncomputable def $dataName : List ℤ × ℕ := eval% encode $e)
    else `(def $dataName : List ℤ × ℕ := eval% encode $e)
  let row ← if nc.isSome then `(noncomputable def $name := decode $dataName)
    else `(def $name := decode $dataName)
  let check ← `(private theorem $checked : encode $e=$dataName := by decide +kernel)
  let proof ← `(theorem $proofName : $e=$name :=
    (decode_encode _).symm.trans (congrArg decode $checked))
  return ⟨mkNullNode #[data.raw,row.raw,check.raw,proof.raw]⟩

end CentralUnimodality.PolynomialTrial.RationalPolyRow
