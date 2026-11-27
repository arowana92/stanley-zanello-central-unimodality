module

public import CentralUnimodality.ScaledExtraction
public import CentralUnimodality.MomentWitnesses
public import CentralUnimodality.WallisTrial

/-! Assemble the two reciprocal-size polynomials for a witness. The
parity split leaves a single common Wallis factor for the odd orders. -/
@[expose] public section

namespace CentralUnimodality.Witness

open Laurent

abbrev Pair := List ℚ × List ℚ

def momentPolynomial (P : ℕ → Laurent) (δ r : ℕ) : Option (List ℚ) := do
  let d := 3*r/2
  let q ← extractPolynomial (1+r%2) d (cellNumerator (-(δ:ℚ)/2) P r)
  return q.map ((1/(2:ℚ)^d)*·)

def buildPair (M : ℕ → Option (List ℚ)) : ℕ → List ℚ → Option Pair
  | _, [] => some ([],[])
  | r, c::cs => do
    let q ← M r
    let (even,odd) ← buildPair M (r+1) cs
    let u := q.map (c*·)
    if r%2 = 0 then return (addCoeffs u even,odd)
    else return (even,addCoeffs u odd)

def familyPair (δ : ℕ) (v : Data) : Option Pair :=
  let cs := coefficients v.B v.t v.roots
  let T := Laurent.tables (cs.length-1)
  let raw := (List.range cs.length).map (rawNumerator (lookup T.1) (lookup T.2) δ)
  buildPair (momentPolynomial (fun j => raw[j]?.getD []) δ) 0 cs

def upperTest (polys : Pair) (b : List ℚ) (c ε : ℚ) : Bool :=
  nonpositive (1/96) (addCoeffs [ε] (addCoeffs polys.1 ((times polys.2 b).map (c*·))))

def checkPair (v : Data) (δ : ℕ) (ε : ℚ) : Bool :=
  match familyPair δ v with
  | none => false
  | some pair => upperTest pair Wallis.lower Wallis.lowerConstant ε &&
      upperTest pair Wallis.upper Wallis.upperConstant ε

end CentralUnimodality.Witness
