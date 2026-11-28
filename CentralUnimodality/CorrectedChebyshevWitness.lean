module

public import CentralUnimodality.FirstCorrectionRows

/-! Construct candidate Chebyshev coefficients for the first residual
by rational arithmetic. The sign and polynomial-identity certificates
check the output independently of this construction. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

def integerProduct (a b : Array ℤ) : Array ℤ := Id.run do
  let mut c := Array.replicate (a.size+b.size-1) (0:ℤ)
  for i in [:a.size] do
    let x := a[i]?.getD 0
    for j in [:b.size] do
      let y := b[j]?.getD 0
      c := c.modify (i+j) (·+x*y)
  return c

def cosineCoefficients (a : Array ℤ) : Array ℤ := Id.run do
  let mut c := Array.replicate a.size (0:ℤ)
  for j in [:a.size] do
    let factor := (a[j]?.getD 0) <<< (2*(a.size-1-j))
    let mut choose : ℕ := 1
    for t in [:j+1] do
      let k := j-t
      let weight : ℤ := if k=0 then 1 else if k%2=0 then 2 else -2
      c := c.modify k (·+weight*choose*factor)
      choose := choose*(j+k)/(t+1)
  return c

def residualWitness (σ : ℕ) : ℕ × List ℤ := Id.run do
  let p := (firstOrdinary σ).toArray
  let u := integerProduct (halfWeighted firstBridge).toArray (halfWeighted trialPower).toArray
  let m := integerProduct (halfWeighted bridgePower).toArray (halfWeighted (correctionPower σ)).toArray
  let size := max p.size (max u.size m.size)
  let top := size-1
  let common := fullFactor top
  let mut row := #[]
  let mut fact : ℕ := 1
  for i in [:size] do
    let conv := (u[i]?.getD 0)+7680*(m[i]?.getD 0)
    row := row.push ((common:ℤ)*(p[i]?.getD 0)-(residualDen:ℤ)*(common/fact:ℕ)*conv)
    fact := fact*(4*(i+1))
  let c := cosineCoefficients row
  let den := 4^top*common*7680*2^240*residualDen
  let g := c.foldl (fun d x => d.gcd x.natAbs) den
  return (den/g,(c.map (fun x => x/(g:ℤ))).toList)

end CentralUnimodality.PolynomialTrial
