module

public import CentralUnimodality.RankBinWitnesses

/-! Rational arithmetic for the two saddle ranges. The maximal cost at a
first-hit time uses a different rank shift for each signed order. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic

def epsilon : ℚ := 1/4096
def lateCut : ℚ := 15/16
def energy : ℚ := (1+epsilon)*(2+epsilon)/6
def binFraction (curve : Bool) : ℚ := if curve then 1/14 else 1/10

structure SaddleBin where
  lower : ℚ
  upper : ℚ
  fraction : ℚ
  zlo : ℚ
  zhi : ℚ
  drift : ℚ
  denom : ℚ
  variance : ℚ
  gaussian : ℚ

def saddleBin (curve : Bool) (i : ℕ) : SaddleBin :=
  let l := binFraction curve
  let g : ℚ := (1199/100)*(if curve then 15/16 else 3/4)+2*(i:ℚ)
  let G := min 25 (g+2)
  let f := l+epsilon
  let lo := rootLo ((1-(G/128)^2)*(1-f)^3/12)
  let hi := rootHi ((1-l+epsilon)^3/12)
  let κ := g/2*(1-g^2*epsilon/12)
  let denom := 2*κ*(1-f)/(1+G/128)
  let V := (f+(1+G/128)/(1-f)*(f^2+1/(2*κ^2)))/(4*lo^2)
  let x := V/2
  ⟨g,G,l,lo,hi,κ,denom,V,1-x+x^2/2-x^3/6⟩

def cutAt (B : SaddleBin) (i : ℕ) : ℚ := min lateCut (B.fraction+i/48)

def signedCost (r : Fin 3) (d zhi mass diff curv : ℚ) :=
  let u := (1001/1000)*d*zhi
  if r=0 then mass else if r=1 then (1001/1000)*diff+u*mass else curv+2*u*diff

structure RankCharge where
  admissible : Bool
  units : ℕ

def firstCharge (B : SaddleBin) (row : ShiftRow) (i : ℕ) (r : Fin 3) : RankCharge :=
  let v := cutAt B i
  let w := cutAt B (i+1)
  if v=w then ⟨true,0⟩ else
    let e := w+epsilon
    let d := firstShift row i r
    let lam := B.upper+d
    let β := lam*e/4
    let chunk := v/3-2*epsilon
    let root := rootLo chunk
    let F := 2*β+(4/5)/root
    let z := rootLo ((1-(lam*(1-v)/128)^2)*(1-e)^3/12)
    let x := d^2*energy/8-v*(1-e/2)^2*(B.lower+d)*(B.lower*(1-B.lower^2*epsilon/6)+d)/8
    let prob := ((w-v)/2+epsilon)*(1/2+β/128)*F^2*decay (-x)/(root*B.denom)
    let ratio := B.zhi/z
    let cost := signedCost r d B.zhi ((23/50)*ratio) ((23/50)*ratio^2) ((14/25)*ratio^3)
    ⟨decide (x≤0 ∧ 0<root ∧ 0<z ∧ 80≤4096*chunk ∧ 0≤d ∧ d≤32 ∧ lam≤57),
      ⌈(scale:ℚ)*prob*cost⌉₊⟩

def lateCharge (B : SaddleBin) (row : ShiftRow) (r : Fin 3) : RankCharge :=
  let d := lateShift row r
  let a := (B.drift+d/2)*lateCut*(1-lateCut/2)
  let cap := (B.upper+d)/2-a
  let x := d^2*energy/8-a^2/2
  let prob := decay (-x)*(2*cap+(4/5)/rootLo B.fraction)/B.denom
  let cost := signedCost r d B.zhi 19 810 98000
  ⟨decide (x≤0 ∧ 0≤a ∧ a≤(6/25)*64 ∧ 0≤cap ∧ cap≤(6/25)*64 ∧ 0≤d ∧ d≤32),
    ⌈(scale:ℚ)*prob*cost⌉₊⟩

def sumCharges (B : SaddleBin) (row : ShiftRow) (r : Fin 3) : ℚ :=
  (((∑ i ∈ Finset.range 42, (firstCharge B row i r).units)+(lateCharge B row r).units:ℕ):ℚ)/scale

def checkSigns (curve : Bool) (i : ℕ) : Bool :=
  let B := saddleBin curve i
  let row := shiftRow curve i
  let lost := sumCharges B row
  let mass := (3989/10000)*B.gaussian-5/1000-lost 0
  let central := B.variance/(1+B.variance/2)-B.gaussian
  let growth := (999/1000)*B.zlo*B.lower*mass-1/4-lost 1
  let curvature := -((3989/10000)*central+10/1000+lost 2)
  decide ((∀ r : Fin 3, (lateCharge B row r).admissible=true ∧
    ∀ j : Fin 42, (firstCharge B row j r).admissible=true) ∧
    B.lower≤B.upper ∧ B.upper≤25 ∧ 0<B.denom ∧ 0<B.zlo ∧ B.zhi≤259/1000 ∧
    0<B.drift ∧ 0≤B.variance ∧ 0<mass ∧ central<0 ∧
    (if curve then 3/100<curvature else 33/1000<growth))

end CentralUnimodality.MarkedExcursion.BinArithmetic
