module

public import CentralUnimodality.PeakGrowthWitnesses

/-! Rational upper bounds on the two losses in the signed growth test.
Each early cost contains its actual time-bin width. The two choices of
estimate have a common change of measure and suffix scale. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic.Peak

structure TimeBin where
  left : ℚ
  right : ℚ
  v : ℚ
  e : ℚ
  shift : ℚ
  lam : ℚ
  beta : ℚ
  z : ℚ
  base : ℚ
  area : Bool

def timeBin (i : Fin 7) (j : ℕ) : TimeBin :=
  let B := tabulated i
  let code := methodCode (shifts i) j
  let d : ℚ := (code/2:ℕ)
  let left := timeEdge i j
  let right := timeEdge i (j+1)
  let v := left-epsilon
  let e := right+epsilon
  let lam := B.upper+d
  let z := rootLo ((1-(lam*(1-v)/128)^2)*(1-e)^3/12)
  let base := d^2*energy/8-v*(1-e/2)^2*(B.lower+d)*(B.lower*(1-B.lower^2*epsilon/6)+d)/8
  ⟨left,right,v,e,d,lam,lam*e/4,z,base,decide (code%2=1)⟩

def liveBudget (β f : ℚ) := 2*β+(4/5)*decay ((12/25)*β^2*f)/rootLo f

def fifthsBudget (C : TimeBin) :=
  let f := C.v/5-2*epsilon
  let g := 3*C.v/5-epsilon
  (1/2+C.beta/128)*(liveBudget C.beta f)^2*(43/50)/rootLo g

def areaY (C : TimeBin) := C.lam*C.e*rootHi ((C.e+epsilon)/2)/2
def areaSave (B : SaddleBin) (C : TimeBin) :=
  (B.lower+C.shift)^2*C.v*(C.v^2-epsilon^2)/96*(1-(C.lam*C.e/256)^2/6)
def areaBudget (C : TimeBin) :=
  let y := areaY C
  let p := rootHi (22/7)
  (4/5)*(1+y*(p+min p y)/2)/(rootLo (C.v-epsilon))^3

def timeExponent (B : SaddleBin) (C : TimeBin) :=
  if C.area then C.base+C.lam*C.e/256-areaSave B C+(areaY C)^2/4 else C.base

def timeCost (B : SaddleBin) (C : TimeBin) :=
  let rank := (1001/1000)*(B.zhi/C.z)^2*(36/100+C.lam*C.z*(43/100))
  let hit := if C.area then areaBudget C else fifthsBudget C
  rank*(C.right-C.left)/(2*B.denom)*hit*decay (-(timeExponent B C))

def timeOK (B : SaddleBin) (C : TimeBin) : Bool :=
  decide (0<C.left ∧ C.left<C.right ∧ 0<C.v-epsilon ∧ C.v≤C.e ∧ C.e<1 ∧
    0<rootLo (C.v-epsilon) ∧ 0<rootLo (C.v/5-2*epsilon) ∧ 0<rootLo (3*C.v/5-epsilon) ∧
    0<C.z ∧ 0≤C.shift ∧ C.shift≤32 ∧ C.lam≤57 ∧
    0<C.v/5-2*epsilon ∧ 80≤4096*(3*C.v/5-epsilon) ∧ C.beta≤(21/100)*64 ∧ timeExponent B C≤0)

def timeUnits (i : Fin 7) (j : ℕ) : ℕ := ⌈(scale:ℚ)*timeCost (tabulated i) (timeBin i j)⌉₊

structure LateBin where
  shift : ℚ
  height : ℚ
  cap : ℚ
  expo : ℚ

def lateBin (i : Fin 7) : LateBin :=
  let B := tabulated i
  let d : ℚ := (shifts i).late
  let a := (B.drift+d/2)*finalCut*(1-finalCut/2)
  ⟨d,a,(B.upper+d)/2-a,d^2*energy/8-a^2/2⟩

def lateCost (B : SaddleBin) (C : LateBin) :=
  let refl := min 1 ((21/25)/(C.height*rootLo (1-finalCut-epsilon)))
  (1001/1000)*decay (-C.expo)*refl*liveBudget C.cap firstCut/B.denom*
    (109/2+(B.upper+C.shift)*B.zhi*(18/5))

def lateOK (C : LateBin) : Bool := decide (0<C.height ∧ 0<C.cap ∧ C.height≤(6/25)*64 ∧
  C.cap≤(6/25)*64 ∧ 0≤C.shift ∧ C.shift≤32 ∧ C.expo≤0)

def earlyTotal (i : Fin 7) : ℚ := ((∑ j∈Finset.range (timeBins i),timeUnits i j):ℕ)/ (scale:ℚ)
def lateTotal (i : Fin 7) : ℚ := charge (lateCost (tabulated i) (lateBin i))

def goodPrefix (B : SaddleBin) : Prop :=
  0≤B.lower ∧ B.lower≤B.upper ∧ B.upper≤9 ∧ 0<B.denom ∧ 0<B.zlo ∧
  B.zhi≤259/1000 ∧ 0<B.drift ∧ 0≤B.variance ∧ B.variance/2≤256 ∧
  survivalExponent B.lower≤256 ∧ 0≤3989/10000*B.gaussian-5/1000

instance (B : SaddleBin) : Decidable (goodPrefix B) := by unfold goodPrefix; infer_instance

end CentralUnimodality.MarkedExcursion.BinArithmetic.Peak
