module

public import CentralUnimodality.AffineTaylorRows
public import CentralUnimodality.CorrectedTimeBins
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Physical derivatives on each closed half-unit bin. The factor
`4^r` converts derivatives of the shifted variable back to time. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Polynomial ReturnSplit

def degreeWeight (k : ℕ) : List ℤ → List ℤ
  | [] => []
  | c::a => ((k:ℤ)*c)::degreeWeight (k+1) a

def powerDerivative (a : List ℤ) := degreeWeight 1 a.tail

private theorem weighted_get (a : List ℤ) (k i : ℕ) :
    ((degreeWeight k a)[i]?).getD 0=((k+i:ℕ):ℤ)*(a[i]?.getD 0) := by
  induction a generalizing k i with
  | nil => simp [degreeWeight]
  | cons c a ih =>
    cases i with
    | zero => simp [degreeWeight]
    | succ i =>
      simp only [degreeWeight,List.getElem?_cons_succ,ih]
      rw [show k+1+i=k+(i+1) by omega]

theorem powerDerivative_real (a : List ℤ) : realDense (powerDerivative a)=(realDense a).derivative := by
  ext i
  simp only [realDense,coeff_map,powerDerivative,dense_coeff,weighted_get,coeff_derivative]
  cases a with
  | nil => simp
  | cons c a => simp [Nat.add_comm,mul_comm]

theorem realDense_abs (a : List ℤ) {t : ℝ} (ht : |t|≤1) :
    |(realDense a).eval t|≤coefficientMass a := by
  induction a with
  | nil => simp [realDense,densePoly,coefficientMass]
  | cons c a ih =>
    have h : (realDense (c::a)).eval t=(c:ℝ)+t*(realDense a).eval t := by simp [realDense,densePoly]
    have mass : (coefficientMass (c::a):ℝ)=|(c:ℝ)|+coefficientMass a := by simp [coefficientMass]
    rw [h,mass]
    apply (abs_add_le ..).trans
    rw [abs_mul]
    exact add_le_add (le_refl _) ((mul_le_mul ht ih (abs_nonneg _) (by norm_num)).trans_eq (one_mul _))

private theorem affine_jet (a : List ℤ) (L D : ℝ) (r : ℕ) :
    iteratedDeriv r (fun v : ℝ => D*(realDense a).eval (4*v-L))=
      fun v => D*4^r*(realDense (powerDerivative^[r] a)).eval (4*v-L) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ,ih,Function.iterate_succ_apply']
    funext v
    let p := realDense (powerDerivative^[r] a)
    have arg : HasDerivAt (fun x : ℝ => 4*x-L) 4 v := by
      convert (((hasDerivAt_id v).const_mul (4:ℝ)).sub_const L) using 1 <;> simp
    have chain := ((p.hasDerivAt (4*v-L)).comp v arg).const_mul (D*4^r)
    rw [powerDerivative_real]
    change deriv (fun x : ℝ => D*4^r*p.eval (4*x-L)) v=D*4^(r+1)*p.derivative.eval (4*v-L)
    rw [show deriv (fun x : ℝ => D*4^r*p.eval (4*x-L)) v=D*4^r*(p.derivative.eval (4*v-L)*4) from chain.deriv]
    ring

def binJetInteger (bits i r : ℕ) (a : List ℤ) : ℕ :=
  4^r*coefficientMass (powerDerivative^[r] (packedAffineRow bits (2*i+1) a))

theorem binJet_bound {f : ℝ → ℝ} (a : List ℤ)
    (rep : ∀ v, f v=(realDense a).eval (v/256)/2^120) (bits i r : ℕ) (hi : i<288)
    (cap : coefficientMass a*1024^a.length<2^bits) {v : ℝ} (hv : v∈halfInterval i) :
    |iteratedDeriv r f v|≤(binJetInteger bits i r a:ℝ)/(1024^a.length*2^120) := by
  let l : ℤ := 2*(i:ℤ)+1
  have hl : l.natAbs+1≤1024 := by
    have eq : l=((2*i+1:ℕ):ℤ) := by simp [l]
    rw [eq,Int.natAbs_natCast]; omega
  let D : ℝ := 1/(1024^a.length*2^120)
  have D0 : 0≤D := by dsimp [D]; positivity
  have power : (1024:ℝ)^a.length≠0 := by positivity
  have repr : f=fun x : ℝ => D*(realDense (affineRow l a)).eval (4*x-l) := by
    funext x
    rw [rep,affine_real,show ((l:ℝ)+(4*x-l))/1024=x/256 by ring]
    dsimp only [D]; field_simp
  have range : |4*v-(l:ℝ)|≤1 := by
    obtain ⟨lo,hi'⟩ := hv
    change (i:ℝ)/2≤v at lo
    change v≤((i+1:ℕ):ℝ)/2 at hi'
    dsimp [l]; push_cast at *; rw [abs_le]; constructor <;> linarith only [lo,hi']
  rw [repr,affine_jet,abs_mul,abs_of_nonneg (by positivity : 0≤D*4^r)]
  change _≤((4^r*coefficientMass (powerDerivative^[r] (packedAffineRow bits l a)):ℕ):ℝ)/_
  rw [packedAffineRow_exact bits l hl a cap]
  apply (mul_le_mul_of_nonneg_left (realDense_abs _ range) (by positivity : 0≤D*4^r)).trans_eq
  dsimp only [D]; push_cast; ring

end CentralUnimodality.PolynomialTrial
