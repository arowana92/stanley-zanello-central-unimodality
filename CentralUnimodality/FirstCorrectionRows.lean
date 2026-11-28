module

public import CentralUnimodality.PhysicalCorrectionTrial
public import CentralUnimodality.ExactTrialConvolution

/-! Integer rows for the drift and logarithm polynomials after writing
the physical variable as 256 times the monomial variable. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Polynomial ReturnSplit

def driftRow (d : ℕ) (a : List ℤ) : List ℤ :=
  (List.range a.length).map fun k => (((k+1)*(k+d):ℕ):ℤ)*entry a (k+1)

noncomputable def driftOp (d : ℕ) (P : ℝ[X]) := C (d:ℝ)*P.derivative+X*P.derivative.derivative

theorem driftRow_exact (d : ℕ) (a : List ℤ) : realDense (driftRow d a)=driftOp d (realDense a) := by
  have get (i : ℕ) : (densePoly (driftRow d a)).coeff i=(((i+1)*(i+d):ℕ):ℤ)*(densePoly a).coeff (i+1) := by
    simp only [dense_coeff,driftRow]
    by_cases hi : i<a.length
    · simp [entry,List.getElem?_range hi]
    · simp [List.getElem?_eq_none (show (List.range a.length).length ≤ i by simp; omega),
        List.getElem?_eq_none (show a.length ≤ i+1 by omega),List.getElem?_map]
  ext i
  cases i with
  | zero =>
    simp [realDense,driftOp,coeff_derivative,get]
  | succ i =>
    simp only [realDense,coeff_map,driftOp,coeff_add,coeff_C_mul,coeff_X_mul,coeff_derivative,
      get,Int.coe_castRingHom,Int.cast_mul,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    push_cast; ring

def logTimesRow (a b : ℤ) (p : List ℤ) := linearRows a b (0::0::p) (0::0::0::0::0::p)

theorem logTimesRow_exact (a b : ℤ) (p : List ℤ) :
    realDense (logTimesRow a b p)=(C (a:ℝ)*X^2+C (b:ℝ)*X^5)*realDense p := by
  simp only [logTimesRow,realDense,dense_linear,densePoly,Polynomial.map_add,Polynomial.map_mul,
    Polynomial.map_C,map_X,Int.coe_castRingHom,C_0,zero_add]
  ring

def correctionPower (σ : ℕ) := unpackCheb 1536 (if σ=0 then evenCorrectionRow else oddCorrectionRow).toList

def freeLogTimes (σ : ℕ) := logTimesRow (30720*(2*(σ:ℤ)+1)) 8589934592 freePower
def bridgeLogTimes := logTimesRow 5120 536870912 bridgePower

def firstOrdinary (σ : ℕ) := linearRows (2^120*(residualDen:ℤ)) (15*2^240)
  (linearRows (-512) (-15) (freeLogTimes σ) (driftRow 2 freePower)) (driftRow 2 residualPower)

def firstBridge := linearRows (-512) (-15) bridgeLogTimes (driftRow 1 bridgePower)

end CentralUnimodality.PolynomialTrial
