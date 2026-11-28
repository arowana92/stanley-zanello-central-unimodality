module

public import CentralUnimodality.ChebyshevShift
public import CentralUnimodality.PolynomialTrialBounds

/-! Kernel certificates for the two cubic-exponential differential
equations, in the same Chebyshev coordinates as the amplitude trial. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

open Polynomial Polynomial.Chebyshev

def odeRow (a : List ℤ) (k : ℤ) (i : ℕ) : ℤ :=
  -2*entry (derivativeRow 0 a) i+k*scaleShift (scaleShift (entry a)) i

def odeBudget (a : List ℤ) (k : ℤ) : ℕ :=
  2*(∑ i ∈ Finset.range (a.length+2), (odeRow a k i).natAbs)+(odeRow a k 0).natAbs

private theorem outside {a : List ℤ} {i : ℕ} (h : a.length ≤ i) : entry a i=0 := by
  simp [entry,List.getElem?_eq_none h]

private theorem shifted_outside (a : List ℤ) (i : ℕ) (h : a.length < i) : scaleShift (entry a) i=0 := by
  cases i with
  | zero => omega
  | succ i => simp [scaleShift,neighbor,outside (a:=a) (i:=i+1) (by omega),
      outside (a:=a) (i:=i) (by omega),outside (a:=a) (i:=i+2) (by omega)]

theorem ode_polynomial (a : List ℤ) (k : ℤ) :
    weightedSeries (a.length+2) (fun i => (odeRow a k i:ℝ)) =
      -2*realRow (derivativeRow 0 a)+C (k:ℝ)*(2-2*X)^2*realRow a := by
  let n := a.length
  let d := derivativeRow 0 a
  have dc (j : ℕ) (hj : n≤j) : (entry d j:ℝ)=0 := by
    rw [outside (by simpa only [d,derivativeRow_length] using hj),Int.cast_zero]
  have hc (j : ℕ) (hj : n≤j) : entry a j=0 := outside hj
  have id : (fun i => (odeRow a k i:ℝ))=
      fun i => (-2:ℝ)*(entry d i:ℝ)+(k:ℝ)*(scaleShift (scaleShift (entry a)) i:ℝ) := by
    funext i; simp [odeRow,d]
  rw [id,weightedSeries_linear,weightedSeries_succ_zero _ _ (dc _ (by omega)),
    weightedSeries_succ_zero _ _ (dc _ le_rfl),scaleShift_series (n+1) _
      (shifted_outside _ _ (by dsimp [n]; omega)) (shifted_outside _ _ (by dsimp [n]; omega)),
    scaleShift_series n _ (hc _ le_rfl) (hc _ (by omega))]
  simp only [realRow,derivativeRow_length,map_neg,Polynomial.C_ofNat,d,n]
  ring

theorem ode_value_bound (a : List ℤ) (k : ℤ) {v : ℝ} (hv : v∈Set.Icc (0:ℝ) 256) :
    |256*deriv (value a) v+(k:ℝ)*(v/64)^2*value a v|≤(odeBudget a k:ℝ)/(2*2^120) := by
  let x := 1-v/128
  have hx : |x|≤1 := abs_le.mpr ⟨by dsimp [x]; linarith only [hv.2],by dsimp [x]; linarith only [hv.1]⟩
  have bound := weightedSeries_bound (a.length+2) (fun i => (odeRow a k i:ℝ)) hx
  rw [ode_polynomial] at bound
  have he : 256*deriv (value a) v+(k:ℝ)*(v/64)^2*value a v =
      ((-2*realRow (derivativeRow 0 a)+C (k:ℝ)*(2-2*X)^2*realRow a).eval x)/(2*2^120) := by
    rw [(value_hasDerivAt a v).deriv]
    simp only [value,eval_add,eval_mul,eval_neg,eval_ofNat,eval_C,eval_pow,eval_sub,eval_X,x]
    ring
  rw [he,abs_div,abs_of_pos (by positivity : (0:ℝ)<2*2^120)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  simpa [odeBudget,Int.natCast_natAbs,Int.cast_abs] using bound

def endpointNumerator (a : List ℤ) : ℤ :=
  2*(∑ i ∈ Finset.range a.length, entry a i)-entry a 0

theorem value_zero (a : List ℤ) : value a 0=(endpointNumerator a:ℝ)/(2*2^120) := by
  simp [value,realRow,weightedSeries,eval_finsetSum,T_eval_one,endpointNumerator]

def freeCandidate := doubleHead freeRow.toList
def bridgeCandidate := doubleHead bridgeRow.toList

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem gaussian_budgets :
    odeBudget freeCandidate 131072*10^22≤2*2^120 ∧
    odeBudget bridgeCandidate 32768*10^22≤2*2^120 ∧
    (endpointNumerator freeCandidate-2*2^120).natAbs*10^22≤2*2^120 ∧
    (endpointNumerator bridgeCandidate-2*2^120).natAbs*10^22≤2*2^120 := by
  decide +kernel

end CentralUnimodality.PolynomialTrial
