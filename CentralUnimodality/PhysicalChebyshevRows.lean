module

public import CentralUnimodality.SecondResidualRows
public import CentralUnimodality.ChebyshevShift

/-! Convert a dense integer polynomial in physical time to symmetric
Chebyshev coefficients at x=1-v/128. The recurrence has integral
coefficients and needs only the two neighbors of the current index. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Polynomial Polynomial.Chebyshev Finset

def physicalChebTail (previous : ℤ) : List ℤ → List ℤ
  | [] => [-64*previous]
  | c::a => 64*(2*c-previous-entry a 0)::physicalChebTail c a

private theorem shifted_length (previous : ℤ) (a : List ℤ) :
    (physicalChebTail previous a).length=a.length+1 := by
  induction a generalizing previous with
  | nil => rfl
  | cons c a ih => simp [physicalChebTail,ih]

def physicalChebStep (c : ℤ) : List ℤ → List ℤ
  | [] => [c]
  | x::a => (c+64*(2*x-2*entry a 0))::physicalChebTail x a

private theorem step_length (c : ℤ) (a : List ℤ) :
    (physicalChebStep c a).length=a.length+1 := by
  cases a <;> simp [physicalChebStep,shifted_length]

private theorem shifted_entry (p : ℤ) (a : List ℤ) (i : ℕ) (hi : i≤a.length) :
    entry (physicalChebTail p a) i=64*(2*entry a i-entry (p::a) i-entry a (i+1)) := by
  induction a generalizing p i with
  | nil =>
    have : i=0 := by simpa using hi
    subst i; simp [entry,physicalChebTail]
  | cons c a ih =>
    cases i with
    | zero => simp [entry,physicalChebTail]
    | succ i =>
      simpa [physicalChebTail,entry] using ih c i (by simpa using hi)

private theorem step_entry {c : ℤ} {a : List ℤ} {i : ℕ} (hi : i<a.length+1) :
    entry (physicalChebStep c a) i=(if i=0 then c else 0)+64*scaleShift (entry a) i := by
  cases a with
  | nil =>
    have : i=0 := by simpa using hi
    subst i; simp [physicalChebStep,entry,scaleShift,neighbor]
  | cons x a =>
    cases i with
    | zero => simp [physicalChebStep,entry,scaleShift,neighbor]; ring
    | succ i =>
      have h := shifted_entry x a i (by simp at hi; omega)
      simpa [physicalChebStep,entry,scaleShift,neighbor,sub_add_eq_sub_sub] using h

private theorem series_congr {n : ℕ} (hn : 0<n) {a b : ℕ → ℝ} (h : ∀ i<n, a i=b i) :
    weightedSeries n a=weightedSeries n b := by
  unfold weightedSeries
  rw [h 0 hn]
  congr 2
  apply sum_congr rfl
  intro i hi
  rw [h i (mem_range.mp hi)]

private theorem step_model (c : ℤ) (a : List ℤ) :
    realRow (physicalChebStep c a)=C (c:ℝ)+C 64*(2-2*X)*realRow a := by
  let u := fun i : ℕ => if i=0 then (c:ℝ) else 0
  let k := fun i : ℕ => (scaleShift (entry a) i:ℝ)
  have len : (physicalChebStep c a).length=a.length+1 := step_length c a
  have one : weightedSeries (a.length+1) u=C (c:ℝ) := by
    simp [weightedSeries,u,sum_range_succ']
    ring
  have outside (i : ℕ) (hi : a.length ≤ i) : entry a i=0 := by simp [entry,List.getElem?_eq_none hi]
  have eq := scaleShift_series a.length (entry a) (outside _ le_rfl) (outside _ (by omega))
  change weightedSeries (physicalChebStep c a).length (fun i => (entry (physicalChebStep c a) i:ℝ))=_
  rw [len,series_congr (b:=fun i => 1*u i+64*k i) (by omega) (by
    intro i hi; rw [step_entry hi]; simp [u,k,apply_ite (fun z : ℤ => (z:ℝ))])]
  rw [weightedSeries_linear,one]
  change C 1*C (c:ℝ)+C 64*weightedSeries (a.length+1) (fun i => (scaleShift (entry a) i:ℝ))=_
  rw [eq]
  simp [realRow,mul_assoc]

def physicalCheb : List ℤ → List ℤ
  | [] => []
  | c::a => physicalChebStep c (physicalCheb a)

@[simp] theorem physicalCheb_length (a : List ℤ) : (physicalCheb a).length=a.length := by
  induction a with
  | nil => rfl
  | cons c a ih => simp [physicalCheb,step_length,ih]

theorem physical_cheb_eval (a : List ℤ) (v : ℝ) :
    (realRow (physicalCheb a)).eval (1-v/128)=(realDense a).eval v := by
  induction a with
  | nil => simp [physicalCheb,realRow,weightedSeries,entry,realDense,densePoly]
  | cons c a ih =>
    rw [physicalCheb,step_model]
    simp only [eval_add,eval_mul,eval_C,eval_sub,eval_ofNat,eval_X,ih]
    have cons : (realDense (c::a)).eval v=(c:ℝ)+v*(realDense a).eval v := by simp [realDense,densePoly]
    rw [cons]; ring

end CentralUnimodality.PolynomialTrial
