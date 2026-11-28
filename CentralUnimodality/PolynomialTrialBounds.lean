module

public import CentralUnimodality.CertifiedChebyshev
public import CentralUnimodality.PolynomialTrialData
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! Interpret the published dyadic coefficients as a real function of
scaled time. The kernel checks its first two derivative rows and their
norms over the whole interval. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

open Polynomial

def entry (a : List ℤ) (i : ℕ) : ℤ := a[i]?.getD 0

private theorem entry_zero {a : List ℤ} {i : ℕ} (h : a.length ≤ i) : entry a i=0 := by
  simp [entry,List.getElem?_eq_none h]

def doubleHead : List ℤ → List ℤ
  | [] => []
  | c::a => (2*c)::a

def derivativeRow (start : ℕ) : List ℤ → List ℤ
  | [] => []
  | _::a =>
    let tail := derivativeRow (start+1) a
    (2*((start:ℤ)+1)*entry a 0+entry tail 1)::tail

@[simp] theorem derivativeRow_length (a : List ℤ) (s : ℕ) : (derivativeRow s a).length=a.length := by
  induction a generalizing s with
  | nil => rfl
  | cons _ a ih => simp [derivativeRow,ih]

theorem derivativeRow_step (a : List ℤ) (s i : ℕ) :
    entry (derivativeRow s a) i-entry (derivativeRow s a) (i+2)=
      2*((s:ℤ)+i+1)*entry a (i+1) := by
  induction a generalizing s i with
  | nil => simp [entry,derivativeRow]
  | cons c a ih =>
    cases i with
    | zero => simp [entry,derivativeRow]
    | succ i =>
      change entry (derivativeRow (s+1) a) i-entry (derivativeRow (s+1) a) (i+2)=
        2*((s:ℤ)+(i+1:ℕ)+1)*entry a (i+1)
      rw [ih]; push_cast; ring

noncomputable def realRow (a : List ℤ) : ℝ[X] := weightedSeries a.length (fun i => (entry a i:ℝ))

theorem realRow_derivative (a : List ℤ) :
    derivative (realRow a)=realRow (derivativeRow 0 a) := by
  simp only [realRow,derivativeRow_length]
  apply weightedSeries_derivative
  · rw [entry_zero le_rfl,Int.cast_zero]
  · rw [entry_zero (by simp),Int.cast_zero]
  · rw [entry_zero (by simp),Int.cast_zero]
  · intro i _
    exact_mod_cast (by simpa using derivativeRow_step a 0 i)

def rowBudget (a : List ℤ) : ℕ :=
  2*(∑ i ∈ Finset.range a.length, (entry a i).natAbs)+(entry a 0).natAbs

theorem realRow_bound (a : List ℤ) {x : ℝ} (hx : |x|≤1) :
    |(realRow a).eval x|≤(rowBudget a:ℝ) := by
  have h := weightedSeries_bound a.length (fun i => (entry a i:ℝ)) hx
  simpa [realRow,rowBudget,Int.natCast_natAbs,Int.cast_abs] using h

noncomputable def value (a : List ℤ) (v : ℝ) : ℝ :=
  (realRow a).eval (1-v/128)/(2*2^120)

theorem value_hasDerivAt (a : List ℤ) (v : ℝ) :
    HasDerivAt (value a) (-value (derivativeRow 0 a) v/128) v := by
  have inner : HasDerivAt (fun x : ℝ => 1-x/128) (0-1/128) v :=
    HasDerivAt.sub (hasDerivAt_const ..) ((hasDerivAt_id v).div_const 128)
  have outer := (((realRow a).hasDerivAt (1-v/128)).comp v inner).div_const (2*2^120)
  convert outer using 1
  · rfl
  · rw [realRow_derivative]; dsimp [value]; ring

theorem value_bound (a : List ℤ) {v : ℝ} (hv : v∈Set.Icc (0:ℝ) 256) :
    |value a v|≤(rowBudget a:ℝ)/(2*2^120) := by
  rw [value,abs_div,abs_of_pos (by positivity : (0:ℝ)<2*2^120)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply realRow_bound
  exact abs_le.mpr ⟨by linarith only [hv.2],by linarith only [hv.1]⟩

def candidate := doubleHead trialRow.toList

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem candidate_budgets :
    rowBudget candidate≤4*2^120 ∧
    rowBudget (derivativeRow 0 candidate)≤4*2^120*128 ∧
    rowBudget (derivativeRow 0 (derivativeRow 0 candidate))≤4*2^120*128^2 := by
  decide +kernel

theorem candidate_bounds {v : ℝ} (hv : v∈Set.Icc (0:ℝ) 256) :
    |value candidate v|≤2 ∧ |deriv (value candidate) v|≤2 ∧ |deriv (deriv (value candidate)) v|≤2 := by
  let d := derivativeRow 0 candidate
  let dd := derivativeRow 0 d
  have D : deriv (value candidate)=fun x => -value d x/128 :=
    funext (fun x => (value_hasDerivAt candidate x).deriv)
  have DD : deriv (deriv (value candidate)) v=value dd v/128^2 := by
    rw [D]
    have H : HasDerivAt (fun x => -value d x/128) (-(-value dd v/128)/128) v :=
      (value_hasDerivAt d v).neg.div_const 128
    rw [H.deriv]; ring
  obtain ⟨h₀,h₁,h₂⟩ := candidate_budgets
  have a : (rowBudget candidate:ℝ)≤4*2^120 := by exact_mod_cast h₀
  have b : (rowBudget d:ℝ)≤4*2^120*128 := by exact_mod_cast h₁
  have c : (rowBudget dd:ℝ)≤4*2^120*128^2 := by exact_mod_cast h₂
  rw [DD,D,abs_div,abs_neg,abs_div]
  norm_num
  refine ⟨?_,?_,?_⟩
  · linarith only [value_bound candidate hv,a]
  · linarith only [value_bound d hv,b]
  · linarith only [value_bound dd hv,c]

end CentralUnimodality.PolynomialTrial
