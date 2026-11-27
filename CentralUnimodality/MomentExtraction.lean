module

public import CentralUnimodality.MomentTables
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! Extract the unnormalized corank moments at any length from a table that
satisfies the finite Laurent certificate. -/
@[expose] public section

namespace CentralUnimodality.Laurent

open PowerSeries

def ratioSum (n : ℕ) : Laurent → ℚ
  | [] => 0
  | (h,c)::p => c*rootRatio h n + ratioSum n p

theorem coeff_eval (n : ℕ) (p : Laurent) :
    coeff n (eval p) = (n.centralBinom:ℚ)*ratioSum n p := by
  induction p with
  | nil => simp [eval,ratioSum]
  | cons t p ih =>
    obtain ⟨h,c⟩ := t
    rw [eval, map_add, coeff_C_mul, rootPower_coeff, ih, ratioSum]
    ring

def evenNumerator (p : Laurent) := scaleShift 1 (-1) p
def oddNumerator (p : Laurent) := add (scaleShift 1 (-1) p) (scaleShift (-1) 0 p)

theorem evenNumerator_eq (p : Laurent) : eval (evenNumerator p) = ballotBase*eval p := by
  simp [evenNumerator, eval_scaleShift, rootPower_neg_one]

theorem oddNumerator_eq (p : Laurent) :
    eval (oddNumerator p) = X*(2*((dyckBase*ballotBase)*eval p)) := by
  simp only [oddNumerator,eval_add,eval_scaleShift, map_one, one_mul, rootPower_neg_one,
    map_neg, rootPower_zero, mul_one, neg_one_mul]
  have h := catalanRoot_mul_ballotBase
  unfold catalanRoot at h
  linear_combination eval p*h

theorem extracted_even {M : ℕ} {B : ℕ → Laurent}
    (h : SameColumns M (model ballotBase B) (evenBallotSeries (exp ℚ))) (n r : ℕ) (hr : r ≤ M) :
    (rankMoment n 0 r : ℚ) = r.factorial*(n.centralBinom:ℚ)*ratioSum n (evenNumerator (B r)) := by
  have he := congrArg (coeff n) (h r hr)
  rw [model, momentColumn_fromColumns, ← evenNumerator_eq, coeff_eval, even_momentColumn] at he
  field_simp at he
  linear_combination -he

theorem extracted_odd {M : ℕ} {O : ℕ → Laurent}
    (h : SameColumns M (model (dyckBase*ballotBase) O) (oddBallotSeries (exp ℚ)))
    (n r : ℕ) (hr : r ≤ M) :
    2*(rankMoment n 1 r : ℚ) =
      r.factorial*((n+1).centralBinom:ℚ)*ratioSum (n+1) (oddNumerator (O r)) := by
  have he := congrArg (coeff n) (h r hr)
  rw [model, momentColumn_fromColumns, odd_momentColumn] at he
  have hs := congrArg (coeff (n+1)) (oddNumerator_eq (O r))
  rw [coeff_eval, coeff_succ_X_mul, ← map_ofNat (C (R := ℚ)) 2, coeff_C_mul, he] at hs
  field_simp at hs
  linear_combination -hs

end CentralUnimodality.Laurent
