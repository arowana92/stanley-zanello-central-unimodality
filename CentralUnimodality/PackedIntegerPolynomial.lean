module

public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Recover signed integer polynomial coefficients from one exact
evaluation in a power-of-two base. The bias puts the centered digit
into the ordinary Euclidean remainder interval. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

open Polynomial

def centeredDigits (b : ℕ) : ℕ → ℤ → List ℤ
  | 0, _ => []
  | n+1, val =>
    let q := (val+2^b) >>> (b+1)
    (val-(q <<< (b+1))) :: centeredDigits b n q

@[simp] theorem centeredDigits_length (b n : ℕ) (val : ℤ) : (centeredDigits b n val).length=n := by
  induction n generalizing val with
  | zero => rfl
  | succ n ih => simp [centeredDigits,ih]

theorem eval_split (p : ℤ[X]) (B : ℤ) : p.eval B=p.coeff 0+p.divX.eval B*B := by
  have h := congrArg (Polynomial.eval B) (divX_mul_X_add p)
  simpa only [eval_add,eval_mul,eval_X,eval_C,add_comm (p.coeff 0)] using h.symm

private theorem rounded_quotient (p : ℤ[X]) (b : ℕ) (small : |p.coeff 0|<2^b) :
    (p.eval (2^(b+1))+2^b) >>> (b+1)=p.divX.eval (2^(b+1)) := by
  rw [Int.shiftRight_eq_div_pow,Nat.cast_pow,Nat.cast_ofNat,eval_split p]
  set B : ℤ := 2^(b+1)
  have hB : B=2^b+2^b := by dsimp [B]; rw [pow_succ]; ring
  have hz : B≠0 := by dsimp [B]; positivity
  have rearr : p.coeff 0+p.divX.eval B*B+2^b=(p.coeff 0+2^b)+p.divX.eval B*B := by ring
  rw [rearr,Int.add_mul_ediv_right _ _ hz,Int.ediv_eq_zero_of_lt,Int.zero_add]
  · have := (abs_lt.mp small).1; omega
  · have := (abs_lt.mp small).2; omega

theorem centeredDigits_coeff (p : ℤ[X]) (b n : ℕ) (small : ∀ i, |p.coeff i|<2^b)
    {i : ℕ} (hi : i<n) :
    (centeredDigits b n (p.eval (2^(b+1))))[i]?=some (p.coeff i) := by
  induction n generalizing i p with
  | zero => omega
  | succ n ih =>
    rw [centeredDigits,rounded_quotient p b (small 0)]
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero,Int.shiftLeft_eq,eval_split p]
      congr 1; ring
    | succ i =>
      rw [List.getElem?_cons_succ]
      simpa only [coeff_divX] using ih p.divX (fun k => by simpa using small (k+1)) (by omega : i<n)

/-- Two integer polynomials with bounded coefficients agree whenever
their evaluations agree at the chosen base. -/
theorem eq_of_packed_eval {p q : ℤ[X]} (b : ℕ) (hp : ∀ i, |p.coeff i|<2^b)
    (hq : ∀ i, |q.coeff i|<2^b) (equal : p.eval (2^(b+1))=q.eval (2^(b+1))) : p=q := by
  ext i
  have h := centeredDigits_coeff p b (i+1) hp (Nat.lt_succ_self i)
  rw [equal,centeredDigits_coeff q b (i+1) hq (Nat.lt_succ_self i)] at h
  exact (Option.some.inj h).symm

end CentralUnimodality.PolynomialTrial
