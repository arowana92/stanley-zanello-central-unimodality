module

public import CentralUnimodality.PackedIntegerPolynomial
public import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic.Ring

/-! Convert a shifted Chebyshev series to its exact signed monomial
coefficients by evaluating the three-term recurrence at a large base. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

open Polynomial Polynomial.Chebyshev

noncomputable def shiftedT (i : ℕ) : ℤ[X] := (T ℤ i).comp (1-2*X)

@[simp] theorem shiftedT_zero : shiftedT 0=1 := by simp [shiftedT]
@[simp] theorem shiftedT_one : shiftedT 1=1-2*X := by simp [shiftedT]

theorem shiftedT_pair (i : ℕ) :
    shiftedT (i+2)=C 2*shiftedT (i+1)-C 4*(X*shiftedT (i+1))-shiftedT i := by
  unfold shiftedT
  simp only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,T_add_two,sub_comp,mul_comp,ofNat_comp,X_comp,
    Polynomial.C_ofNat]
  ring

private theorem coeff_X_bound (p : ℤ[X]) {A : ℤ} (hA : 0≤A) (h : ∀ j, |p.coeff j|≤A) (i : ℕ) :
    |(X*p).coeff i|≤A := by
  cases i with
  | zero => simpa using hA
  | succ i => simpa using h i

theorem shiftedT_bound (j : ℕ) : ∀ i, |(shiftedT j).coeff i|≤(7:ℤ)^j := by
  induction j using Nat.twoStepInduction with
  | zero =>
    intro i; cases i <;> simp [Polynomial.coeff_one]
  | one =>
    intro i; cases i with
    | zero => norm_num
    | succ i => cases i <;> norm_num [Polynomial.coeff_one,coeff_X]
  | more j lo hi =>
    intro i
    rw [shiftedT_pair,coeff_sub,coeff_sub,coeff_C_mul,coeff_C_mul]
    apply (abs_sub ..).trans
    apply (add_le_add (abs_sub ..) (lo i)).trans
    rw [abs_mul,abs_mul]
    have middle := coeff_X_bound _ (by positivity) hi i
    have first := hi i
    rw [pow_succ] at first middle
    rw [pow_succ,pow_succ]
    norm_num
    linarith only [first,middle,pow_nonneg (by decide : (0:ℤ)≤7) j]

def coefficientMass (a : List ℤ) : ℕ := (a.map Int.natAbs).sum

noncomputable def integerChebyshev : List ℤ → ℕ → ℤ[X]
  | [], _ => 0
  | c::a, i => C c*shiftedT i+integerChebyshev a (i+1)

theorem integerChebyshev_bound (a : List ℤ) (j i : ℕ) :
    |(integerChebyshev a j).coeff i|≤(coefficientMass a:ℤ)*7^(j+a.length) := by
  induction a generalizing j with
  | nil => simp [integerChebyshev,coefficientMass]
  | cons c a ih =>
    rw [integerChebyshev,coeff_add,coeff_C_mul]
    apply (abs_add_le ..).trans
    rw [abs_mul]
    have e : (7:ℤ)^j≤7^(j+(c::a).length) := pow_le_pow_right₀ (by decide) (by omega)
    have A := mul_le_mul_of_nonneg_left ((shiftedT_bound j i).trans e) (abs_nonneg c)
    have B := ih (j+1)
    simp only [List.length_cons,show j+1+a.length=j+(a.length+1) by omega] at A B ⊢
    change _≤((c.natAbs+coefficientMass a:ℕ):ℤ)*_
    push_cast
    linarith only [A,B]

def packChebAux (b : ℕ) : List ℤ → ℤ → ℤ → ℤ
  | [], _, _ => 0
  | c::a, u, v => c*u+packChebAux b a v (2*v-(v <<< (b+3))-u)

def packCheb (b : ℕ) (a : List ℤ) : ℤ := packChebAux b a 1 (1-(1 <<< (b+2)))

theorem packCheb_eval (b : ℕ) (a : List ℤ) :
    packCheb b a=(integerChebyshev a 0).eval (2^(b+1)) := by
  let B : ℤ := 2^(b+1)
  have aux (l : List ℤ) (j : ℕ) :
      packChebAux b l ((shiftedT j).eval B) ((shiftedT (j+1)).eval B)=(integerChebyshev l j).eval B := by
    induction l generalizing j with
    | nil => simp [integerChebyshev,packChebAux]
    | cons c l ih =>
      have next : (shiftedT (j+2)).eval B=
          2*(shiftedT (j+1)).eval B-((shiftedT (j+1)).eval B <<< (b+3))-(shiftedT j).eval B := by
        rw [shiftedT_pair,Int.shiftLeft_eq]
        simp only [eval_sub,eval_mul,eval_C,eval_X,B]
        ring
      rw [packChebAux,← next,ih,integerChebyshev,eval_add,eval_mul,eval_C]
  have H := aux a 0
  simpa [packCheb,B,Int.shiftLeft_eq,pow_succ,show ∀ x : ℤ, 2*(x*2)=x*2*2 by intro; ring] using H

theorem unpackCheb_coeff (b : ℕ) (a : List ℤ) (small : (coefficientMass a:ℤ)*7^a.length<2^b)
    {i : ℕ} (hi : i<a.length) :
    (centeredDigits b a.length (packCheb b a))[i]?=some ((integerChebyshev a 0).coeff i) := by
  rw [packCheb_eval]
  apply centeredDigits_coeff _ _ _ _ hi
  intro k
  exact (integerChebyshev_bound a 0 k).trans_lt (by simpa using small)

end CentralUnimodality.PolynomialTrial
