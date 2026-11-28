module

public import CentralUnimodality.PackedChebyshev
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.ComputeDegree

/-! Integer coefficient lists for the packed comparison of the true
arcsine product with a proposed residual row. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Polynomial

noncomputable def densePoly : List ℤ → ℤ[X]
  | [] => 0
  | c::a => C c+X*densePoly a

theorem dense_coeff (a : List ℤ) (i : ℕ) : (densePoly a).coeff i=a[i]?.getD 0 := by
  induction a generalizing i with
  | nil => simp [densePoly]
  | cons c a ih => cases i <;> simp only [densePoly,coeff_add,coeff_C,coeff_X_mul,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,ih] <;> simp

theorem dense_coeff_bound (a : List ℤ) (i : ℕ) : |(densePoly a).coeff i|≤(coefficientMass a:ℤ) := by
  rw [dense_coeff]
  induction a generalizing i with
  | nil => simp [coefficientMass]
  | cons c a ih =>
    cases i with
    | zero =>
      change |c|≤((c.natAbs+coefficientMass a:ℕ):ℤ)
      simp
    | succ i =>
      have h := ih i
      simp only [coefficientMass,List.map_cons,List.sum_cons,Nat.cast_add] at h ⊢
      simp only [List.getElem?_cons_succ]
      linarith only [h,Int.natCast_nonneg c.natAbs]

def unpackCheb (b : ℕ) (a : List ℤ) : List ℤ := centeredDigits b a.length (packCheb b a)

private theorem shifted_degree (j : ℕ) : (shiftedT j).natDegree≤j := by
  apply natDegree_comp_le.trans
  rw [Chebyshev.natDegree_T,Int.natAbs_natCast]
  have core : (1-2*X:ℤ[X]).natDegree≤1 := by compute_degree!
  exact (Nat.mul_le_mul_left j core).trans_eq (Nat.mul_one j)

private theorem integerChebyshev_support (a : List ℤ) (j i : ℕ) (hi : j+a.length ≤ i) :
    (integerChebyshev a j).coeff i=0 := by
  induction a generalizing j with
  | nil => simp [integerChebyshev]
  | cons c a ih =>
    have n := List.length_cons (a:=c) (as:=a)
    have h₁ := coeff_eq_zero_of_natDegree_lt ((shifted_degree j).trans_lt (by omega : j < i))
    rw [integerChebyshev,coeff_add,coeff_C_mul,h₁,mul_zero,zero_add,ih _ (by omega)]

theorem unpackCheb_poly (b : ℕ) (a : List ℤ) (small : (coefficientMass a:ℤ)*7^a.length<2^b) :
    densePoly (unpackCheb b a)=integerChebyshev a 0 := by
  ext i
  rw [dense_coeff]
  by_cases hi : i<a.length
  · simp [unpackCheb,unpackCheb_coeff b a small hi]
  · simp [unpackCheb,List.getElem?_eq_none (show (centeredDigits b a.length (packCheb b a)).length ≤ i by
      simpa using Nat.le_of_not_gt hi),integerChebyshev_support a 0 i (by omega)]

def packDense (bits : ℕ) : List ℤ → ℤ
  | [] => 0
  | c::a => c+(packDense bits a <<< bits)

theorem packDense_eval (b : ℕ) (a : List ℤ) : packDense b a=(densePoly a).eval (2^b) := by
  induction a with
  | nil => simp [packDense,densePoly]
  | cons c a ih => simp [packDense,densePoly,Int.shiftLeft_eq,ih,mul_comm]

def linearRows (p q : ℤ) : List ℤ → List ℤ → List ℤ
  | [], b => b.map (q*·)
  | a, [] => a.map (p*·)
  | u::a, v::b => (p*u+q*v)::linearRows p q a b

private theorem dense_scale (p : ℤ) (a : List ℤ) : densePoly (a.map (p*·))=C p*densePoly a := by
  induction a with
  | nil => simp [densePoly]
  | cons c a ih => simp only [List.map_cons,densePoly,map_mul,ih]; ring

theorem dense_linear (p q : ℤ) (a b : List ℤ) :
    densePoly (linearRows p q a b)=C p*densePoly a+C q*densePoly b := by
  induction a generalizing b with
  | nil => simp [linearRows,densePoly,dense_scale]
  | cons u a ih =>
    cases b with
    | nil => simp [linearRows,dense_scale,densePoly]; ring
    | cons v b => simp only [linearRows,densePoly,map_add,map_mul,ih]; ring

theorem dense_product_bound (a b : List ℤ) (i : ℕ) :
    |(densePoly a*densePoly b).coeff i|≤(coefficientMass a:ℤ)*coefficientMass b := by
  induction a generalizing i with
  | nil => simp [densePoly,coefficientMass]
  | cons c a ih =>
    have mass : (coefficientMass (c::a):ℤ)=|c|+coefficientMass a := by simp [coefficientMass]
    rw [densePoly,add_mul,mul_assoc X,coeff_add,coeff_C_mul,mass,add_mul]
    apply (abs_add_le ..).trans
    apply add_le_add
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (dense_coeff_bound b i) (abs_nonneg c)
    · cases i with
      | zero => simp; positivity
      | succ i => simpa using ih i

end CentralUnimodality.PolynomialTrial
