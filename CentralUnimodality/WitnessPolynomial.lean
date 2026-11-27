module

public import CentralUnimodality.MomentTest
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Numerical witness polynomials are built from rational roots. All
antiderivative values at rational endpoints are computed over the rationals. -/
@[expose] public section

namespace CentralUnimodality

namespace Witness

def addCoeffs : List ℚ → List ℚ → List ℚ
  | [], v => v
  | u, [] => u
  | a::u, b::v => (a+b) :: addCoeffs u v

def rootCoeffs : List ℚ → List ℚ
  | [] => [1]
  | a::t =>
    let p := rootCoeffs t
    addCoeffs (p.map (-a*·)) (0::p)

def horner {R : Type*} [Field R] [CharZero R] (x : R) : List ℚ → R
  | [] => 0
  | a::t => (a:R) + x * horner x t

theorem horner_add {R : Type*} [Field R] [CharZero R] (x : R) (u v : List ℚ) :
    horner x (addCoeffs u v) = horner x u + horner x v := by
  induction u generalizing v with
  | nil => simp [addCoeffs, horner]
  | cons a u ih =>
    cases v with
    | nil => simp [addCoeffs, horner]
    | cons b v => simp only [addCoeffs, horner, Rat.cast_add, ih]; ring

theorem horner_scale {R : Type*} [Field R] [CharZero R] (x : R) (a : ℚ) (u : List ℚ) :
    horner x (u.map (a*·)) = (a:R)*horner x u := by
  induction u with
  | nil => simp [horner]
  | cons b u ih => simp only [List.map_cons, horner, Rat.cast_mul, ih]; ring

theorem horner_roots {R : Type*} [Field R] [CharZero R] (x : R) (u : List ℚ) :
    horner x (rootCoeffs u) = (u.map (fun a : ℚ => x-(a:R))).prod := by
  induction u with
  | nil => simp [rootCoeffs, horner]
  | cons a u ih =>
    simp only [rootCoeffs, horner_add, horner_scale, horner, Rat.cast_neg, Rat.cast_zero,
      List.map_cons, List.prod_cons, ih]
    ring

def primitiveAt {R : Type*} [Field R] [CharZero R] (x : R) (i : ℕ) : List ℚ → R
  | [] => 0
  | c::t => (c:R)/((i:R)+1) * x^(i+1) + primitiveAt x (i+1) t

theorem primitiveAt_cast (x : ℚ) (i : ℕ) (p : List ℚ) :
    ((primitiveAt x i p : ℚ):ℝ) = primitiveAt (x:ℝ) i p := by
  induction p generalizing i with
  | nil => simp [primitiveAt]
  | cons c p ih => simp [primitiveAt, ih]

theorem primitiveAt_derivative (p : List ℚ) (i : ℕ) (x : ℝ) :
    HasDerivAt (fun y => primitiveAt y i p) (x^i * horner x p) x := by
  induction p generalizing i with
  | nil => simpa [primitiveAt, horner] using hasDerivAt_const x (0:ℝ)
  | cons c p ih =>
    have hd : HasDerivAt (fun y : ℝ => (c:ℝ)/((i:ℝ)+1)*y^(i+1)) ((c:ℝ)*x^i) x := by
      convert (hasDerivAt_pow (i+1) x).const_mul ((c:ℝ)/((i:ℝ)+1)) using 1
      simp only [Nat.cast_succ, Nat.add_sub_cancel]
      field_simp
    have hv : x^i * horner x (c::p) =
        (c:ℝ)*x^i + x^(i+1)*horner x p := by simp only [horner, pow_succ]; ring
    rw [hv]
    exact hd.add (ih (i+1))

def coefficients (B t : ℚ) (roots : List ℚ) := rootCoeffs (B :: t :: (roots++roots))

noncomputable def primitive (B t : ℚ) (roots : List ℚ) (x : ℝ) : ℝ :=
  primitiveAt x 0 (coefficients B t roots)

theorem primitive_derivative (B t : ℚ) (roots : List ℚ) (x : ℝ) :
    HasDerivAt (primitive B t roots)
      (((B:ℝ)-x)*((t:ℝ)-x) * (roots.map (fun r : ℚ => x-(r:ℝ))).prod^2) x := by
  have h := primitiveAt_derivative (coefficients B t roots) 0 x
  simp only [coefficients, horner_roots, List.map_cons, List.prod_cons, List.map_append,
    List.prod_append, pow_zero, one_mul] at h
  convert h using 1 <;> first | rfl | ring

end Witness

end CentralUnimodality
