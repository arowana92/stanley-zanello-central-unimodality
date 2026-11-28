module

public import CentralUnimodality.BalancedIntervalSigns
public import CentralUnimodality.BlockRadixDigits

/-! Exact Taylor shift on a half-unit physical interval. After setting
`t = 4v - (2i+1)`, the monomial variable is `(2i+1+t)/1024`.
All coefficients have a common denominator, including an extra
factor of 1024 so that the zero polynomial needs no special case. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Polynomial

def affineStep (l : ℤ) : List ℤ → ℤ → List ℤ
  | [], d => [d]
  | c::a, d => (l*c+d)::affineStep l a c

def affineRow (l : ℤ) : List ℤ → List ℤ
  | [] => []
  | c::a => affineStep l (affineRow l a) (c*1024^(a.length+1))

private theorem step_length (l : ℤ) (a : List ℤ) (d : ℤ) :
    (affineStep l a d).length=a.length+1 := by
  induction a generalizing d with
  | nil => rfl
  | cons c a ih => simp [affineStep,ih]

theorem affine_length (l : ℤ) (a : List ℤ) : (affineRow l a).length=a.length := by
  induction a with
  | nil => rfl
  | cons c a ih => simp [affineRow,step_length,ih]

private theorem step_mass (l : ℤ) (a : List ℤ) (d : ℤ) :
    coefficientMass (affineStep l a d)≤(l.natAbs+1)*coefficientMass a+d.natAbs := by
  induction a generalizing d with
  | nil => simp [affineStep,coefficientMass]
  | cons c a ih =>
    have h := Int.natAbs_add_le (l*c) d
    rw [Int.natAbs_mul] at h
    change (l*c+d).natAbs+coefficientMass (affineStep l a c)≤
      (l.natAbs+1)*(c.natAbs+coefficientMass a)+d.natAbs
    have sub := ih c
    nlinarith only [h,sub]

theorem affine_mass (l : ℤ) (hl : l.natAbs+1≤1024) (a : List ℤ) :
    coefficientMass (affineRow l a)≤coefficientMass a*1024^a.length := by
  induction a with
  | nil => simp [affineRow,coefficientMass]
  | cons c a ih =>
    apply (step_mass ..).trans
    rw [Int.natAbs_mul,Int.natAbs_pow]
    change (l.natAbs+1)*coefficientMass (affineRow l a)+c.natAbs*1024^(a.length+1)≤
      (c.natAbs+coefficientMass a)*1024^(a.length+1)
    have sub := Nat.mul_le_mul hl ih
    rw [pow_succ]
    nlinarith only [sub]

private theorem step_packed (l : ℤ) (a : List ℤ) (d : ℤ) (s : ℕ) :
    packDense s (affineStep l a d)=(l+2^s)*packDense s a+d := by
  induction a generalizing d with
  | nil => simp [affineStep,packDense,Int.shiftLeft_eq]
  | cons c a ih => simp only [affineStep,packDense,Int.shiftLeft_eq,ih]; ring

private theorem scalar_den (u v : ℤ) (a : List ℤ) : (scalarHomogeneous u v a).2=v^a.length := by
  induction a with
  | nil => simp [scalarHomogeneous]
  | cons c a ih => simp [scalarHomogeneous,ih,pow_succ,mul_comm]

private theorem affine_scalar (l : ℤ) (a : List ℤ) (s : ℕ) :
    (scalarHomogeneous (l+2^s) 1024 a).1=packDense s (affineRow l a) := by
  induction a with
  | nil => rfl
  | cons c a ih => simp only [scalarHomogeneous,affineRow,step_packed,ih,scalar_den,pow_succ]; ring

def packedAffineRow (bits : ℕ) (l : ℤ) (a : List ℤ) :=
  blockCenteredDigits bits 10 a.length (blockHomogeneous (l+2^(bits+1)) 1024 5 a).1

theorem packedAffineRow_exact (bits : ℕ) (l : ℤ) (hl : l.natAbs+1≤1024) (a : List ℤ)
    (cap : coefficientMass a*1024^a.length<2^bits) : packedAffineRow bits l a=affineRow l a := by
  have small (i : ℕ) : |(densePoly (affineRow l a)).coeff i|<2^bits :=
    (dense_coeff_bound _ _).trans_lt (by exact_mod_cast (affine_mass l hl a).trans_lt cap)
  unfold packedAffineRow
  rw [blockHomogeneous_exact,affine_scalar,packDense_eval,blockCenteredDigits_exact]
  apply List.ext_getElem?
  intro i
  by_cases hi : i<a.length
  · rw [centeredDigits_coeff _ _ _ small hi,dense_coeff,List.getElem?_eq_getElem (by rwa [affine_length])]
    rfl
  · rw [List.getElem?_eq_none (by rw [centeredDigits_length]; omega),
        List.getElem?_eq_none (by rw [affine_length]; omega)]

private theorem step_real (l : ℤ) (a : List ℤ) (d : ℤ) (t : ℝ) :
    (realDense (affineStep l a d)).eval t=((l:ℝ)+t)*(realDense a).eval t+d := by
  induction a generalizing d with
  | nil => simp [affineStep,realDense,densePoly]
  | cons c a ih =>
    have consEval (x : ℤ) (p : List ℤ) : (realDense (x::p)).eval t=(x:ℝ)+t*(realDense p).eval t := by
      simp [realDense,densePoly]
    rw [affineStep,consEval,ih,consEval]; push_cast; ring

theorem affine_real (l : ℤ) (a : List ℤ) (t : ℝ) :
    (realDense (affineRow l a)).eval t=1024^a.length*(realDense a).eval (((l:ℝ)+t)/1024) := by
  induction a with
  | nil => simp [affineRow,realDense,densePoly]
  | cons c a ih =>
    have consEval : (realDense (c::a)).eval (((l:ℝ)+t)/1024)=
        (c:ℝ)+(((l:ℝ)+t)/1024)*(realDense a).eval (((l:ℝ)+t)/1024) := by simp [realDense,densePoly]
    rw [affineRow,step_real,ih,consEval,List.length_cons]
    push_cast; rw [pow_succ]; ring

end CentralUnimodality.PolynomialTrial
