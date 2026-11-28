module

public import CentralUnimodality.PackedBaseResidual
public import CentralUnimodality.BalancedDensePacking

/-! Exact dense evaluation of arbitrary beta products. A single signed integer
multiplication supplies all convolution coefficients, and the output shares
one positive factorial denominator. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Polynomial Finset ReturnSplit

def productBits (a b : List ℤ) := (coefficientMass a*coefficientMass b).log2+1

def packedDenseProduct (a b : List ℤ) :=
  let k := productBits a b
  blockCenteredDigits k 7 (a.length+b.length-1) (blockPackDense (k+1) 6 a*blockPackDense (k+1) 6 b)

theorem packedDenseProduct_eq (a b : List ℤ) :
    packedDenseProduct a b=let k := productBits a b
      centeredDigits k (a.length+b.length-1) (packDense (k+1) a*packDense (k+1) b) := by
  simp only [packedDenseProduct,blockCenteredDigits_exact,blockPackDense_exact]

@[simp] theorem packedDenseProduct_length (a b : List ℤ) :
    (packedDenseProduct a b).length=a.length+b.length-1 := by
  rw [packedDenseProduct_eq]
  exact centeredDigits_length ..

theorem packed_dense_product (a b : List ℤ) : densePoly (packedDenseProduct a b)=densePoly a*densePoly b := by
  let k := productBits a b
  have small (i : ℕ) : |(densePoly a*densePoly b).coeff i|<2^k := by
    apply (dense_product_bound a b i).trans_lt
    exact_mod_cast (Nat.lt_log2_self (n:=coefficientMass a*coefficientMass b))
  have eval : packDense (k+1) a*packDense (k+1) b=(densePoly a*densePoly b).eval (2^(k+1)) := by
    rw [eval_mul,packDense_eval,packDense_eval]
  ext i
  rw [packedDenseProduct_eq,dense_coeff]
  change (centeredDigits k (a.length+b.length-1) _)[i]?.getD 0=_
  rw [eval]
  by_cases hi : i<a.length+b.length-1
  · rw [centeredDigits_coeff _ _ _ small hi]; rfl
  · rw [List.getElem?_eq_none (by simpa only [centeredDigits_length] using le_of_not_gt hi)]
    change 0=_
    rw [coeff_mul]
    symm
    apply sum_eq_zero
    intro z hz
    have sum := Finset.mem_antidiagonal.mp hz
    simp only [dense_coeff]
    by_cases l : a.length≤z.1
    · simp [List.getElem?_eq_none l]
    · simp [List.getElem?_eq_none (by omega : b.length≤z.2)]

theorem real_packed_dense_product (a b : List ℤ) :
    realDense (packedDenseProduct a b)=realDense a*realDense b := by
  simp [realDense,packed_dense_product]

def divideWeights (common : ℕ) : List ℤ → ℕ → ℕ → List ℤ
  | [], _, _ => []
  | c::cs, j, f => ((common/f:ℕ):ℤ)*c::divideWeights common cs (j+1) (f*(4*(j+1)))

private theorem divided_coeff (c : ℕ) (a : List ℤ) (j i : ℕ) :
    (densePoly (divideWeights c a j (fullFactor j))).coeff i=
      ((c/fullFactor (j+i):ℕ):ℤ)*(densePoly a).coeff i := by
  induction a generalizing j i with
  | nil => simp [divideWeights,densePoly]
  | cons x a ih =>
    cases i with
    | zero => simp [divideWeights,dense_coeff]
    | succ i =>
      rw [divideWeights,show fullFactor j*(4*(j+1))=fullFactor (j+1) by rfl]
      simp only [densePoly,coeff_add,coeff_C,ite_eq_right (Nat.succ_ne_zero i),coeff_X_mul,zero_add]
      simpa only [show j+(i+1)=(j+1)+i by omega] using ih (j+1) i

private theorem factor_dvd {i n : ℕ} (h : i≤n) : fullFactor i ∣ fullFactor n := by
  induction n,h using Nat.le_induction with
  | base => exact dvd_refl _
  | succ n _ ih => exact dvd_mul_of_dvd_left ih _

private theorem restore_weights (a : List ℤ) :
    diagonal (fun k => (fullFactor k:ℝ)) (realDense (divideWeights (fullFactor (a.length-1)) a 0 1))=
      C (fullFactor (a.length-1):ℝ)*realDense a := by
  ext i
  rw [diagonal_coeff,coeff_C_mul]
  simp only [realDense,coeff_map,eq_intCast]
  have divC := divided_coeff (fullFactor (a.length-1)) a 0 i
  simp only [show fullFactor 0=1 by rfl,Nat.zero_add] at divC
  rw [divC,Int.cast_mul,Int.cast_natCast]
  by_cases h : i<a.length
  · have d := Nat.div_mul_cancel (factor_dvd (by omega : i≤a.length-1))
    have e : (↑(fullFactor (a.length-1)/fullFactor i):ℝ)*fullFactor i=fullFactor (a.length-1) := by exact_mod_cast d
    linear_combination (↑((densePoly a).coeff i):ℝ)*e
  · rw [dense_coeff,List.getElem?_eq_none (le_of_not_gt h)]
    simp

def betaDense (a b : List ℤ) : ℕ × List ℤ :=
  let product := packedDenseProduct (halfWeighted a) (halfWeighted b)
  let den := fullFactor (product.length-1)
  (den,divideWeights den product 0 1)

theorem betaDense_pos (a b : List ℤ) : 0<(betaDense a b).1 := by
  unfold betaDense
  dsimp only
  rw [fullFactor_eq]
  positivity

theorem betaDense_real (a b : List ℤ) : realDense (betaDense a b).2=
    C ((betaDense a b).1:ℝ)*betaProduct (realDense a) (realDense b) := by
  let product := packedDenseProduct (halfWeighted a) (halfWeighted b)
  change realDense (divideWeights (fullFactor (product.length-1)) product 0 1)=_
  apply diagonal_full_injective
  rw [restore_weights,diagonal_const_mul,diagonal_betaProduct]
  change C (fullFactor (product.length-1):ℝ)*realDense product=C (fullFactor (product.length-1):ℝ)*_
  congr 1
  rw [show realDense product=realDense (halfWeighted a)*realDense (halfWeighted b) from real_packed_dense_product ..]
  change realDense (weightList (fun i => 4*i+2) a 0 (halfFactor 0))*
    realDense (weightList (fun i => 4*i+2) b 0 (halfFactor 0))=_
  rw [realDense_weightList _ halfFactor (fun _ => rfl),realDense_weightList _ halfFactor (fun _ => rfl)]

end CentralUnimodality.PolynomialTrial
