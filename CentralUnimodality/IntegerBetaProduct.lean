module

public import CentralUnimodality.DenseIntegerCertificate
public import CentralUnimodality.GammaPolynomialSplit

/-! Clear the factorial denominators in the arcsine product, turning
the exact real polynomial identity into one integer convolution. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Polynomial ReturnSplit

def halfFactor : ℕ → ℕ
  | 0 => 1
  | n+1 => halfFactor n*(4*n+2)

def fullFactor : ℕ → ℕ
  | 0 => 1
  | n+1 => fullFactor n*(4*(n+1))

theorem fullFactor_eq (n : ℕ) : fullFactor n=4^n*n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => rw [fullFactor,ih,pow_succ,Nat.factorial_succ]; ring

theorem halfFactor_eq (n : ℕ) : (halfFactor n:ℝ)=4^n*n.factorial*survival n := by
  induction n with
  | zero => simp [halfFactor,survival]
  | succ n ih =>
    rw [halfFactor,Nat.cast_mul,ih,survival_succ,Nat.factorial_succ,pow_succ]
    push_cast; field_simp; ring

theorem clear_beta (a b : ℕ) : (fullFactor (a+b):ℝ)*betaWeight a b=(halfFactor a:ℝ)*halfFactor b := by
  rw [fullFactor_eq,halfFactor_eq,halfFactor_eq,betaWeight]
  push_cast
  rw [pow_add]
  field_simp

noncomputable def diagonal (w : ℕ → ℝ) (p : ℝ[X]) : ℝ[X] :=
  ∑ j ∈ p.support, monomial j (w j*p.coeff j)

@[simp] theorem diagonal_coeff (w : ℕ → ℝ) (p : ℝ[X]) (i : ℕ) :
    (diagonal w p).coeff i=w i*p.coeff i := by
  simp only [diagonal,finsetSum_coeff,coeff_monomial_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ h; simp [h]
  · intro hi; simp [notMem_support_iff.mp hi]

private theorem diagonal_sum {ι : Type*} (w : ℕ → ℝ) (s : Finset ι) (f : ι → ℝ[X]) :
    diagonal w (∑ i ∈ s, f i)=∑ i ∈ s, diagonal w (f i) := by
  ext k; simp [Finset.mul_sum]

private theorem diagonal_monomial (w : ℕ → ℝ) (n : ℕ) (c : ℝ) :
    diagonal w (monomial n c)=monomial n (w n*c) := by
  ext i; by_cases h : n=i
  · subst i; simp
  · simp [h]

theorem diagonal_const_mul (w : ℕ → ℝ) (c : ℝ) (p : ℝ[X]) :
    diagonal w (C c*p)=C c*diagonal w p := by ext i; simp [coeff_C_mul,mul_left_comm]

theorem diagonal_full_injective : Function.Injective (diagonal (fun k => (fullFactor k:ℝ))) := by
  intro p q H
  ext k
  have eq := congrArg (fun r : ℝ[X] => r.coeff k) H
  simp only [diagonal_coeff] at eq
  exact mul_left_cancel₀ (by rw [fullFactor_eq]; positivity : (fullFactor k:ℝ)≠0) eq

theorem diagonal_betaProduct (B F : ℝ[X]) :
    diagonal (fun k => (fullFactor k:ℝ)) (betaProduct B F)=
      diagonal (fun k => (halfFactor k:ℝ)) B*diagonal (fun k => (halfFactor k:ℝ)) F := by
  rw [betaProduct,diagonal_sum]
  simp only [diagonal_sum,diagonal_monomial]
  conv_rhs => unfold diagonal
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum,monomial_mul_monomial]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  linear_combination B.coeff a*F.coeff b*clear_beta a b

def weightList (step : ℕ → ℕ) : List ℤ → ℕ → ℕ → List ℤ
  | [], _, _ => []
  | c::a, j, t => (t*c)::weightList step a (j+1) (t*step j)

noncomputable def realDense (a : List ℤ) := (densePoly a).map (Int.castRingHom ℝ)

private theorem weightList_coeff (step w : ℕ → ℕ) (hw : ∀ j, w (j+1)=w j*step j)
    (a : List ℤ) (s i : ℕ) :
    (densePoly (weightList step a s (w s))).coeff i=(w (s+i):ℤ)*(densePoly a).coeff i := by
  induction a generalizing s i with
  | nil => simp [weightList,densePoly]
  | cons c a ih =>
    cases i with
    | zero => simp [weightList,dense_coeff]
    | succ i =>
      rw [weightList,← hw]
      simp only [densePoly,coeff_add,coeff_C,ite_eq_right (Nat.succ_ne_zero i),coeff_X_mul,zero_add]
      simpa only [show s+(i+1)=(s+1)+i by omega] using ih (s+1) i

theorem realDense_weightList (step w : ℕ → ℕ) (hw : ∀ j, w (j+1)=w j*step j)
    (a : List ℤ) : realDense (weightList step a 0 (w 0))=diagonal (fun j => (w j:ℝ)) (realDense a) := by
  ext i; simp [realDense,coeff_map,weightList_coeff step w hw]

end CentralUnimodality.PolynomialTrial
