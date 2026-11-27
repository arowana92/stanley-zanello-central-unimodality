module

public import CentralUnimodality.CurveQuotient
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.MvPolynomial.Equiv

/-! An explicit minor evaluates the class of each bivariate alternant.
The first exponent is the area grading (the false column of variables). -/
@[expose] public section

namespace CentralUnimodality.Polarization
open MvPolynomial
variable {n : ℕ}

noncomputable def pairedMonomial (a d : Fin n → ℕ) : Poly n :=
  ∏ i, X (false,i)^a i * X (true,i)^d i

noncomputable def alternant (a d : Fin n → ℕ) : Poly n := signedSum (pairedMonomial a d)

theorem alternant_det (a d : Fin n → ℕ) :
    alternant a d = (Matrix.of fun i j => (X (false,i):Poly n)^a j * X (true,i)^d j).det := by
  classical
  simp [alternant,signedSum,pairedMonomial,Matrix.det_apply,Units.smul_def,reindex]

theorem alternant_bidegree (a d : Fin n → ℕ) :
    alternant a d ∈ bidegreeSpace n ((∑ i, a i)+(∑ i, d i)) (∑ i, a i) := by
  apply sum_bidegree
  have h (b : Bool) : (pairedMonomial a d).IsWeightedHomogeneous (degree b)
      (∑ i, ((a i:ℤ)*degree b (false,i)+(d i:ℤ)*degree b (true,i))) := by
    apply IsWeightedHomogeneous.prod
    intro i _
    apply IsWeightedHomogeneous.mul
    · simpa [nsmul_eq_mul] using (isWeightedHomogeneous_X ℚ (degree b) (false,i)).pow (a i)
    · simpa [nsmul_eq_mul] using (isWeightedHomogeneous_X ℚ (degree b) (true,i)).pow (d i)
  constructor
  · simpa [degree,column] using h false
  · simpa [degree,column] using h true

theorem alternant_class_mem (a d : Fin n → ℕ) :
    (relations n).mkQ (alternant a d) ∈
      coinvariantSpace n ((∑ i, a i)+(∑ i, d i)) (∑ i, a i) :=
  ⟨_,⟨alternant_bidegree a d,sum_alternating _⟩,rfl⟩

private theorem separated_coeff (p : Fin n → Polynomial ℚ) (e : Fin n →₀ ℕ) :
    (∏ i, Polynomial.aeval (X i : SinglePoly n) (p i)).coeff e = ∏ i, (p i).coeff (e i) := by
  classical
  induction n with
  | zero => have : e=0 := by ext i; exact i.elim0
            simp [this]
  | succ n ih =>
    let E := finSuccEquiv ℚ n
    have head : E (Polynomial.aeval (X 0) (p 0)) = (p 0).map C := by
      rw [← Polynomial.aeval_algHom_apply E]
      change Polynomial.aeval (finSuccEquiv ℚ n (X 0)) _ = _
      rw [finSuccEquiv_X_zero,Polynomial.aeval_X_left_eq_map]
      rfl
    have tail (i : Fin n) : E (Polynomial.aeval (X i.succ) (p i.succ)) =
        Polynomial.C (Polynomial.aeval (X i) (p i.succ)) := by
      rw [← Polynomial.aeval_algHom_apply E]
      change Polynomial.aeval (finSuccEquiv ℚ n (X i.succ)) _ = _
      rw [finSuccEquiv_X_succ]
      induction p i.succ using Polynomial.induction_on' with
      | add f g hf hg => simp [hf,hg]
      | monomial k r =>
        simp [Polynomial.aeval_monomial,Algebra.algebraMap_eq_smul_one]
        exact Algebra.smul_def _ _
    conv_lhs => rw [← Finsupp.cons_tail e,← finSuccEquiv_coeff_coeff]
    rw [Fin.prod_univ_succ,Fin.prod_univ_succ (f := fun i => (p i).coeff (e i))]
    change ((E (_*_)).coeff _).coeff _ = _
    rw [map_mul, map_prod,head]
    simp_rw [tail]
    rw [← map_prod,Polynomial.coeff_mul_C,Polynomial.coeff_map,coeff_C_mul,ih]
    rfl

/-- The rows are exponents (a,d) and the columns are the powers 0 through n-1. -/
noncomputable def curveMatrix (U : Polynomial ℚ) (a d : Fin n → ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => ((Polynomial.X:Polynomial ℚ)^(d i+a i) * U^(a i)).coeff (j:ℕ)

theorem probe_pairedMonomial (U : Polynomial ℚ) (a d : Fin n → ℕ) :
    curveProbe U (pairedMonomial a d) = (curveMatrix U a d).det := by
  classical
  change (curve U (signedSum (pairedMonomial a d))).coeff _ = _
  rw [signedSum,map_sum,coeff_sum,← Matrix.det_transpose,Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  rw [map_zsmul,← Int.cast_smul_eq_zsmul ℚ,coeff_smul]
  change (σ.sign:ℚ)*_ = (σ.sign:ℚ)*_
  congr 1
  let p := fun i => (Polynomial.X:Polynomial ℚ)^(d i+a i)*U^(a i)
  have site (i j : Fin n) : curve U ((X (false,i))^a j * (X (true,i))^d j) =
      Polynomial.aeval (X i) (p j) := by
    simp [p,mul_pow,pow_add]; ring
  have he : curve U (rename (reindex σ) (pairedMonomial a d)) =
      ∏ i, Polynomial.aeval (X i) (p (σ.symm i)) := by
    unfold pairedMonomial
    rw [map_prod,map_prod]
    apply Eq.trans _ (Equiv.prod_comp σ (fun i => Polynomial.aeval (X i : SinglePoly n) (p (σ.symm i))))
    apply Finset.prod_congr rfl
    intro i _
    simpa [reindex] using site (σ i) i
  rw [he,separated_coeff]
  simpa [curveMatrix,p] using Equiv.prod_comp σ.symm (fun i => (p i).coeff (σ i:ℕ))

theorem quotientProbe_alternant (U : Polynomial ℚ) (a d : Fin n → ℕ) :
    quotientProbe U ((relations n).mkQ (alternant a d)) =
      (Fintype.card (Perm n):ℚ)*(curveMatrix U a d).det := by
  have ha := sum_alternating (pairedMonomial a d)
  have he : signedSum (alternant a d) = (Fintype.card (Perm n)) • alternant a d := by
    unfold signedSum
    have h (σ : Perm n) : (σ.sign:ℤ) • rename (reindex σ) (alternant a d) = alternant a d := by
      change (σ.sign:ℤ) • rename (reindex σ) (signedSum (pairedMonomial a d)) = _
      rw [ha σ,smul_smul]
      rcases Int.units_eq_one_or σ.sign with he|he <;> simp [he,alternant]
    simp [h]
  rw [quotientProbe_mk,← probe_pairedMonomial]
  change (curve U (signedSum (alternant a d))).coeff _ = _*(curve U (alternant a d)).coeff _
  rw [he,map_nsmul,← Nat.cast_smul_eq_nsmul ℚ,coeff_smul]
  rfl

end CentralUnimodality.Polarization
