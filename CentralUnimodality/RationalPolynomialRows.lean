module

public import CentralUnimodality.PackedBetaEvaluation
public import CentralUnimodality.HalfIntervalDerivatives
public import CentralUnimodality.QuadraticResidualPolynomial
public import CentralUnimodality.CorrectionDilation

/-! Dense rational rows for the differential and beta operations in the
quadratic residual. The common denominator is positive, including for zero. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

structure RationalPolyRow where
  numer : List ℤ
  denom : ℕ+
deriving Repr

namespace RationalPolyRow
open Polynomial ReturnSplit

noncomputable def model (p : RationalPolyRow) : ℝ[X] :=
  C (1/(p.denom:ℝ))*realDense p.numer

def zero : RationalPolyRow := ⟨[],1⟩

@[simp] theorem model_zero : zero.model=0 := by simp [zero,model,realDense,densePoly]

def linear (a b : ℤ) (p q : RationalPolyRow) : RationalPolyRow :=
  let n := Nat.lcm p.denom q.denom
  ⟨linearRows (a*(n/(p.denom:ℕ):ℕ)) (b*(n/(q.denom:ℕ):ℕ)) p.numer q.numer,
   ⟨n,Nat.lcm_pos p.denom.pos q.denom.pos⟩⟩

theorem model_linear (a b : ℤ) (p q : RationalPolyRow) :
    (linear a b p q).model=C (a:ℝ)*p.model+C (b:ℝ)*q.model := by
  let n := Nat.lcm p.denom q.denom
  have pos : (0:ℝ)<n := by exact_mod_cast Nat.lcm_pos p.denom.pos q.denom.pos
  have pp : (0:ℝ)<p.denom := by exact_mod_cast p.denom.pos
  have qp : (0:ℝ)<q.denom := by exact_mod_cast q.denom.pos
  have hp : ((n/(p.denom:ℕ):ℕ):ℝ)=n/(p.denom:ℝ) := by
    apply (eq_div_iff pp.ne').mpr
    exact_mod_cast Nat.div_mul_cancel (Nat.dvd_lcm_left (p.denom:ℕ) q.denom)
  have hq : ((n/(q.denom:ℕ):ℕ):ℝ)=n/(q.denom:ℝ) := by
    apply (eq_div_iff qp.ne').mpr
    exact_mod_cast Nat.div_mul_cancel (Nat.dvd_lcm_right (p.denom:ℕ) q.denom)
  apply Polynomial.funext; intro z
  change (C (1/(n:ℝ))*realDense (linearRows (a*(n/(p.denom:ℕ):ℕ)) (b*(n/(q.denom:ℕ):ℕ)) p.numer q.numer)).eval z=_
  rw [eval_mul,eval_C,dense_linear_eval]
  simp only [model,eval_add,eval_mul,eval_C,Int.cast_mul,Int.cast_natCast,hp,hq]
  field_simp

def scale (a : ℤ) (b : ℕ+) (p : RationalPolyRow) : RationalPolyRow :=
  ⟨linearRows a 0 p.numer [],b*p.denom⟩

theorem model_scale (a : ℤ) (b : ℕ+) (p : RationalPolyRow) :
    (scale a b p).model=C ((a:ℝ)/(b:ℝ))*p.model := by
  apply Polynomial.funext; intro z
  have bp : (0:ℝ)<b := by exact_mod_cast b.pos
  have dp : (0:ℝ)<p.denom := by exact_mod_cast p.denom.pos
  simp only [scale,model,eval_mul,eval_C,dense_linear_eval,PNat.mul_coe,Nat.cast_mul,Int.cast_zero,zero_mul,add_zero]
  field_simp

def mul (p q : RationalPolyRow) : RationalPolyRow :=
  ⟨packedDenseProduct p.numer q.numer,p.denom*q.denom⟩

theorem model_mul (p q : RationalPolyRow) : (mul p q).model=p.model*q.model := by
  simp only [mul,model,PNat.mul_coe,Nat.cast_mul,real_packed_dense_product,one_div,mul_inv, map_mul]
  ring

def term (h : ℕ) (a : ℤ) (b : ℕ+) : RationalPolyRow := ⟨List.replicate h 0++[a],b⟩

def shift (k : ℕ) (p : RationalPolyRow) : RationalPolyRow :=
  ⟨List.replicate k 0++p.numer,p.denom⟩

private theorem shift_dense (a : List ℤ) (k : ℕ) :
    realDense (List.replicate k 0++a)=X^k*realDense a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ,List.cons_append,show realDense (0::(List.replicate k 0++a))=
      X*realDense (List.replicate k 0++a) by simp [realDense,densePoly],ih,pow_succ]; ring

theorem model_shift (k : ℕ) (p : RationalPolyRow) : (shift k p).model=X^k*p.model := by
  simp only [shift,model,shift_dense]; ring

theorem model_term (h : ℕ) (a : ℤ) (b : ℕ+) : (term h a b).model=C ((a:ℝ)/(b:ℝ))*X^h := by
  simp only [term,model,shift_dense]
  have c : realDense [a]=C (a:ℝ) := by simp [realDense,densePoly]
  simp only [c,div_eq_mul_inv,one_mul,map_mul]
  ring

def diff (k : ℕ) (p : RationalPolyRow) : RationalPolyRow := ⟨powerDerivative^[k] p.numer,p.denom⟩

theorem model_diff (k : ℕ) (p : RationalPolyRow) : (diff k p).model=derivative^[k] p.model := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',← ih]
    simp only [diff,model,Function.iterate_succ_apply',powerDerivative_real,derivative_C_mul]

def beta (p q : RationalPolyRow) : RationalPolyRow :=
  let t := betaDense p.numer q.numer
  ⟨t.2,⟨t.1,(betaDense_pos ..)⟩*p.denom*q.denom⟩

theorem model_beta (p q : RationalPolyRow) :
    (beta p q).model=betaProduct p.model q.model := by
  rw [model,model,model,beta_constants]
  simp only [beta,PNat.mul_coe,Nat.cast_mul]
  rw [betaDense_real,← mul_assoc,← map_mul]
  congr 2
  have bp : (0:ℝ)<(betaDense p.numer q.numer).1 := by exact_mod_cast betaDense_pos p.numer q.numer
  have pp : (0:ℝ)<p.denom := by exact_mod_cast p.denom.pos
  have qp : (0:ℝ)<q.denom := by exact_mod_cast q.denom.pos
  field_simp
  change _=(((betaDense p.numer q.numer).1*(p.denom:ℕ):ℕ):ℝ)
  rw [Nat.cast_mul]

def drop (k : ℕ) (p : RationalPolyRow) : RationalPolyRow := ⟨p.numer.drop k,p.denom⟩

theorem model_drop_coeff (k : ℕ) (p : RationalPolyRow) (i : ℕ) :
    ((drop k p).model).coeff i=p.model.coeff (k+i) := by
  simp [drop,model,realDense,coeff_C_mul,coeff_map,dense_coeff,List.getElem?_drop]

def weighted (a b : ℕ) (p q : RationalPolyRow) : RationalPolyRow :=
  drop (a+b) (beta (shift a p) (shift b q))

theorem model_weighted (a b : ℕ) (p q : RationalPolyRow) :
    (weighted a b p q).model=weightedBeta a b p.model q.model := by
  ext i
  rw [weighted,model_drop_coeff,model_beta,model_shift,model_shift,← weighted_beta_clear,
    mul_comm (X ^ (a+b)),coeff_mul_X_pow']
  simp

def sumRows (f : ℕ → RationalPolyRow) : ℕ → RationalPolyRow
  | 0 => zero
  | k+1 => linear 1 1 (sumRows f k) (f k)

theorem model_sum (f : ℕ → RationalPolyRow) (n : ℕ) :
    (sumRows f n).model=∑ i ∈ Finset.range n, (f i).model := by
  induction n with
  | zero => simp [sumRows]
  | succ n ih => simp [sumRows,model_linear,ih,Finset.sum_range_succ]

end RationalPolyRow
end CentralUnimodality.PolynomialTrial
