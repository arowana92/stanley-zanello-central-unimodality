module

public import CentralUnimodality.MomentEquations

/-! Realize a table of Laurent columns as a bivariate formal series. The
finite convolutions and dilations below are exact at each moment order. -/
@[expose] public section

namespace CentralUnimodality

open PowerSeries

noncomputable def fromColumns (A : ℕ → PowerSeries ℚ) : MomentBiseries :=
  PowerSeries.mk (fun n => PowerSeries.mk (fun r => coeff n (A r)))

theorem momentColumn_fromColumns (r : ℕ) (A : ℕ → PowerSeries ℚ) :
    momentColumn r (fromColumns A) = A r := by
  apply PowerSeries.ext
  simp only [coeff_momentColumn, fromColumns, coeff_mk, implies_true]

theorem momentColumn_add (r : ℕ) (F G : MomentBiseries) :
    momentColumn r (F+G) = momentColumn r F + momentColumn r G := by
  apply PowerSeries.ext
  simp only [coeff_momentColumn, map_add, implies_true]

theorem momentColumn_sub (r : ℕ) (F G : MomentBiseries) :
    momentColumn r (F-G) = momentColumn r F - momentColumn r G := by
  apply PowerSeries.ext
  simp only [coeff_momentColumn, map_sub, implies_true]

theorem momentColumn_C (r : ℕ) (a : PowerSeries ℚ) : momentColumn r (C a) = C (coeff r a) := by
  apply PowerSeries.ext
  intro n
  rw [coeff_momentColumn, coeff_C, coeff_C]
  split <;> simp

theorem momentColumn_one (r : ℕ) : momentColumn r 1 = if r = 0 then 1 else 0 := by
  rw [← map_one (C (R := PowerSeries ℚ)), momentColumn_C, coeff_one]
  split <;> simp

theorem momentColumn_X_mul (r : ℕ) (F : MomentBiseries) :
    momentColumn r (X*F) = X*momentColumn r F := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [coeff_momentColumn]
  | succ n => simp [coeff_momentColumn, coeff_succ_X_mul]

namespace Laurent

def sumRange (f : ℕ → Laurent) : ℕ → Laurent
  | 0 => []
  | n+1 => add (sumRange f n) (f n)

theorem eval_sumRange (f : ℕ → Laurent) (n : ℕ) :
    eval (sumRange f n) = ∑ i ∈ Finset.range n, eval (f i) := by
  induction n with
  | zero => simp [sumRange,eval]
  | succ n ih => rw [sumRange, eval_add, ih, Finset.sum_range_succ]

def convolution (A B : ℕ → Laurent) (r : ℕ) : Laurent :=
  sumRange (fun i => mul (A i) (B (r-i))) (r+1)

theorem product_columns (F G : MomentBiseries) (a b : PowerSeries ℚ) (A B : ℕ → Laurent) (r : ℕ)
    (hF : ∀ i ≤ r, momentColumn i F = a*eval (A i))
    (hG : ∀ i ≤ r, momentColumn i G = b*eval (B i)) :
    momentColumn r (F*G) = a*b*eval (convolution A B r) := by
  rw [momentColumn_mul, convolution, eval_sumRange, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have := Finset.mem_range.mp hi
  rw [hF i (by omega), hG _ (by omega), eval_mul]
  ac_rfl

def shifted (b : MomentBase) (d : ℕ) (A : ℕ → Laurent) (r : ℕ) : Laurent :=
  sumRange (fun i => b.divided d (A (r-i)) i) (r+1)

theorem shifted_columns (b : MomentBase) (d : ℕ) (F : MomentBiseries) (A : ℕ → Laurent) (r : ℕ)
    (hF : ∀ i ≤ r, momentColumn i F = b.value*eval (A i)) :
    momentColumn r (rescale ((exp ℚ)^d) F) = b.value * eval (shifted b d A r) := by
  rw [momentColumn_rescale, shifted, eval_sumRange, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hF _ (Nat.sub_le ..), MomentBase.eval_divided]

def exponential (A : ℕ → Laurent) (r : ℕ) : Laurent :=
  sumRange (fun i => scaleShift (1/(i.factorial:ℚ)) 0 (A (r-i))) (r+1)

theorem exp_columns (F : MomentBiseries) (a : PowerSeries ℚ) (A : ℕ → Laurent) (r : ℕ)
    (hF : ∀ i ≤ r, momentColumn i F = a*eval (A i)) :
    momentColumn r (C (exp ℚ)*F) = a*eval (exponential A r) := by
  rw [momentColumn_mul, exponential, eval_sumRange, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [momentColumn_C, coeff_exp, hF _ (Nat.sub_le ..), eval_scaleShift, rootPower_zero]
  simp only [mul_one, Algebra.algebraMap_self_apply]
  ac_rfl

end Laurent

end CentralUnimodality
