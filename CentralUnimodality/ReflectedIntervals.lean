module

public import CentralUnimodality.IntervalClosure
public import Mathlib.Algebra.Polynomial.BigOperators

/-! Construct intervals from the reflected inequalities. Successive left-half
increments make intervals symmetric about e/2. Every coefficient still
unaccounted for lies on the right and supplies a singleton interval. -/
@[expose] public section

namespace CentralUnimodality

open Polynomial

private def increment (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => f 0
  | i+1 => f (i+1)-f i

private theorem increment_sum {f : ℕ → ℕ} (r : ℕ) (h : ∀ i < r, f i ≤ f (i+1)) :
    ∑ i ∈ Finset.range (r+1), increment f i = f r := by
  induction r with
  | zero => simp [increment]
  | succ r ih =>
    rw [Finset.sum_range_succ,ih (fun i hi => h i (by omega)),increment]
    have := h r (by omega)
    omega

private noncomputable def shells (f : ℕ → ℕ) (e : ℕ) : Polynomial ℕ :=
  ∑ a ∈ Finset.range (e/2+1), increment f a • intervalPoly a (e-2*a)

private theorem shells_good (f : ℕ → ℕ) (e : ℕ) : IntervalDecomposition (shells f e) e := by
  apply IntervalDecomposition.range
  intro a ha
  exact (IntervalDecomposition.single (by omega : (e:ℤ) ≤ 2*a+((e-2*a:ℕ):ℤ))).nsmul _

private theorem shells_coeff {P : Polynomial ℕ} {e : ℕ} (hr : ReflectedCoeffs P e) (k : ℕ) :
    (shells P.coeff e).coeff k = if k ≤ e then P.coeff (min k (e-k)) else 0 := by
  rw [shells,finsetSum_coeff]
  simp only [AddMonoidAlgebra.coeff_smul_apply,coeff_interval]
  simp only [nsmul_eq_mul]
  by_cases hk : k ≤ e
  · rw [ite_eq_left hk]
    let r := min k (e-k)
    have hr' : r ≤ e/2 := by dsimp [r]; omega
    have hmono (i : ℕ) (hi : i < r) : P.coeff i ≤ P.coeff (i+1) := hr i (i+1) (by omega) (by omega)
    rw [← increment_sum r hmono]
    calc
      _ = ∑ a ∈ Finset.range (e/2+1), if a < r+1 then increment P.coeff a else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        have := Finset.mem_range.mp ha
        dsimp only [r]
        split <;> split <;> first | omega | simp
      _ = _ := by
        rw [← Finset.sum_filter]
        congr 1
        ext i
        simp only [Finset.mem_filter,Finset.mem_range]
        omega
  · rw [ite_eq_right hk]
    apply Finset.sum_eq_zero
    intro i hi
    have := Finset.mem_range.mp hi
    rw [ite_eq_right (by omega : ¬ (i ≤ k ∧ k ≤ i+(e-2*i))),mul_zero]

theorem intervalDecomposition_of_reflected {P : Polynomial ℕ} {e : ℕ} (hr : ReflectedCoeffs P e) :
    IntervalDecomposition P e := by
  let F := shells P.coeff e
  let D := max e P.natDegree
  have hle (k : ℕ) : F.coeff k ≤ P.coeff k := by
    rw [show F = _ from rfl,shells_coeff hr]
    split
    next hk =>
      by_cases hmid : k ≤ e-k
      · simp [min_eq_left hmid]
      · rw [min_eq_right (by omega)]
        exact hr _ _ (by omega) (by omega)
    next => exact Nat.zero_le _
  let R (k : ℕ) := (P.coeff k-F.coeff k) • intervalPoly k 0
  have hR : IntervalDecomposition (∑ k ∈ Finset.range (D+1), R k) e := by
    apply IntervalDecomposition.range
    intro k _
    by_cases hk : e ≤ 2*k
    · exact (IntervalDecomposition.single (by omega : (e:ℤ) ≤ 2*k+(0:ℕ))).nsmul _
    · have hx : F.coeff k = P.coeff k := by
        rw [show F = _ from rfl,shells_coeff hr,ite_eq_left (by omega),min_eq_left (by omega)]
      simpa only [R,hx,Nat.sub_self,zero_smul] using IntervalDecomposition.zero (e:ℤ)
  have hrepr : P = F + ∑ k ∈ Finset.range (D+1), R k := by
    ext j
    rw [coeff_add,finsetSum_coeff]
    simp only [R,AddMonoidAlgebra.coeff_smul_apply,coeff_interval,Nat.add_zero]
    simp only [nsmul_eq_mul]
    by_cases hj : j ≤ D
    · rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr (by omega))]
      · simp [Nat.add_sub_of_le (hle j)]
      · intro i _ hi
        rw [ite_eq_right (by omega : ¬ (i ≤ j ∧ j ≤ i)),mul_zero]
    · have hd : P.natDegree < j := lt_of_le_of_lt (le_max_right ..) (lt_of_not_ge hj)
      have he : e < j := lt_of_le_of_lt (le_max_left ..) (lt_of_not_ge hj)
      rw [coeff_eq_zero_of_natDegree_lt hd,show F.coeff j = 0 by
        rw [show F = _ from rfl,shells_coeff hr,ite_eq_right (by omega)]]
      simp only [zero_add]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      have := Finset.mem_range.mp hi
      rw [ite_eq_right (by omega : ¬ (i ≤ j ∧ j ≤ i)),mul_zero]
  exact hrepr ▸ (shells_good P.coeff e).add hR

theorem intervalDecomposition_iff_reflected (P : Polynomial ℕ) (e : ℕ) :
    IntervalDecomposition P e ↔ ReflectedCoeffs P e :=
  ⟨IntervalDecomposition.reflected,intervalDecomposition_of_reflected⟩

end CentralUnimodality
