module

public import CentralUnimodality.PrefixInduction

/-! Coefficients and positive linear combinations of intervals with a lower
bound on the sum of their endpoints. -/
@[expose] public section

namespace CentralUnimodality

open Polynomial

theorem coeff_interval (a w k : ℕ) :
    (intervalPoly a w).coeff k = if a ≤ k ∧ k ≤ a+w then 1 else 0 := by
  simp only [intervalPoly,finsetSum_coeff,coeff_X_pow]
  by_cases h : a ≤ k ∧ k ≤ a+w
  · rw [ite_eq_left h,Finset.sum_eq_single_of_mem (k-a) (Finset.mem_range.mpr (by omega))]
    · rw [ite_eq_left (by omega)]
    · intro i _ hi
      simp [show k ≠ a+i by omega]
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro i hi
    have := Finset.mem_range.mp hi
    simp [show k ≠ a+i by omega]

theorem IntervalDecomposition.zero (e : ℤ) : IntervalDecomposition 0 e := ⟨[],by simp,by simp⟩

theorem IntervalDecomposition.add {P Q : Polynomial ℕ} {e : ℤ}
    (hP : IntervalDecomposition P e) (hQ : IntervalDecomposition Q e) : IntervalDecomposition (P+Q) e := by
  obtain ⟨a,rfl,ha⟩ := hP
  obtain ⟨b,rfl,hb⟩ := hQ
  refine ⟨a++b,by simp,?_⟩
  intro t ht
  exact (List.mem_append.mp ht).elim (ha t) (hb t)

theorem IntervalDecomposition.nsmul {P : Polynomial ℕ} {e : ℤ}
    (h : IntervalDecomposition P e) (n : ℕ) : IntervalDecomposition (n • P) e := by
  induction n with
  | zero => simpa only [zero_smul] using IntervalDecomposition.zero e
  | succ n ih => simpa only [succ_nsmul] using ih.add h

theorem IntervalDecomposition.single {a w : ℕ} {e : ℤ} (h : e ≤ 2*(a:ℤ)+w) :
    IntervalDecomposition (intervalPoly a w) e := ⟨[(a,w)],by simp,by simpa using h⟩

theorem IntervalDecomposition.range {f : ℕ → Polynomial ℕ} {e : ℤ} {n : ℕ}
    (h : ∀ i < n, IntervalDecomposition (f i) e) : IntervalDecomposition (∑ i ∈ Finset.range n, f i) e := by
  induction n with
  | zero => simpa only [Finset.range_zero,Finset.sum_empty] using IntervalDecomposition.zero e
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact (ih (fun i hi => h i (by omega))).add (h n (by omega))

theorem IntervalDecomposition.reflected {Q : Polynomial ℕ} {e : ℤ} (h : IntervalDecomposition Q e) :
    ReflectedCoeffs Q e := by
  obtain ⟨a,rfl,ha⟩ := h
  intro i j hij hcut
  induction a with
  | nil => simp
  | cons t a ih =>
    obtain ⟨v,w⟩ := t
    simp only [List.map_cons,List.sum_cons,coeff_add]
    apply add_le_add _ (ih (fun t ht => ha t (List.mem_cons_of_mem _ ht)))
    have he := ha (v,w) List.mem_cons_self
    simp only at he
    rw [coeff_interval,coeff_interval]
    split <;> split <;> omega

end CentralUnimodality
