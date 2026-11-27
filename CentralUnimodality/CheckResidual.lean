module

public import CentralUnimodality.PackedResidual

/-! Executable checker for exported integer arrays. Its decisions are exact
and independent of the code that produced the arrays. -/
@[expose] public section

namespace CentralUnimodality

namespace Residual

open Polynomial

noncomputable def rowPolynomial : List ℤ → Polynomial ℤ
  | [] => 0
  | a::v => C a + X*rowPolynomial v

def evaluateRow (B : ℤ) : List ℤ → ℤ
  | [] => 0
  | a::v => a+B*evaluateRow B v

theorem eval_rowPolynomial (B : ℤ) (v : List ℤ) :
    (rowPolynomial v).eval B = evaluateRow B v := by
  induction v with
  | nil => simp [rowPolynomial,evaluateRow]
  | cons a v ih => simp [rowPolynomial,evaluateRow,ih]

theorem coeff_rowPolynomial (v : List ℤ) (i : ℕ) : (rowPolynomial v).coeff i = v[i]?.getD 0 := by
  induction v generalizing i with
  | nil => simp [rowPolynomial]
  | cons a v ih =>
    rw [rowPolynomial,coeff_add,coeff_C]
    cases i <;> simp [coeff_X_mul,ih]

def magnitude : List ℤ → ℕ
  | [] => 0
  | a::v => max a.natAbs (magnitude v)

theorem row_bound (v : List ℤ) (i : ℕ) : |(rowPolynomial v).coeff i| ≤ (magnitude v:ℤ) := by
  rw [coeff_rowPolynomial]
  induction v generalizing i with
  | nil => simp [magnitude]
  | cons a v ih =>
    cases i with
    | zero => simp [magnitude]
    | succ i =>
      simp only [List.getElem?_cons_succ]
      exact (ih i).trans (by exact_mod_cast le_max_right a.natAbs (magnitude v))

/-- Blocks are low degree first. L may be shorter than the arrays. -/
def check (B s : ℤ) (L : ℕ) (F R V E : List ℤ) : Bool :=
  decide (0 < B ∧ 0 ≤ s ∧ s*magnitude F+(L:ℤ)*magnitude R*magnitude V+magnitude E < B ∧
    (s*evaluateRow B F-evaluateRow B R*evaluateRow B V-evaluateRow B E) % B^L = 0)

theorem check_sound {B s : ℤ} {L : ℕ} {F R V E : List ℤ} (h : check B s L F R V E = true) :
    ∀ i < L, s*(rowPolynomial F).coeff i-((rowPolynomial R)*(rowPolynomial V)).coeff i = (rowPolynomial E).coeff i := by
  obtain ⟨hB,hs,hsize,hc⟩ := of_decide_eq_true h
  apply packed_residual_coefficients hB hs _ _ _ _ (fun i _ => row_bound F i)
    (fun i _ => row_bound R i) (fun i _ => row_bound V i) (fun i _ => row_bound E i) hsize
  simpa only [eval_rowPolynomial] using Int.dvd_of_emod_eq_zero hc

theorem checked_bound {B s : ℤ} {L : ℕ} {F R V E : List ℤ}
    (h : check B s L F R V E = true) {e : ℕ} (he : magnitude E ≤ e) :
    ∀ i < L, |s*(rowPolynomial F).coeff i-((rowPolynomial R)*(rowPolynomial V)).coeff i| ≤ (e:ℤ) := by
  intro i hi
  rw [check_sound h i hi]
  exact (row_bound E i).trans (by exact_mod_cast he)

end Residual

end CentralUnimodality
