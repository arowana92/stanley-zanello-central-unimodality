module

public import CentralUnimodality.DyckCurveWords
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Interval.Finset.Nat

/-! Binomial interpolation separates rows having the same initial order.
The assigned new orders still fit the original permutation of slots. -/
@[expose] public section

namespace CentralUnimodality.Polarization
open Matrix
variable {n : ℕ}

/-- Row orders and powers are separate data during the induction. -/
noncomputable def orderMatrix (U : Polynomial ℚ) (s a : Fin n → ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => ((Polynomial.X:Polynomial ℚ)^(s i) * U^(a i)).coeff (j:ℕ)

def orderGroup (s : Fin n → ℕ) (i : Fin n) := Finset.univ.filter fun j => s j=s i

def groupIndex (s : Fin n → ℕ) (σ : Perm n) (i : Fin n) :=
  ((orderGroup s i).filter fun j => σ j < σ i).card

theorem groupIndex_lt (s : Fin n → ℕ) (σ : Perm n) (i : Fin n) :
    groupIndex s σ i < (orderGroup s i).card := by
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset (Finset.filter_subset ..)).mpr
  exact ⟨i,by simp [orderGroup],by simp⟩

private theorem groupIndex_strict {s : Fin n → ℕ} {σ : Perm n} {i j : Fin n}
    (he : s i=s j) (hlt : σ i < σ j) : groupIndex s σ i < groupIndex s σ j := by
  apply Finset.card_lt_card
  have sub : ((orderGroup s i).filter fun k => σ k < σ i) ⊆
      ((orderGroup s j).filter fun k => σ k < σ j) := by
    intro k hk
    simp [orderGroup,he] at hk ⊢
    exact ⟨hk.1,lt_trans hk.2 hlt⟩
  exact (Finset.ssubset_iff_of_subset sub).mpr ⟨i,by simp [orderGroup,he,hlt],by simp⟩

theorem groupIndex_slots {s : Fin n → ℕ} {σ : Perm n} (hf : ∀ i, s i ≤ (σ i:ℕ)) (i : Fin n) :
    s i + groupIndex s σ i ≤ (σ i:ℕ) := by
  let G := (orderGroup s i).filter fun j => σ j < σ i
  have h := Finset.card_le_card_of_injOn (s := G) (t := Finset.Ico (s i) (σ i:ℕ))
    (fun j => (σ j:ℕ)) (by
      intro j hj
      simp [G,orderGroup] at hj
      exact Finset.mem_Ico.mpr ⟨hj.1 ▸ hf j,hj.2⟩)
    (fun _ _ _ _ h => σ.injective (Fin.ext h))
  change groupIndex s σ i ≤ _ at h
  rw [Nat.card_Ico] at h
  have := hf i
  omega

theorem newOrders_distinct (s : Fin n → ℕ) (σ : Perm n) :
    Function.Injective (fun i => (s i+groupIndex s σ i,groupIndex s σ i)) := by
  intro i j h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp only at h₁ h₂
  have he : s i=s j := by omega
  apply σ.injective
  rcases lt_trichotomy (σ i) (σ j) with h|h|h
  · exact False.elim ((groupIndex_strict he h).ne h₂)
  · exact h
  · exact False.elim ((groupIndex_strict he.symm h).ne h₂.symm)

theorem groupIndex_progress {s : Fin n → ℕ} (hs : ¬Function.Injective s) (σ : Perm n) :
    0 < ∑ i, groupIndex s σ i := by
  classical
  simp only [Function.Injective] at hs
  push Not at hs
  obtain ⟨i,j,he,hne⟩ := hs
  have hn : σ i ≠ σ j := fun h => hne (σ.injective h)
  apply (Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mpr
  rcases lt_or_gt_of_ne hn with h|h
  · exact ⟨j,Finset.mem_univ _,lt_of_le_of_lt (Nat.zero_le _) (groupIndex_strict he h)⟩
  · exact ⟨i,Finset.mem_univ _,lt_of_le_of_lt (Nat.zero_le _) (groupIndex_strict he.symm h)⟩

/-- Evaluation of binomial polynomials of successive degrees on distinct
nonnegative integers has invertible matrix over the rationals. -/
theorem binomial_det_ne_zero {g : ℕ} (v : Fin g → ℕ) (hv : Function.Injective v) :
    (Matrix.of fun i j : Fin g => (Nat.choose (v i) j:ℚ)).det ≠ 0 := by
  let A : Matrix (Fin g) (Fin g) ℚ := Matrix.of fun i j => Nat.choose (v i) j
  let u := fun i => (v i:ℚ)
  have hi : Function.Injective u := fun i j h => hv ((Nat.cast_inj (R := ℚ)).mp h)
  have h := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde u
    (fun i => descPochhammer ℚ i) (fun i => descPochhammer_natDegree ℚ i) (fun i => monic_descPochhammer ℚ i)
  have he : Matrix.of (fun i j : Fin g => (descPochhammer ℚ j).eval (u i)) =
      A * diagonal (fun j : Fin g => (Nat.factorial j:ℚ)) := by
    ext i j
    simp [A,u,descPochhammer_eval_eq_descFactorial,Nat.descFactorial_eq_factorial_mul_choose,mul_comm]
  rw [he,Matrix.det_mul] at h
  change A.det ≠ 0
  intro hz
  rw [hz,zero_mul] at h
  exact Matrix.det_vandermonde_ne_zero_iff.mpr hi h

/-- A row combination supported in the group of i isolates coefficient h
among the first g binomial coefficients. -/
theorem group_interpolation (s a : Fin n → ℕ) (hp : Function.Injective fun i => (s i,a i))
    (i : Fin n) {h : ℕ} (hh : h < (orderGroup s i).card) :
    ∃ c : Fin n → ℚ, (∀ j, s j ≠ s i → c j=0) ∧
      ∀ k < (orderGroup s i).card, (∑ j, c j*(Nat.choose (a j) k:ℚ)) = if k=h then 1 else 0 := by
  classical
  let G := orderGroup s i
  let e := (G.orderIsoOfFin rfl).toEquiv
  let v := fun j : Fin G.card => a (e j).val
  have hi : Function.Injective v := by
    intro j k he
    apply e.injective
    apply Subtype.ext
    apply hp
    have hj := (e j).property
    have hk := (e k).property
    have hj' := (Finset.mem_filter.mp hj).2
    have hk' := (Finset.mem_filter.mp hk).2
    exact Prod.ext (hj'.trans hk'.symm) he
  let B : Matrix (Fin G.card) (Fin G.card) ℚ := Matrix.of fun j k => Nat.choose (v j) k
  have hB := Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr (binomial_det_ne_zero v hi))
  let l : Fin G.card := ⟨h,hh⟩
  let c := fun j : Fin n => if hj : j ∈ G then B⁻¹ l (e.symm ⟨j,hj⟩) else 0
  refine ⟨c,fun j hj => by simp [c,G,orderGroup,hj],?_⟩
  intro k hk
  let b : Fin G.card := ⟨k,hk⟩

  calc
    _ = ∑ j ∈ G, c j*(Nat.choose (a j) k:ℚ) := by
      symm; apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      simp [c,hj]
    _ = ∑ j : G, c j.val*(Nat.choose (a j.val) k:ℚ) := (Finset.sum_attach _ _).symm
    _ = ∑ j : Fin G.card, B⁻¹ l j * B j b := by
      rw [← Equiv.sum_comp e]
      apply Finset.sum_congr rfl
      intro j _
      simp [c,(e j).property,B,v,b]
    _ = _ := by
      rw [← Matrix.mul_apply,hB]
      simp [Matrix.one_apply,l,b,eq_comm]

end CentralUnimodality.Polarization
