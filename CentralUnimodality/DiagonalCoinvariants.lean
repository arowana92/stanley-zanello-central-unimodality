module

public import CentralUnimodality.DiagonalPolarization
import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.LinearAlgebra.Quotient.Basic

/-! Reflected dimensions of the alternating diagonal coinvariants and
their implication for the ordinary Dyck input after specialization. -/
@[expose] public section

namespace CentralUnimodality.Polarization
open MvPolynomial

variable {n : ℕ}

/-- Alternating polynomials for simultaneous permutation of the variable pairs. -/
noncomputable def alternating (n : ℕ) : Submodule ℚ (Poly n) where
  carrier := {p | ∀ σ : Equiv.Perm (Fin n), rename (reindex σ) p = (σ.sign:ℤ) • p}
  zero_mem' := by simp
  add_mem' := by intro p q hp hq σ; rw [map_add,hp σ,hq σ,smul_add]
  smul_mem' := by intro r p hp σ; rw [map_smul,hp σ,smul_comm]

private theorem move_alternating (a b : Bool) {p : Poly n} (hp : p ∈ alternating n) :
    move a b p ∈ alternating n := by
  intro σ
  rw [← move_rename,hp σ,map_zsmul]

noncomputable def relations (n : ℕ) : Submodule ℚ (Poly n) := (invariantIdeal n).restrictScalars ℚ

noncomputable def coinvariantMove (a b : Bool) : Module.End ℚ (Poly n ⧸ relations n) :=
  (relations n).mapQ (relations n) (move a b).toLinearMap fun _ hp => move_ideal a b hp

/-- The image of the alternating polynomials of bidegree (k,d-k) in the
quotient by the ideal of positive-degree simultaneous invariants. -/
noncomputable def coinvariantSpace (n d k : ℕ) : Submodule ℚ (Poly n ⧸ relations n) :=
  (bidegreeSpace n d k ⊓ alternating n).map (relations n).mkQ

noncomputable def coinvariantOperators (n d : ℕ) : WeightOperators d (Poly n ⧸ relations n) where
  space := coinvariantSpace n d
  raise := coinvariantMove false true
  lower := coinvariantMove true false
  raise_mem := by
    rintro k _ ⟨p,⟨hp,ha⟩,rfl⟩
    exact ⟨_,⟨(polynomialOperators n d).raise_mem k p hp,move_alternating false true ha⟩,rfl⟩
  lower_mem := by
    rintro k _ ⟨p,⟨hp,ha⟩,rfl⟩
    exact ⟨_,⟨(polynomialOperators n d).lower_mem k p hp,move_alternating true false ha⟩,rfl⟩
  lower_zero := by
    rintro _ ⟨p,⟨hp,_⟩,rfl⟩
    change (relations n).mkQ (move true false p) = 0
    rw [show move true false p = 0 from (polynomialOperators n d).lower_zero p hp,map_zero]
  commutator := by
    rintro k _ ⟨p,⟨hp,_⟩,rfl⟩
    change (relations n).mkQ (move false true (move true false p)) =
      (relations n).mkQ (move true false (move false true p)) + (2*(k:ℚ)-d) • (relations n).mkQ p
    rw [← map_smul,← map_add]
    exact congrArg (relations n).mkQ ((polynomialOperators n d).commutator k p hp)

private theorem total_weight (m : (Bool × Fin n) →₀ ℕ) :
    Finsupp.weight (degree false) m + Finsupp.weight (degree true) m =
      (Finsupp.weight (fun _ : Bool × Fin n => (1:ℕ)) m:ℤ) := by
  simp only [Finsupp.weight_apply,Finsupp.sum,Nat.cast_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  rintro ⟨b,i⟩ _
  cases b <;> simp [degree,column]

private theorem bidegree_homogeneous (n d k : ℕ) :
    bidegreeSpace n d k ≤ weightedHomogeneousSubmodule ℚ (fun _ => (1:ℕ)) d := by
  intro p hp m hm
  have h := total_weight m
  rw [hp.1 hm,hp.2 hm] at h
  omega

instance finite_coinvariantSpace (n d k : ℕ) : FiniteDimensional ℚ (coinvariantSpace n d k) := by
  let W := weightedHomogeneousSubmodule ℚ (fun _ : Bool × Fin n => (1:ℕ)) d
  have : Module.Finite ℚ W := Module.Finite.iff_fg.mpr
    (weightedHomogeneousSubmodule_fg _ (fun _ => 1) (by simp) d)
  let L := Submodule.inclusion ((inf_le_left : bidegreeSpace n d k ⊓ alternating n ≤ _).trans
    (bidegree_homogeneous n d k))
  have : FiniteDimensional ℚ ↥(bidegreeSpace n d k ⊓ alternating n) :=
    FiniteDimensional.of_injective L (Submodule.inclusion_injective _)
  unfold coinvariantSpace
  infer_instance

theorem coinvariant_reflected {n d i j : ℕ} (hij : i ≤ j) (hs : i+j ≤ d) :
    Module.finrank ℚ (coinvariantSpace n d i) ≤ Module.finrank ℚ (coinvariantSpace n d j) := by
  have : FiniteDimensional ℚ ((coinvariantOperators n d).space j) := finite_coinvariantSpace n d j
  exact (coinvariantOperators n d).reflected_finrank hij hs

private theorem distinct_exponents {p : Poly n} (hp : p ∈ alternating n)
    (m : (Bool × Fin n) →₀ ℕ) (hm : p.coeff m ≠ 0) :
    Function.Injective (fun i : Fin n => (m (false,i),m (true,i))) := by
  classical
  intro i j hij
  by_contra hne
  let σ := Equiv.swap i j
  have hi : Function.Injective (reindex σ) := ((Equiv.refl Bool).prodCongr σ).injective
  have hx (b : Bool) : m (b,i) = m (b,j) := by
    cases b
    · exact congrArg Prod.fst hij
    · exact congrArg Prod.snd hij
  have hfix : m.mapDomain (reindex σ) = m := by
    ext ⟨b,z⟩
    have h := Finsupp.mapDomain_apply_of_injective hi m (b,σ z)
    have hσ : reindex σ (b,σ z) = (b,z) := by simp [reindex,σ]
    rw [hσ] at h
    rw [h]
    by_cases h₁ : z=i
    · subst z; simpa [σ] using (hx b).symm
    by_cases h₂ : z=j
    · subst z; simpa [σ] using hx b
    · rw [show σ z = z from Equiv.swap_apply_of_ne_of_ne h₁ h₂]
  have h := coeff_rename_mapDomain (reindex σ) hi p m
  rw [hp σ,hfix,show σ.sign = -1 from Equiv.Perm.sign_swap hne] at h
  simp only [Units.val_neg,Units.val_one,neg_smul,one_smul,coeff_neg] at h
  exact hm (by linarith)

theorem alternating_degree_cutoff {d k : ℕ} {p : Poly n}
    (hb : p ∈ bidegreeSpace n d k) (ha : p ∈ alternating n) (hp : p ≠ 0) :
    ⌈dyckLower n⌉₊ ≤ d := by
  classical
  obtain ⟨m,hm⟩ : ∃ m, p.coeff m ≠ 0 := by contrapose! hp; ext m; exact hp m
  let g := fun i : Fin n => (m (false,i),m (true,i))
  have hg : Function.Injective g := distinct_exponents ha m hm
  have h := degree_sum_lower (Finset.univ.image g)
  rw [Finset.card_image_of_injective _ hg,Finset.card_univ,Fintype.card_fin,
      Finset.sum_image (fun _ _ _ _ he => hg he)] at h
  have he := bidegree_homogeneous n d k hb hm
  change Finsupp.weight (fun _ => (1:ℕ)) m = d at he
  rw [Finsupp.weight_apply,Finsupp.sum_fintype _ _ (by simp),Fintype.sum_prod_type,Fintype.sum_bool] at he
  simp only [nsmul_eq_mul,mul_one] at he
  apply Nat.ceil_le.mpr
  convert h using 1
  dsimp [g]
  rw [Finset.sum_add_distrib,← he]
  ac_rfl

theorem coinvariantSpace_eq_bot {d k : ℕ} (hd : d < ⌈dyckLower n⌉₊) : coinvariantSpace n d k = ⊥ := by
  apply le_antisymm _ bot_le
  rintro _ ⟨p,⟨hb,ha⟩,rfl⟩
  have hp : p=0 := by by_contra hn; exact (Nat.not_le_of_gt hd) (alternating_degree_cutoff hb ha hn)
  simp [hp]

/-- The univariate specialization of the alternating coinvariant Hilbert
series is the only ordinary Dyck input here. -/
def DyckHilbertSpecialization : Prop := ∀ n, ∃ degrees : Finset ℕ, ∀ k,
  (dyckPoly n).coeff k = ∑ d ∈ degrees, Module.finrank ℚ (coinvariantSpace n d k)

theorem dyck_comparisons_of_hilbert (hh : DyckHilbertSpecialization) : DyckComparisons := by
  intro n i j hij hs
  obtain ⟨degrees,h⟩ := hh n
  rw [h i,h j]
  apply Finset.sum_le_sum
  intro d _
  by_cases hd : d < ⌈dyckLower n⌉₊
  · rw [coinvariantSpace_eq_bot hd,finrank_bot]
    exact Nat.zero_le _
  · exact coinvariant_reflected hij.le (by omega)

theorem conjecture34_of_hilbert_and_midpoints (hh : DyckHilbertSpecialization)
    (hm : ∀ n ≥ 96, ∀ δ ≤ 1, CentralToMidpoint n δ) : Conjecture34 :=
  conjecture34_of_comparisons_and_midpoints (dyck_comparisons_of_hilbert hh) hm

end CentralUnimodality.Polarization
