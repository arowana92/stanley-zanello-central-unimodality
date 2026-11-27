module

public import CentralUnimodality.DyckWeightOperators
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.RingTheory.Derivation.Lie

/-! Polarizations of the two sets of variables in diagonal coinvariants. -/
@[expose] public section

namespace CentralUnimodality.Polarization
open MvPolynomial

abbrev Poly (n : ℕ) := MvPolynomial (Bool × Fin n) ℚ
variable {n : ℕ}

noncomputable def move (a b : Bool) : Derivation ℚ (Poly n) (Poly n) :=
  mkDerivation ℚ fun z => if z.1=b then X (a,z.2) else 0

@[simp] theorem move_X (a b c : Bool) (i : Fin n) :
    move a b (X (c,i)) = if c=b then X (a,i) else 0 := mkDerivation_X ℚ _ _

theorem commutator :
    ⁅move (n := n) false true,move (n := n) true false⁆ = move false false - move true true := by
  apply derivation_ext
  rintro ⟨c,i⟩
  cases c <;> simp [Derivation.commutator_apply]

private theorem sum_deriv_apply {ι : Type*} (s : Finset ι) (D : ι → Derivation ℚ (Poly n) (Poly n)) (p : Poly n) :
    (∑ i ∈ s, D i) p = ∑ i ∈ s, D i p := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih => simp [ih]

theorem move_apply (a b : Bool) (p : Poly n) :
    move a b p = ∑ i : Fin n, X (a,i)*pderiv (b,i) p := by
  classical
  let D : Fin n → Derivation ℚ (Poly n) (Poly n) := fun i => (X (a,i):Poly n) • pderiv (b,i)
  have he : move a b = ∑ i, D i := by
    apply derivation_ext
    rintro ⟨c,j⟩
    rw [sum_deriv_apply,move_X]
    by_cases hc : c=b
    · subst c
      simp [D,pderiv_X,Pi.single_apply,smul_eq_mul]
    · simp [D,pderiv_X,smul_eq_mul,hc]
  rw [he,sum_deriv_apply]
  rfl

def reindex (σ : Equiv.Perm (Fin n)) (z : Bool × Fin n) := (z.1,σ z.2)

theorem move_rename (a b : Bool) (σ : Equiv.Perm (Fin n)) (p : Poly n) :
    move a b (rename (reindex σ) p) = rename (reindex σ) (move a b p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [move]
  | add p q hp hq => simp [hp,hq]
  | mul_X p i h =>
    obtain ⟨c,j⟩ := i
    by_cases hc : c=b <;> simp [Derivation.leibniz,smul_eq_mul,reindex,hc,h]

theorem constant_move (a b : Bool) (p : Poly n) : constantCoeff (move a b p) = 0 := by
  rw [move_apply,map_sum]
  simp

def positiveInvariant (p : Poly n) : Prop :=
  constantCoeff p = 0 ∧ ∀ σ : Equiv.Perm (Fin n), rename (reindex σ) p = p

noncomputable def invariantIdeal (n : ℕ) : Ideal (Poly n) := Ideal.span {p | positiveInvariant p}

theorem move_ideal (a b : Bool) {p : Poly n} (hp : p ∈ invariantIdeal n) :
    move a b p ∈ invariantIdeal n := by
  change p ∈ Submodule.span (Poly n) {q | positiveInvariant q} at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    apply Ideal.subset_span
    exact ⟨constant_move a b p,fun σ => by rw [← move_rename,hp.2 σ]⟩
  | zero => simp
  | add f g _ _ hf hg => simpa using (invariantIdeal n).add_mem hf hg
  | smul f p hp ih =>
    rw [smul_eq_mul,Derivation.leibniz,smul_eq_mul,smul_eq_mul]
    exact (invariantIdeal n).add_mem ((invariantIdeal n).mul_mem_left _ ih)
      ((invariantIdeal n).mul_mem_right _ hp)

def column (b : Bool) (z : Bool × Fin n) : ℕ := if z.1=b then 1 else 0
def degree (b : Bool) (z : Bool × Fin n) : ℤ := column b z

private theorem weight_cast (b : Bool) (m : (Bool × Fin n) →₀ ℕ) :
    Finsupp.weight (degree b) m = (Finsupp.weight (column b) m:ℤ) := by
  simp [Finsupp.weight_apply,Finsupp.sum,degree]

private theorem eq_zero_of_negative {p : Poly n} {b : Bool} {l : ℤ}
    (hl : l < 0) (hp : p.IsWeightedHomogeneous (degree b) l) : p = 0 := by
  ext m
  change p.coeff m = 0
  by_contra hn
  have h := hp hn
  rw [weight_cast] at h
  omega

theorem move_degree (a b c : Bool) {p : Poly n} {l : ℤ} (hp : p.IsWeightedHomogeneous (degree c) l) :
    (move a b p).IsWeightedHomogeneous (degree c)
      (l+(if a=c then 1 else 0)-(if b=c then 1 else 0)) := by
  rw [move_apply]
  apply IsWeightedHomogeneous.sum
  intro i _
  have hh := hp.pderiv (i := (b,i)) (sub_add_cancel l (degree c (b,i)))
  convert (isWeightedHomogeneous_X (R := ℚ) (degree c) (a,i)).mul hh using 1
  by_cases ha : a=c <;> by_cases hb : b=c <;> simp [degree,column,ha,hb]
  ring

private theorem euler_column (b : Bool) {p : Poly n} {l : ℤ}
    (hp : p.IsWeightedHomogeneous (degree b) l) : move b b p = (l:ℚ) • p := by
  by_cases hl : 0 ≤ l
  · have he := Int.toNat_of_nonneg hl
    have hn : p.IsWeightedHomogeneous (column b) l.toNat := by
      intro m hm
      have h := hp hm
      rw [weight_cast] at h
      omega
    have h := hn.sum_weight_X_mul_pderiv
    rw [move_apply,← he,Int.cast_natCast,Nat.cast_smul_eq_nsmul ℚ]
    cases b <;> simpa [Fintype.sum_prod_type,Fintype.sum_bool,column] using h
  · rw [eq_zero_of_negative (by omega) hp,map_zero,smul_zero]

noncomputable def bidegreeSpace (n d k : ℕ) : Submodule ℚ (Poly n) :=
  weightedHomogeneousSubmodule ℚ (degree false) (k:ℤ) ⊓
  weightedHomogeneousSubmodule ℚ (degree true) ((d:ℤ)-k)

noncomputable def polynomialOperators (n d : ℕ) : WeightOperators d (Poly n) where
  space := bidegreeSpace n d
  raise := (move false true).toLinearMap
  lower := (move true false).toLinearMap
  raise_mem := by
    intro k p hp
    constructor
    · simpa using move_degree false true false hp.1
    · change (move false true p).IsWeightedHomogeneous _ _
      convert move_degree false true true hp.2 using 1
      simp
      ring
  lower_mem := by
    intro k p hp
    constructor
    · simpa using move_degree true false false hp.1
    · change (move true false p).IsWeightedHomogeneous _ _
      convert move_degree true false true hp.2 using 1
      simp
      ring
  lower_zero := by
    intro p hp
    apply eq_zero_of_negative (l := -1) (b := false) (by decide)
    simpa using move_degree true false false hp.1
  commutator := by
    intro k p hp
    have h := congrArg (fun (D : Derivation ℚ (Poly n) (Poly n)) => D p) (commutator (n := n))
    simp only [Derivation.commutator_apply,sub_apply,euler_column false hp.1,euler_column true hp.2,
      Int.cast_natCast,Int.cast_sub] at h
    apply eq_add_of_sub_eq'
    change move false true (move true false p) - move true false (move false true p) = _
    rw [h,← sub_smul]
    congr 1
    ring

end CentralUnimodality.Polarization
