module

public import CentralUnimodality.CurvePerturbation

/-! Nonvanishing of each individual Dyck alternant in the diagonal
coinvariant quotient, for every semilength. -/
@[expose] public section

namespace CentralUnimodality.Polarization
open Polynomial Matrix
variable {n : ℕ}

private theorem distinct_orders (s a : Fin n → ℕ) (hs : Function.Injective s)
    (σ : Perm n) (hf : ∀ i, s i ≤ (σ i:ℕ)) : (orderMatrix 1 s a).det ≠ 0 := by
  let f := fun i => (⟨s i,lt_of_le_of_lt (hf i) (σ i).isLt⟩ : Fin n)
  have hi : Function.Injective f := fun i j h => hs (congrArg Fin.val h)
  let e := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hi)
  have he : orderMatrix 1 s a = (1 : Matrix (Fin n) (Fin n) ℚ).submatrix e id := by
    ext i j
    simp only [orderMatrix,of_apply,one_pow,mul_one,coeff_X_pow,submatrix_apply]
    change _ = (1 : Matrix (Fin n) (Fin n) ℚ) (e i) j
    have hh : e i=j ↔ (j:ℕ)=s i := ⟨fun h => (congrArg Fin.val h).symm,fun h => Fin.ext h.symm⟩
    by_cases hij : e i=j
    · simp [Matrix.one_apply,hij,hh.mp hij]
    · have hn : (j:ℕ) ≠ s i := fun h => hij (hh.mpr h)
      simp [hij,hn]
  rw [he,Matrix.det_permute,Matrix.det_one,mul_one]
  exact_mod_cast ((Equiv.Perm.sign e).isUnit.ne_zero)

/-- A permutation of dominating slots and distinct pairs of orders and powers
suffice for a rational curve with nonzero coefficient determinant. -/
theorem curve_nonsingular (s a : Fin n → ℕ) (hp : Function.Injective fun i => (s i,a i))
    (σ : Perm n) (hf : ∀ i, s i ≤ (σ i:ℕ)) :
    ∃ U : Polynomial ℚ, U.eval 0=1 ∧ (orderMatrix U s a).det ≠ 0 := by
  classical
  by_cases hs : Function.Injective s
  · exact ⟨1,by simp,distinct_orders s a hs σ hf⟩
  · obtain ⟨V,_,hV⟩ := curve_nonsingular (fun i => s i+groupIndex s σ i) (groupIndex s σ)
      (newOrders_distinct s σ) σ (groupIndex_slots hf)
    exact perturbation_step s a hp σ V hV
termination_by (∑ i, (σ i:ℕ)) - ∑ i, s i
decreasing_by
  have hb := Finset.sum_le_sum (s := Finset.univ) fun i _ => groupIndex_slots hf i
  have hh := groupIndex_progress hs σ
  rw [Finset.sum_add_distrib] at hb ⊢
  omega

/-- The slots condition and pairwise distinction are also necessary. -/
theorem curve_nonsingular_iff (s a : Fin n → ℕ) :
    (∃ U : Polynomial ℚ, U.eval 0=1 ∧ (orderMatrix U s a).det ≠ 0) ↔
      (Function.Injective fun i => (s i,a i)) ∧ FitsSlots s := by
  constructor
  · rintro ⟨U,_,hU⟩
    constructor
    · intro i j he
      by_contra hne
      apply hU (Matrix.det_zero_of_row_eq hne ?_)
      ext k
      have h : s i=s j ∧ a i=a j := Prod.ext_iff.mp he
      simp only [orderMatrix,Matrix.of_apply,h.1,h.2]
    · rw [Matrix.det_apply] at hU
      obtain ⟨σ,_,hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hU
      have hn : (∏ i, orderMatrix U s a (σ i) i) ≠ 0 := by
        intro hz; exact hs (by rw [hz,smul_zero])
      refine ⟨σ.symm,fun i => ?_⟩
      have hi := Finset.prod_ne_zero_iff.mp hn (σ.symm i) (Finset.mem_univ _)
      by_contra hf
      simp [orderMatrix,Polynomial.coeff_X_pow_mul',hf] at hi
  · rintro ⟨hp,σ,hf⟩
    exact curve_nonsingular s a hp σ hf

theorem dyck_curve_nonsingular {w : List Bool} (hw : w ∈ dycks n) :
    ∃ U : Polynomial ℚ, U.eval 0=1 ∧
      (curveMatrix U (dyckAreaEntry hw) (dinvEntry (dyckAreaEntry hw))).det ≠ 0 := by
  obtain ⟨σ,hf⟩ := dyck_orders_fit hw
  obtain ⟨U,hU,hD⟩ := curve_nonsingular _ _ (entry_pairs_injective (dyckAreaEntry hw)) σ hf
  exact ⟨U,hU,by simpa [curveMatrix,orderMatrix,Nat.add_comm] using hD⟩

/-- The individual quotient class is nonzero in its area/dinv bidegree. -/
theorem dyckClass_ne_zero {w : List Bool} (hw : w ∈ dycks n) : dyckClass hw ≠ 0 := by
  obtain ⟨U,_,hD⟩ := dyck_curve_nonsingular hw
  intro hz
  have he := quotientProbe_alternant U (dyckAreaEntry hw) (dinvEntry (dyckAreaEntry hw))
  rw [show (relations n).mkQ (alternant _ _) = dyckClass hw from rfl,hz,map_zero] at he
  have hc : (Fintype.card (Perm n):ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact (mul_ne_zero hc hD) he.symm

end CentralUnimodality.Polarization
