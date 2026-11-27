module

public import CentralUnimodality.DyckCurveDetection
public import CentralUnimodality.DyckDiagonalSlices
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! A square curve-evaluation minor bounds the dimension of its actual
bigraded quotient space. Total dimension then suffices to turn all the
slice lower bounds into the ordinary Dyck Hilbert specialization. -/
@[expose] public section

namespace CentralUnimodality.Polarization
open Matrix
variable {n d k : ℕ}

/-- Literal paths of total degree d and area k. -/
def slicePaths (n d k : ℕ) : Finset (List Bool) :=
  ((dycks n).filter (fun w => dyckTotalDegree w=d)).filter (fun w => walkCorank w=k)

theorem card_slicePaths (n d k : ℕ) : (slicePaths n d k).card = dyckSliceCount n d k := by
  rw [slicePaths,Finset.card_filter,dyckSliceCount]

theorem slicePath_data (w : slicePaths n d k) :
    w.val ∈ dycks n ∧ dyckTotalDegree w.val=d ∧ walkCorank w.val=k := by
  have h := Finset.mem_filter.mp w.property
  exact ⟨(Finset.mem_filter.mp h.1).1,(Finset.mem_filter.mp h.1).2,h.2⟩

noncomputable def sliceClass (w : slicePaths n d k) : coinvariantSpace n d k :=
  ⟨dyckClass (slicePath_data w).1,by
    have h := dyckClass_bidegree (slicePath_data w).1
    simpa only [(slicePath_data w).2.1,(slicePath_data w).2.2] using h⟩

/-- Every occupied area/dinv bidegree contains a nonzero class. -/
theorem dyck_slice_finrank_pos (hw : 0 < dyckSliceCount n d k) :
    0 < Module.finrank ℚ (coinvariantSpace n d k) := by
  rw [← card_slicePaths,Finset.card_pos] at hw
  obtain ⟨w,hw⟩ := hw
  let v := sliceClass (⟨w,hw⟩ : slicePaths n d k)
  apply Module.finrank_pos_iff.mpr
  exact ⟨v,0,fun h => dyckClass_ne_zero _ (congrArg Subtype.val h)⟩

/-- Columns are paths, rows are rational test curves. -/
noncomputable def sliceCurveMatrix (U : slicePaths n d k → Polynomial ℚ) :
    Matrix (slicePaths n d k) (slicePaths n d k) ℚ := Matrix.of fun i j =>
  let a := dyckAreaEntry (slicePath_data j).1
  (curveMatrix (U i) a (dinvEntry a)).det

theorem slice_independent_of_minor (U : slicePaths n d k → Polynomial ℚ)
    (hU : (sliceCurveMatrix U).det ≠ 0) : LinearIndependent ℚ (sliceClass (n := n) (d := d) (k := k)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have he (i : slicePaths n d k) :
      (Fintype.card (Perm n):ℚ) * ((sliceCurveMatrix U).mulVec g i) = 0 := by
    let f := (quotientProbe (U i)).comp (coinvariantSpace n d k).subtype
    have h := congrArg f hg
    rw [map_sum,map_zero] at h
    simp only [f,map_smul,LinearMap.comp_apply,Submodule.subtype_apply,sliceClass,dyckClass,
      quotientProbe_alternant,smul_eq_mul] at h
    rw [Matrix.mulVec,dotProduct,Finset.mul_sum]
    convert h using 1
    apply Finset.sum_congr rfl
    intro j _
    unfold sliceCurveMatrix
    simp only [Matrix.of_apply]
    ring
  have hcard : (Fintype.card (Perm n):ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr hU))
  have hz : g=0 := hinj (by
    rw [Matrix.mulVec_zero]
    exact funext (fun i => (mul_eq_zero.mp (he i)).resolve_left hcard))
  simp [hz]

theorem dyck_slice_le_of_minor (U : slicePaths n d k → Polynomial ℚ) (hU : (sliceCurveMatrix U).det ≠ 0) :
    dyckSliceCount n d k ≤ Module.finrank ℚ (coinvariantSpace n d k) := by
  simpa [card_slicePaths] using (slice_independent_of_minor U hU).fintype_card_le_finrank

/-- Determinants on all slices of occupied total degrees. -/
def DyckCurveMinors : Prop := ∀ n d, d ∈ (dycks n).image dyckTotalDegree → ∀ k,
  ∃ U : slicePaths n d k → Polynomial ℚ, (sliceCurveMatrix U).det ≠ 0

/-- A Catalan bound on the sum of the dimensions over any finite set of
areas, restricted to total degrees occurring among the Dyck paths. -/
def DyckDimensionBound : Prop := ∀ n (areas : Finset ℕ),
  ∑ k ∈ areas, ∑ d ∈ (dycks n).image dyckTotalDegree, Module.finrank ℚ (coinvariantSpace n d k) ≤ (dycks n).card

private theorem dyck_area_mass {n : ℕ} {K : Finset ℕ} (hK : ∀ w ∈ dycks n, walkCorank w ∈ K) :
    ∑ k ∈ K, (dyckPoly n).coeff k = (dycks n).card := by
  simp only [dyckPoly,corankSum,Polynomial.finsetSum_coeff,Polynomial.coeff_X_pow]
  rw [Finset.sum_comm]
  have hf (w : List Bool) (hw : w ∈ dycks n) : (∑ k ∈ K, if k=walkCorank w then 1 else 0) = (1:ℕ) := by
    simp [hK w hw]
  rw [Finset.sum_congr rfl hf]
  simp

theorem dyck_hilbert_of_minors_and_dimension (hm : DyckCurveMinors) (hb : DyckDimensionBound) :
    DyckHilbertSpecialization := by
  intro n
  let D := (dycks n).image dyckTotalDegree
  refine ⟨D,fun k => ?_⟩
  let f := fun k => (dyckPoly n).coeff k
  let g := fun k => ∑ d ∈ D, Module.finrank ℚ (coinvariantSpace n d k)
  have hle (j) : f j ≤ g j := by
    dsimp [f,g]
    rw [dyck_slice_sum]
    apply Finset.sum_le_sum
    intro d hd
    obtain ⟨U,hU⟩ := hm n d hd j
    exact dyck_slice_le_of_minor U hU
  apply (hle k).antisymm
  by_contra! hlt
  let K := insert k ((dycks n).image walkCorank)
  have hsum := Finset.sum_lt_sum (s := K) (fun j _ => hle j)
    ⟨k,Finset.mem_insert_self _ _,hlt⟩
  have he : ∑ j ∈ K, f j = (dycks n).card :=
    dyck_area_mass (fun w hw => Finset.mem_insert_of_mem (Finset.mem_image_of_mem walkCorank hw))
  exact ((he ▸ hsum).not_ge (hb n K))

theorem conjecture34_of_minors_dimension_and_midpoints (hm : DyckCurveMinors) (hb : DyckDimensionBound)
    (hc : ∀ n ≥ 96, ∀ δ ≤ 1, CentralToMidpoint n δ) : Conjecture34 :=
  conjecture34_of_hilbert_and_midpoints (dyck_hilbert_of_minors_and_dimension hm hb) hc

end CentralUnimodality.Polarization
