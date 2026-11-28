module

public import CentralUnimodality.ExcursionFirstMoment
public import CentralUnimodality.FirstReturnMass
import Mathlib.Tactic.Positivity

/-! At each positive even time the fair, unnormalized absolute first area
moment of the first return is exactly one half. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion

private def arch (w : List Bool) : List Bool := (false::w)++[true]

private theorem arch_injective : Function.Injective arch := by
  intro w v h
  exact (List.cons.inj ((List.append_left_inj [true]).mp h)).2

private theorem reflect_injective : Function.Injective reflect :=
  Function.LeftInverse.injective reflect_reflect

private theorem reflect_disp (w : List Bool) : displacement (reflect w) = -displacement w := by
  induction w with
  | nil => simp [reflect,displacement]
  | cons b w ih =>
    change step (!b) + displacement (reflect w) = -(step b + displacement w)
    cases b <;> simp [step,ih,add_comm]

private theorem arch_data {d : ℕ} {w : List Bool} (hw : w∈dycks d) :
    arch w∈firstReturns (2*(d+1)) ∧
      walkArea (arch w)=walkArea w+(2*d+1) ∧ 0≤walkArea (arch w) := by
  obtain ⟨⟨len,hb⟩,hz⟩ := mem_dycks.mp hw
  have disp : displacement (false::w)=1 := by change 1+displacement w=1; omega
  have area : walkArea (arch w)=walkArea w+(2*d+1) := by
    rw [arch,walkArea_append,walkArea_cons,disp,len]
    simp [step,walkArea,heights]
  refine ⟨Finset.mem_filter.mpr ⟨mem_words.mpr (by simp [arch,len]; omega),?_⟩,area,?_⟩
  · refine ⟨by simp [arch],?_,?_⟩
    · rw [arch,displacement_snoc,disp]; decide
    · unfold arch
      rw [List.dropLast_append_of_ne_nil (by decide : [true]≠[])]
      simpa using (noReturn_up_iff w).mpr hb
  · have H := walkArea_eq_corank hb
    rw [area]; omega

private theorem reflect_arch_mem {d : ℕ} {w : List Bool} (hw : w∈dycks d) :
    reflect (arch w) ∈ firstReturns (2*(d+1)) := by
  obtain ⟨hl,hn,hz,hr⟩ := Finset.mem_filter.mp (arch_data hw).1
  apply Finset.mem_filter.mpr
  refine ⟨mem_words.mpr (by simpa [reflect] using mem_words.mp hl),?_,?_,?_⟩
  · simp [reflect,arch]
  · rw [reflect_disp,hz,neg_zero]
  · change NoReturn (((arch w).map (!·)).dropLast)
    rw [← List.map_dropLast]
    exact (noReturn_reflect _).mpr hr

private theorem arch_disjoint (d : ℕ) : Disjoint ((dycks d).image arch)
    ((dycks d).image (reflect ∘ arch)) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨v,_,he⟩ := Finset.mem_image.mp hy
  simp [reflect,arch] at he

private theorem firstReturn_arches (d : ℕ) :
    (dycks d).image arch ∪ (dycks d).image (reflect ∘ arch) = firstReturns (2*(d+1)) := by
  apply Finset.eq_of_subset_of_card_le
  · apply Finset.union_subset
    · intro x hx; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hx; exact (arch_data hw).1
    · intro x hx; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hx; exact reflect_arch_mem hw
  · rw [Finset.card_union_of_disjoint (arch_disjoint d),Finset.card_image_of_injective _ arch_injective,
      Finset.card_image_of_injective _ (reflect_injective.comp arch_injective)]
    have C := card_marks d
    simp only [marks,Finset.card_product,Finset.card_range] at C
    have B : (d+1).centralBinom = (2*d+1).choose d + (2*d+1).choose d := by
      rw [Nat.centralBinom,show 2*(d+1)=2*d+1+1 by omega,Nat.choose_succ_succ,Nat.choose_symm_half]
    have H := card_firstReturns_even d
    rw [B,← C] at H
    apply Nat.le_of_mul_le_mul_left (c:=2*d+1) _ (by omega)
    nlinarith only [H]

theorem firstReturn_absolute_area (d : ℕ) :
    (∑ w ∈ firstReturns (2*(d+1)), |(walkArea w:ℝ)|) / 2^(2*(d+1)) = 1/2 := by
  rw [← firstReturn_arches,Finset.sum_union (arch_disjoint d),
    Finset.sum_image arch_injective.injOn,Finset.sum_image (reflect_injective.comp arch_injective).injOn]
  have one : ∑ w ∈ dycks d, |(walkArea (arch w):ℝ)| = 4^d := by
    rw [← excursion_area_sum]
    apply Finset.sum_congr rfl
    intro w hw
    obtain ⟨_,he,hpos⟩ := arch_data hw
    rw [abs_of_nonneg (by exact_mod_cast hpos : (0:ℝ)≤walkArea (arch w)),he]
    push_cast
    rfl
  simp only [Function.comp_apply,walkArea_reflect,Int.cast_neg,abs_neg,one]
  rw [pow_mul,show (2:ℝ)^2=4 by norm_num,pow_succ]
  field_simp
  norm_num

end CentralUnimodality.MarkedExcursion
