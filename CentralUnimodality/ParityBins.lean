module

public import CentralUnimodality.CubicBlocks

/-! A finite sum over a single parity uses disjoint two-step cells. Split
each cell into 2B places. Dividing the place number by the block length
sends it to one of B bins, each with room for exactly L places. -/
@[expose] public section

namespace CentralUnimodality

def cellSlot (B j h : ℕ) := B*(j-2)+h

theorem cellSlot_bounds {B j h : ℕ} (hj : 2 ≤ j) (hh : h < 2*B) :
    B*(j-2) ≤ cellSlot B j h ∧ cellSlot B j h < B*j := by
  have he : B*(j-2)+2*B = B*j := by
    rw [Nat.mul_comm 2 B,← Nat.mul_add,Nat.sub_add_cancel hj]
  dsimp [cellSlot]
  omega

theorem parity_bins {L B p : ℕ} (hL : 0 < L) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, 2 ≤ j ∧ j ≤ L ∧ j%2 = p)
    (u F : ℕ → ℝ) (hF : ∀ i < B, 0 ≤ F i)
    (hu : ∀ j ∈ J, ∀ h < 2*B, u j ≤ F (cellSlot B j h / L)) :
    (2*(B:ℝ))*(∑ j ∈ J, u j) ≤ (L:ℝ)*(∑ i ∈ Finset.range B, F i) := by
  classical
  let S := J ×ˢ Finset.range (2*B)
  let U := Finset.range B ×ˢ Finset.range L
  let f (x : ℕ × ℕ) := (cellSlot B x.1 x.2/L,cellSlot B x.1 x.2%L)
  have data {x : ℕ × ℕ} (hx : x ∈ S) : x.1 ∈ J ∧ x.2 < 2*B := by
    simpa [S] using hx
  have maps : S.image f ⊆ U := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hj,hh⟩ := data hx
    obtain ⟨h₂,hmax,_⟩ := hJ _ hj
    have hs := (cellSlot_bounds h₂ hh).2.trans_le (Nat.mul_le_mul_left B hmax)
    simpa [U,f] using And.intro ((Nat.div_lt_iff_lt_mul hL).mpr hs) (Nat.mod_lt _ hL)
  have inj : Set.InjOn f (S : Set (ℕ × ℕ)) := by
    intro x hx y hy he
    have h₁ := congrArg Prod.fst he
    have h₂ := congrArg Prod.snd he
    change cellSlot B x.1 x.2/L = cellSlot B y.1 y.2/L at h₁
    change cellSlot B x.1 x.2%L = cellSlot B y.1 y.2%L at h₂
    have hs := Nat.mod_add_div (cellSlot B x.1 x.2) L
    rw [h₁,h₂,Nat.mod_add_div] at hs
    obtain ⟨jx,tx⟩ := data hx
    obtain ⟨jy,ty⟩ := data hy
    obtain ⟨hx₂,_,hpx⟩ := hJ _ jx
    obtain ⟨hy₂,_,hpy⟩ := hJ _ jy
    have bx := cellSlot_bounds hx₂ tx
    have by' := cellSlot_bounds hy₂ ty
    have hj : x.1 = y.1 := by
      rcases lt_trichotomy x.1 y.1 with h|h|h
      · have := Nat.mul_le_mul_left B (by omega : x.1 ≤ y.1-2)
        omega
      · exact h
      · have := Nat.mul_le_mul_left B (by omega : y.1 ≤ x.1-2)
        omega
    apply Prod.ext hj
    dsimp [cellSlot] at hs
    rw [hj] at hs
    omega
  calc
    _ = ∑ x ∈ S, u x.1 := by simp [S,Finset.sum_product,Finset.mul_sum]
    _ ≤ ∑ x ∈ S, F (f x).1 := Finset.sum_le_sum (fun x hx => hu _ (data hx).1 _ (data hx).2)
    _ = ∑ y ∈ S.image f, F y.1 := by rw [Finset.sum_image inj]
    _ ≤ ∑ y ∈ U, F y.1 := Finset.sum_le_sum_of_subset_of_nonneg maps (fun y hy _ =>
      hF _ (Finset.mem_range.mp (Finset.mem_product.mp hy).1))
    _ = _ := by simp [U,Finset.sum_product,Finset.mul_sum]

end CentralUnimodality
