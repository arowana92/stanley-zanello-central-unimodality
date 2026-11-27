module

public import CentralUnimodality.Survival
public import CentralUnimodality.FirstReturn
public import Mathlib.Data.Nat.Choose.Central

/-! The exact first-return coefficient comes from differencing the number of
surviving paths after one further step. -/
@[expose] public section

namespace CentralUnimodality

private def addStep (p : List Bool × Bool) : List Bool := p.1 ++ [p.2]

private theorem addStep_injective : Function.Injective addStep := by
  rintro ⟨u,a⟩ ⟨v,b⟩ h
  change u ++ [a] = v ++ [b] at h
  have huv : u = v := by simpa using congrArg List.dropLast h
  subst v
  exact Prod.ext rfl (List.cons.inj ((List.append_right_inj u).mp h)).1

private theorem strict_or_firstReturn (n : ℕ) :
    strictWords (n+1) ∪ firstReturns (n+1) =
      (strictWords n ×ˢ Finset.univ).image addStep := by
  ext w
  induction w using List.reverseRecOn with
  | nil =>
    simp [strictWords, firstReturns, mem_words, addStep]
  | append_singleton w b _ =>
    have hmem : w++[b] ∈ (strictWords n ×ˢ Finset.univ).image addStep ↔ w ∈ strictWords n := by
      constructor
      · intro h
        obtain ⟨p,hp,he⟩ := Finset.mem_image.mp h
        have h' : p = (w,b) := addStep_injective he
        subst p
        exact (Finset.mem_product.mp hp).1
      · intro h
        exact Finset.mem_image.mpr ⟨(w,b), Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩, rfl⟩
    rw [hmem]
    have hne : w ++ [b] ≠ [] := by simp
    simp only [strictWords, firstReturns, Finset.mem_union, Finset.mem_filter, mem_words,
      List.length_append, List.length_singleton, Nat.add_right_cancel_iff, IsFirstReturn,
      displacement_snoc, noReturn_snoc, List.dropLast_append_of_ne_nil (by simp : [b] ≠ []),
      List.dropLast_singleton, List.append_nil]
    tauto

theorem card_firstReturn_step (n : ℕ) :
    (strictWords (n+1)).card + (firstReturns (n+1)).card = 2*(strictWords n).card := by
  have hdis : Disjoint (strictWords (n+1)) (firstReturns (n+1)) := by
    apply Finset.disjoint_left.mpr
    intro w hs hf
    have h := (Finset.mem_filter.mp hf).2
    exact h.1 (empty_of_bridge_noReturn h.2.1 (Finset.mem_filter.mp hs).2)
  rw [← Finset.card_union_of_disjoint hdis, strict_or_firstReturn, Finset.card_image_of_injective _ addStep_injective,
    Finset.card_product]
  simp [Nat.mul_comm]

theorem firstReturns_odd_empty (n : ℕ) : firstReturns (2*n+1) = ∅ := by
  have h := card_firstReturn_step (2*n)
  rw [card_strictWords_even, card_strictWords_odd] at h
  exact Finset.card_eq_zero.mp (by omega)

/-- There are centralBinom (n+1)/(2*n+1) first-return words of length 2*(n+1).
The division-free form also handles the first positive return length. -/
theorem card_firstReturns_even (n : ℕ) :
    (2*n+1) * (firstReturns (2*(n+1))).card = (n+1).centralBinom := by
  have hs := card_firstReturn_step (2*n+1)
  rw [show 2*n+1+1 = 2*(n+1) by omega, card_strictWords_even, card_strictWords_odd] at hs
  change (n+1).centralBinom + _ = 2*(2*n.centralBinom) at hs
  have h := congrArg (fun k => (2*n+1)*k) hs
  have hb := Nat.succ_mul_centralBinom_succ n
  nlinarith only [h, hb]

end CentralUnimodality
