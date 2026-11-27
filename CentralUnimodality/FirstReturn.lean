module

public import CentralUnimodality.LastReturn

/-! The first-return renewal equation and the Kraft bound on the absolute
mass of the inverse convolution. Time is measured in individual steps. -/
@[expose] public section

namespace CentralUnimodality

def IsFirstReturn (w : List Bool) : Prop :=
  w ≠ [] ∧ displacement w = 0 ∧ NoReturn w.dropLast

instance (w : List Bool) : Decidable (IsFirstReturn w) := inferInstanceAs
  (Decidable (w ≠ [] ∧ displacement w = 0 ∧ NoReturn w.dropLast))

def firstReturns (n : ℕ) : Finset (List Bool) := (words n).filter IsFirstReturn

private theorem exists_first_hit (h : ℤ) (w : List Bool) (hh : 0 ∈ heights h w) :
    ∃ u v, w = u++v ∧ u ≠ [] ∧ h+displacement u = 0 ∧ 0 ∉ heights h u.dropLast := by
  induction w generalizing h with
  | nil => simp [heights] at hh
  | cons b w ih =>
    by_cases hz : h+step b = 0
    · exact ⟨[b], w, rfl, by simp, by simpa [displacement] using hz, by simp [heights]⟩
    · have ht : 0 ∈ heights (h+step b) w := by simpa [heights, Ne.symm hz] using hh
      obtain ⟨u, v, he, hn, hd, ha⟩ := ih _ ht
      refine ⟨b::u, v, by simp [he], by simp, ?_, ?_⟩
      · simpa [displacement, add_assoc] using hd
      · cases u with
        | nil => contradiction
        | cons a u => simpa [heights, Ne.symm hz] using ha

theorem exists_firstReturn {w : List Bool} (h : ¬ NoReturn w) :
    ∃ u v, w = u++v ∧ IsFirstReturn u := by
  obtain ⟨u, v, e, hn, hd, hs⟩ := exists_first_hit 0 w (by simpa [NoReturn] using h)
  exact ⟨u, v, e, hn, by simpa using hd, hs⟩

theorem firstReturn_prefix_free {u v : List Bool}
    (hu : IsFirstReturn u) (huv : IsFirstReturn (u++v)) : v = [] := by
  by_contra hv
  have hs := huv.2.2
  rw [NoReturn, List.dropLast_append_of_ne_nil hv, heights_append] at hs
  have hn : NoReturn u := fun h => hs (List.mem_append_left _ h)
  exact hu.1 (empty_of_bridge_noReturn hu.2.1 hn)

theorem firstReturn_join_injective {u v a b : List Bool}
    (hu : IsFirstReturn u) (ha : IsFirstReturn a) (e : u++v = a++b) : u = a ∧ v = b := by
  rcases List.append_eq_append_iff.mp e with ⟨t, rfl, rfl⟩ | ⟨t, rfl, rfl⟩
  · simp [firstReturn_prefix_free hu ha]
  · simp [firstReturn_prefix_free ha hu]

theorem card_words (n : ℕ) : (words n).card = 2^n := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    rw [words, Finset.card_union_of_disjoint]
    · have inj (b : Bool) : Function.Injective (b :: · : List Bool → List Bool) :=
        fun _ _ he => (List.cons.inj he).2
      rw [Finset.card_image_of_injective _ (inj false), Finset.card_image_of_injective _ (inj true), ih,
        Nat.pow_succ, Nat.mul_two]
    · apply Finset.disjoint_left.mpr
      intro w h₁ h₂
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp h₁
      obtain ⟨v, _, he⟩ := Finset.mem_image.mp h₂
      exact Bool.noConfusion (List.cons.inj he).1

private def firstPairs (B : ℕ → Finset (List Bool)) (n : ℕ) :=
  (Finset.range (n+1)).biUnion fun t => firstReturns t ×ˢ B (n-t)

private theorem mem_firstPairs {B : ℕ → Finset (List Bool)} {p : List Bool × List Bool} {n : ℕ} :
    p ∈ firstPairs B n ↔ p.1.length ≤ n ∧ IsFirstReturn p.1 ∧ p.2 ∈ B (n-p.1.length) := by
  simp only [firstPairs, Finset.mem_biUnion, Finset.mem_range, Finset.mem_product, firstReturns,
    Finset.mem_filter, mem_words]
  constructor
  · rintro ⟨_, ht, ⟨rfl, h₁⟩, h₂⟩; exact ⟨by omega, h₁, h₂⟩
  · rintro ⟨ht, h₁, h₂⟩; exact ⟨_, by omega, ⟨rfl, h₁⟩, h₂⟩

private theorem pairs_disjoint (B : ℕ → Finset (List Bool)) (n : ℕ) :
    ((Finset.range (n+1) : Finset ℕ) : Set ℕ).PairwiseDisjoint (fun t => firstReturns t ×ˢ B (n-t)) := by
  intro a _ b _ hne
  apply Finset.disjoint_left.mpr
  intro p ha hb
  have h₁ := mem_words.mp (Finset.mem_filter.mp (Finset.mem_product.mp ha).1).1
  have h₂ := mem_words.mp (Finset.mem_filter.mp (Finset.mem_product.mp hb).1).1
  exact hne (h₁.symm.trans h₂)

private def concatPair (p : List Bool × List Bool) := p.1 ++ p.2

private theorem concat_injOn (B : ℕ → Finset (List Bool)) (n : ℕ) :
    Set.InjOn concatPair (firstPairs B n : Set _) := by
  intro p hp q hq h
  have he := firstReturn_join_injective (mem_firstPairs.mp hp).2.1 (mem_firstPairs.mp hq).2.1 h
  exact Prod.ext he.1 he.2

/-- Dividing by 2^n gives the subprobability bound for first returns through
length n. This is exact even when the last allowed length is odd. -/
theorem firstReturn_kraft (n : ℕ) :
    ∑ t ∈ Finset.range (n+1), (firstReturns t).card * 2^(n-t) ≤ 2^n := by
  have hs : (firstPairs words n).image concatPair ⊆ words n := by
    intro w hw
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hl, _, ht⟩ := mem_firstPairs.mp hp
    have he := mem_words.mp ht
    apply mem_words.mpr
    change (p.1 ++ p.2).length = n
    rw [List.length_append, he]
    omega
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injOn (concat_injOn words n), firstPairs, Finset.card_biUnion (pairs_disjoint ..)] at hc
  simpa only [Finset.card_product, card_words] using hc

private theorem bridges_eq_first (n : ℕ) :
    bridges (n+1) = (firstPairs bridges (n+1)).image concatPair := by
  ext w
  rw [Finset.mem_image]
  constructor
  · intro hw
    obtain ⟨h₁, h₂⟩ := Finset.mem_filter.mp hw
    have hl := mem_words.mp h₁
    have hz : ¬NoReturn w := by
      intro h
      have := empty_of_bridge_noReturn h₂ h
      simp_all
    obtain ⟨u, v, rfl, hu⟩ := exists_firstReturn hz
    have hv : displacement v = 0 := by
      simpa [displacement_append, hu.2.1] using h₂
    simp only [List.length_append] at hl
    exact ⟨(u,v), mem_firstPairs.mpr ⟨by simpa using (show u.length ≤ n+1 by omega), hu,
      Finset.mem_filter.mpr ⟨mem_words.mpr (by change v.length = n+1-u.length; omega), hv⟩⟩, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨hl, hu, hv⟩ := mem_firstPairs.mp hp
    obtain ⟨hlen, hd⟩ := Finset.mem_filter.mp hv
    have he := mem_words.mp hlen
    exact Finset.mem_filter.mpr ⟨mem_words.mpr (by simp [concatPair]; omega),
      by simp [concatPair, displacement_append, hu.2.1, hd]⟩

/-- Positive-length bridge transforms satisfy the first-return renewal equation. -/
theorem firstReturn_renewal {R : Type*} [Semiring R] (χ : ℤ → R)
    (χ_add : ∀ x y, χ (x+y) = χ x * χ y) (n : ℕ) :
    (∑ w ∈ bridges (n+1), χ (walkArea w)) =
      ∑ t ∈ Finset.range (n+2),
        (∑ u ∈ firstReturns t, χ (walkArea u)) * (∑ v ∈ bridges (n+1-t), χ (walkArea v)) := by
  rw [bridges_eq_first, Finset.sum_image (concat_injOn ..), firstPairs,
    Finset.sum_biUnion (pairs_disjoint ..)]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_product, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v _
  have he : IsFirstReturn u := (Finset.mem_filter.mp hu).2
  simp [concatPair, walkArea_append, he.2.1, χ_add]

end CentralUnimodality
