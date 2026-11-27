module

public import CentralUnimodality.LastReturn
public import CentralUnimodality.Statement

/-! Exact signed-area law for the two central families. This is a finite-sum
identity for arbitrary test functions, so it also applies to Fourier characters. -/
@[expose] public section

namespace CentralUnimodality

def reflect (w : List Bool) : List Bool := w.map (!·)

theorem reflect_reflect (w : List Bool) : reflect (reflect w) = w := by
  simp [reflect, List.map_map, Function.comp_def]

theorem heights_reflect (h : ℤ) (w : List Bool) :
    heights (-h) (reflect w) = (heights h w).map Neg.neg := by
  induction w generalizing h with
  | nil => rfl
  | cons b w ih =>
    have he : step (!b) = -(step b) := by cases b <;> decide
    change (-h+step (!b)) :: heights (-h+step (!b)) (reflect w) =
      -(h+step b) :: (heights (h+step b) w).map Neg.neg
    rw [he, ← neg_add, ih]

theorem walkArea_reflect (w : List Bool) : walkArea (reflect w) = -walkArea w := by
  have negsum (l : List ℤ) : (l.map Neg.neg).sum = -l.sum := by
    induction l with
    | nil => simp
    | cons a l ih => simp [ih, add_comm]
  simpa [walkArea, negsum] using congrArg List.sum (heights_reflect 0 w)

theorem noReturn_reflect (w : List Bool) : NoReturn (reflect w) ↔ NoReturn w := by
  have he := heights_reflect 0 w
  simp only [neg_zero] at he
  simp [NoReturn, he]

private def positiveWord (m : ℕ) (l : List ℕ) := false :: wordOfParts m l

private theorem positiveWord_injOn (m : ℕ) :
    Set.InjOn (positiveWord m) (allPartitions m : Set _) := by
  intro a ha b hb he
  have eqw := (List.cons.inj he).2
  simpa only [wordParts_wordOfParts (mem_allPartitions.mp ha),
    wordParts_wordOfParts (mem_allPartitions.mp hb)] using congrArg wordParts eqw

private theorem mem_positive_image (m : ℕ) (w : List Bool) :
    w ∈ (allPartitions m).image (positiveWord m) ↔
      ∃ v, w = false::v ∧ v.length = m ∧ BallotFrom 0 v := by
  constructor
  · intro h
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp h
    exact ⟨_, rfl, wordOfParts_length m l, ((ballotEquiv m).symm ⟨l, mem_allPartitions.mp hl⟩).2.2⟩
  · rintro ⟨v, rfl, hv, hb⟩
    have hf : Fits m (wordParts v) := by simpa [hv] using (ballot_iff_fits 0 v).mp hb
    exact Finset.mem_image.mpr ⟨wordParts v, mem_allPartitions.mpr hf,
      congrArg (false :: ·) (hv ▸ wordOfParts_wordParts v)⟩

private theorem strictWords_branches (m : ℕ) :
    strictWords (m+1) = (allPartitions m).image (positiveWord m) ∪
      (allPartitions m).image (reflect ∘ positiveWord m) := by
  let up := (allPartitions m).image (positiveWord m)
  have hdown (w : List Bool) :
      w ∈ (allPartitions m).image (reflect ∘ positiveWord m) ↔ reflect w ∈ up := by
    constructor
    · intro h
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp h
      simp only [Function.comp_apply, reflect_reflect]
      exact Finset.mem_image_of_mem _ hl
    · intro h
      obtain ⟨l, hl, he⟩ := Finset.mem_image.mp h
      exact Finset.mem_image.mpr ⟨l, hl, (congrArg reflect he).trans (reflect_reflect _)⟩
  have hu {w : List Bool} (hw : w ∈ up) : w ∈ strictWords (m+1) := by
    obtain ⟨v, rfl, hv, hb⟩ := (mem_positive_image m w).mp hw
    exact Finset.mem_filter.mpr ⟨mem_words.mpr (by simp [hv]), (noReturn_up_iff v).mpr hb⟩
  ext w
  rw [Finset.mem_union, hdown]
  constructor
  · intro h
    obtain ⟨hw, hs⟩ := Finset.mem_filter.mp h
    have hl := mem_words.mp hw
    cases w with
    | nil => simp at hl
    | cons b v =>
      have hv : v.length = m := by simpa using hl
      cases b with
      | false => exact Or.inl ((mem_positive_image m _).mpr ⟨v, rfl, hv, (noReturn_up_iff v).mp hs⟩)
      | true =>
        right
        have hr := (noReturn_reflect (true :: v)).mpr hs
        exact (mem_positive_image m _).mpr ⟨reflect v, rfl, by simpa [reflect] using hv,
          (noReturn_up_iff _).mp hr⟩
  · rintro (h | h)
    · exact hu h
    · obtain ⟨hw, hs⟩ := Finset.mem_filter.mp (hu h)
      exact Finset.mem_filter.mpr ⟨mem_words.mpr (by simpa [reflect] using mem_words.mp hw),
        (noReturn_reflect _).mp hs⟩

/-- Twice the positive signed half-area for a strict word whose suffix
represents a rank-j partition. -/
def signedAreaAtRank (n δ j : ℕ) : ℤ :=
  2*((n : ℤ)*(n+δ)-j) + (2*n+δ+1) + (n+δ)

theorem sum_over_ranks {A : Type*} [AddCommMonoid A] (f : ℕ → A) (n δ : ℕ) (hδ : δ ≤ 1) :
    (∑ l ∈ allPartitions (2*n+δ), f l.sum) =
      ∑ j ∈ Finset.range (n*(n+δ)+1), rankCount (2*n+δ) j • f j := by
  let m := 2*n+δ
  have maps : ∀ l ∈ allPartitions m, l.sum ∈ Finset.range (n*(n+δ)+1) := by
    intro l hl
    have hb := sum_le_staircase_area hδ ((fits_iff_inside_reverse n δ hδ l).mp (mem_allPartitions.mp hl))
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (by simpa using hb))
  rw [← Finset.sum_fiberwise_of_maps_to' maps f]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Finset.sum_const, rankCount_eq_card, m]

theorem signed_ranks {A : Type*} [AddCommMonoid A] (f : ℤ → A) (n δ : ℕ) (hδ : δ ≤ 1) :
    (∑ w ∈ strictWords (2*n+δ+1), f (walkArea w)) =
      ∑ j ∈ Finset.range (n*(n+δ)+1), rankCount (2*n+δ) j •
        (f (signedAreaAtRank n δ j) + f (-signedAreaAtRank n δ j)) := by
  let m := 2*n+δ
  have hdis : Disjoint ((allPartitions m).image (positiveWord m))
      ((allPartitions m).image (reflect ∘ positiveWord m)) := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp h₁
    obtain ⟨b, _, he⟩ := Finset.mem_image.mp h₂
    exact Bool.noConfusion (List.cons.inj he).1
  have hr : Function.Injective reflect := fun _ _ he => by
    simpa only [reflect_reflect] using congrArg reflect he
  rw [strictWords_branches, Finset.sum_union hdis, Finset.sum_image (positiveWord_injOn m),
    Finset.sum_image (hr.injOn.comp (positiveWord_injOn m) (Set.mapsTo_univ ..)),
    ← Finset.sum_add_distrib, ← sum_over_ranks _ n δ hδ]
  apply Finset.sum_congr rfl
  intro l hl
  have ha : walkArea (positiveWord m l) = signedAreaAtRank n δ l.sum := by
    have ht := strict_up_area n δ hδ (wordOfParts_length m l)
    simp only [wordOfParts_length, wordParts_wordOfParts (mem_allPartitions.mp hl)] at ht
    simpa [positiveWord, signedAreaAtRank, m] using ht
  simp [Function.comp_apply, walkArea_reflect, ha]

end CentralUnimodality
