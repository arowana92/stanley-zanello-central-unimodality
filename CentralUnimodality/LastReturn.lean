module

public import CentralUnimodality.WalkArea

/-! Split at the last visit to zero. This gives an exact convolution of
weighted path counts before evaluating any Fourier samples. -/
@[expose] public section

namespace CentralUnimodality

theorem displacement_snoc (w : List Bool) (b : Bool) :
    displacement (w++[b]) = displacement w + step b := by simp [displacement]

theorem noReturn_snoc (w : List Bool) (b : Bool) :
    NoReturn (w++[b]) ↔ NoReturn w ∧ displacement w + step b ≠ 0 := by
  simp [NoReturn, heights_append, heights, ne_comm]

def lastStep (p : List Bool × List Bool) (b : Bool) : List Bool × List Bool :=
  if displacement p.2 + step b = 0 then (p.1 ++ p.2 ++ [b], [])
  else (p.1, p.2 ++ [b])

def lastSplit (w : List Bool) : List Bool × List Bool := w.foldl lastStep ([], [])

private theorem lastSplit_snoc (w : List Bool) (b : Bool) :
    lastSplit (w++[b]) = lastStep (lastSplit w) b := by simp [lastSplit]

theorem lastSplit_valid (w : List Bool) :
    (lastSplit w).1 ++ (lastSplit w).2 = w ∧
    displacement (lastSplit w).1 = 0 ∧ NoReturn (lastSplit w).2 := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl, by simp [lastSplit, NoReturn, heights]⟩
  | append_singleton w b ih =>
    obtain ⟨hc, hb, hs⟩ := ih
    rw [lastSplit_snoc, lastStep]
    split
    next h =>
      refine ⟨by simp [hc], ?_, by simp [NoReturn, heights]⟩
      simp only [List.append_assoc, displacement_append, hb, zero_add] at *
      simpa [displacement] using h
    next h =>
      exact ⟨(List.append_assoc ..).symm.trans (congrArg (· ++ [b]) hc), hb,
        (noReturn_snoc _ _).mpr ⟨hs, h⟩⟩

theorem empty_of_bridge_noReturn {w : List Bool} (hb : displacement w = 0)
    (hs : NoReturn w) : w = [] := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w b _ => exact False.elim (((noReturn_snoc _ _).mp hs).2 (displacement_snoc w b ▸ hb))

private theorem lastSplit_bridge {u : List Bool} (hb : displacement u = 0) :
    lastSplit u = (u, []) := by
  obtain ⟨hc, hz, hs⟩ := lastSplit_valid u
  have hright : displacement (lastSplit u).2 = 0 := by
    have e := congrArg displacement hc
    rwa [displacement_append, hz, zero_add, hb] at e
  have hnil := empty_of_bridge_noReturn hright hs
  exact Prod.ext (by simpa [hnil] using hc) hnil

theorem lastSplit_append {u v : List Bool} (hb : displacement u = 0) (hs : NoReturn v) :
    lastSplit (u++v) = (u,v) := by
  induction v using List.reverseRecOn with
  | nil => simpa using lastSplit_bridge hb
  | append_singleton v b ih =>
    obtain ⟨hv, hne⟩ := (noReturn_snoc _ _).mp hs
    rw [← List.append_assoc, lastSplit_snoc, ih hv]
    simp [lastStep, hne]

def words : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n+1 => (words n).image (false :: ·) ∪ (words n).image (true :: ·)

theorem mem_words {w : List Bool} {n : ℕ} : w ∈ words n ↔ w.length = n := by
  induction n generalizing w with
  | zero => simp [words]
  | succ n ih =>
    cases w with
    | nil => simp [words]
    | cons b w =>
      cases b <;> simp [words, ih]

def bridges (n : ℕ) : Finset (List Bool) := (words n).filter fun w => displacement w = 0
def strictWords (n : ℕ) : Finset (List Bool) := (words n).filter NoReturn

private def splitPairs (n : ℕ) :=
  (Finset.range (n+1)).biUnion fun t => bridges t ×ˢ strictWords (n-t)

private theorem mem_splitPairs {p : List Bool × List Bool} {n : ℕ} :
    p ∈ splitPairs n ↔
      p.1.length + p.2.length = n ∧ displacement p.1 = 0 ∧ NoReturn p.2 := by
  simp only [splitPairs, Finset.mem_biUnion, Finset.mem_range, Finset.mem_product,
    bridges, strictWords, Finset.mem_filter, mem_words]
  constructor
  · rintro ⟨t, ht, ⟨ha, hb⟩, hc, hd⟩
    exact ⟨by omega, hb, hd⟩
  · rintro ⟨h, hb, hs⟩
    exact ⟨_, by omega, ⟨rfl, hb⟩, by omega, hs⟩

private def join (p : List Bool × List Bool) := p.1 ++ p.2

private theorem words_eq_joins (n : ℕ) : words n = (splitPairs n).image join := by
  ext w
  rw [mem_words, Finset.mem_image]
  constructor
  · intro h
    obtain ⟨he, hb, hs⟩ := lastSplit_valid w
    refine ⟨lastSplit w, mem_splitPairs.mpr ⟨?_, hb, hs⟩, he⟩
    rw [← List.length_append, he, h]
  · rintro ⟨p, hp, rfl⟩
    exact List.length_append.trans (mem_splitPairs.mp hp).1

private theorem join_injOn (n : ℕ) : Set.InjOn join (splitPairs n : Set _) := by
  intro a ha b hb he
  obtain ⟨_, h₁, h₂⟩ := mem_splitPairs.mp ha
  obtain ⟨_, h₃, h₄⟩ := mem_splitPairs.mp hb
  exact (lastSplit_append h₁ h₂).symm.trans ((congrArg lastSplit he).trans (lastSplit_append h₃ h₄))

/-- The integer-area transform at all unrestricted lengths is the convolution
of the return-to-zero transform and the no-return transform. -/
theorem lastReturn_convolution {R : Type*} [Semiring R] (χ : ℤ → R)
    (χ_add : ∀ x y, χ (x+y) = χ x * χ y) (n : ℕ) :
    (∑ w ∈ words n, χ (walkArea w)) =
      ∑ t ∈ Finset.range (n+1),
        (∑ u ∈ bridges t, χ (walkArea u)) * (∑ v ∈ strictWords (n-t), χ (walkArea v)) := by
  rw [words_eq_joins, Finset.sum_image (join_injOn n), splitPairs, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro t _
    rw [Finset.sum_product, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v _
    have h := (Finset.mem_filter.mp hu).2
    change displacement u = 0 at h
    simp [join, walkArea_append, h, χ_add]
  · intro a _ b _ hne
    apply Finset.disjoint_left.mpr
    intro p hpa hpb
    have ea := mem_words.mp (Finset.mem_filter.mp (Finset.mem_product.mp hpa).1).1
    have eb := mem_words.mp (Finset.mem_filter.mp (Finset.mem_product.mp hpb).1).1
    exact hne (ea.symm.trans eb)

end CentralUnimodality
