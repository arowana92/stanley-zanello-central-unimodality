module

public import CentralUnimodality.ConditionalRankVariance
public import CentralUnimodality.SaddleRank

/-! The rank mass of a word conditioned to survive a prefix is a mixture
of the unrestricted suffix rank masses, with the exact integer shifts. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

/-- Each down-step in the prefix has its rank label shifted by the suffix length. -/
def shiftedPrefixRank (M : ℕ) (w : List Bool) := (wordParts w).sum + M*(wordParts w).length

theorem shiftedPrefixRank_real (M : ℕ) (w : List Bool) :
    (shiftedPrefixRank M w:ℝ) = prefixRank ((w.length:ℝ)+M) w := by
  induction w with
  | nil => simp [shiftedPrefixRank,prefixRank,wordParts]
  | cons b w ih =>
    cases b
    · simpa [shiftedPrefixRank,prefixRank,wordParts,add_right_comm] using ih
    · simp only [shiftedPrefixRank,wordParts,List.sum_append,List.sum_singleton,List.length_append,
        List.length_nil,Nat.cast_add,Nat.cast_mul,Nat.cast_one,List.length_cons,prefixRank,ite_true] at ih ⊢
      rw [show (w.length:ℝ)+1+M-1=w.length+M by ring,← ih]
      ring

theorem shifted_rank_append (v w : List Bool) :
    (wordParts (v++w)).sum = shiftedPrefixRank w.length v + (wordParts w).sum := by
  have h := prefixRank_full (v++w)
  rw [List.length_append,Nat.cast_add,prefixRank_append,← shiftedPrefixRank_real,
    show (v.length:ℝ)+w.length-v.length=w.length by ring,prefixRank_full] at h
  exact_mod_cast h.symm

theorem prefixMean_full (c : ℝ) (m : ℕ) : prefixMean c (c*m) m m = meanRank c m := by
  rw [← prefixMean_exact,← meanRank_expectation]
  apply Finset.sum_congr rfl
  intro w hw
  rw [← mem_words.mp hw,prefixRank_full]

theorem split_meanRank (c : ℝ) {m L : ℕ} (h : L ≤ m) :
    meanRank c m = prefixMean c (c*m) m L + meanRank c (m-L) := by
  rw [← prefixMean_full,← prefixMean_full,prefixMean,prefixMean,prefixMean]
  conv_lhs => rw [← Nat.add_sub_of_le h]
  rw [Finset.sum_range_add]
  simp only [Nat.add_sub_of_le h]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.cast_sub h,Nat.cast_add]
  have h₁ : (m:ℝ)-(L+i)=(m-L)-i := by ring
  have h₂ : c*m-c*(L+i)=c*(m-L)-c*i := by ring
  rw [h₁,h₂]

/-- The unrestricted suffix mass on all integer sites, including its zero tails. -/
noncomputable def freeRankMass (c : ℝ) (M : ℕ) (k : ℤ) : ℝ :=
  ∑ w ∈ words M, if ((wordParts w).sum:ℤ)=k then signMass c (c*M) w else 0

/-- Rank mass at an integer site with a specified set of allowed prefixes. -/
noncomputable def prefixEventSiteMass (c : ℝ) (m L : ℕ) (A : Finset (List Bool)) (k : ℤ) : ℝ :=
  ∑ w ∈ (words m).filter (fun w => w.take L ∈ A),
    if ((wordParts w).sum:ℤ)=k then signMass c (c*m) w else 0

/-- The unnormalized rank mass with survival imposed through L steps. -/
noncomputable def prefixSiteMass (c : ℝ) (m L : ℕ) (k : ℤ) : ℝ :=
  prefixEventSiteMass c m L (ballots L) k

theorem prefixEventSiteMass_rankEvent (c : ℝ) (m L j : ℕ) (A : Finset (List Bool)) :
    prefixEventSiteMass c m L A j = rankEvent c m j ((words m).filter (fun w => w.take L ∈ A)) := by
  simp only [prefixEventSiteMass,rankEvent,Finset.sum_filter,Nat.cast_inj]

theorem prefixSiteMass_rankEvent (c : ℝ) (m L j : ℕ) :
    prefixSiteMass c m L j = rankEvent c m j ((words m).filter (fun w => w.take L ∈ ballots L)) := by
  exact prefixEventSiteMass_rankEvent c m L j (ballots L)

theorem prefixEventSiteMass_mixture (c : ℝ) {m L : ℕ} (h : L ≤ m) (A : Finset (List Bool))
    (hA : A ⊆ words L) (k : ℤ) :
    prefixEventSiteMass c m L A k = ∑ w ∈ A, signMass c (c*m) w *
      freeRankMass c (m-L) (k-shiftedPrefixRank (m-L) w) := by
  rw [prefixEventSiteMass,prefix_sum h A hA]
  apply Finset.sum_congr rfl
  intro v hv
  rw [freeRankMass,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  have he : c*(m:ℝ)-c*v.length=c*(m-L:ℕ) := by rw [mem_words.mp (hA hv),Nat.cast_sub h]; ring
  rw [shifted_rank_append,mem_words.mp hw,Nat.cast_add,append_mass,he]
  split_ifs <;> first | rfl | omega | simp_all

theorem prefixSiteMass_mixture (c : ℝ) {m L : ℕ} (h : L ≤ m) (k : ℤ) :
    prefixSiteMass c m L k = ∑ w ∈ ballots L, signMass c (c*m) w *
      freeRankMass c (m-L) (k-shiftedPrefixRank (m-L) w) :=
  prefixEventSiteMass_mixture c h (ballots L) (Finset.filter_subset ..) k

theorem saddle_suffix_site (c : ℝ) {m L : ℕ} (h : L ≤ m) {j : ℤ} (hj : meanRank c m=j)
    {w : List Bool} (hw : w ∈ ballots L) :
    ((j-shiftedPrefixRank (m-L) w:ℤ):ℝ)-meanRank c (m-L) = -centeredRank c (c*m) m w := by
  rw [Int.cast_sub,Int.cast_natCast,← hj,split_meanRank c h,shiftedPrefixRank_real,centeredRank,
    (mem_ballots.mp hw).1,Nat.cast_sub h]
  rw [show (L:ℝ)+(m-L)=m by ring]
  ring

end CentralUnimodality.MarkedExcursion
