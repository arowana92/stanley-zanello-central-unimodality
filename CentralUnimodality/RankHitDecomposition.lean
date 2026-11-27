module

public import CentralUnimodality.PinnedRankLoss
public import CentralUnimodality.RightSuffixApproximation
import CentralUnimodality.DyckRecurrence

/-! Disjoint decomposition of the surviving-prefix rank mass into complete
ballot words, first hits through a cut, and hits after the cut. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion

def lateHitEvent (m T : ℕ) := (words m).filter (fun w => w.take T ∈ ballots T ∧ ¬BallotFrom 0 w)

private theorem take_ballot {w : List Bool} (hw : BallotFrom 0 w) (t : ℕ) : BallotFrom 0 (w.take t) := by
  have h := (ballot_iff_heights 0 w).mp hw
  rw [← List.take_append_drop t w,heights_append] at h
  exact (ballot_iff_heights 0 _).mpr fun x hx => h x (List.mem_append_left _ hx)

private theorem one_hit_step {m t : ℕ} (ht : t+1 ≤ m) (F : List Bool → ℝ) :
    (∑ w ∈ (words m).filter (fun w => w.take t ∈ ballots t), F w) =
      (∑ w ∈ (words m).filter (fun w => w.take (t+1) ∈ ballots (t+1)), F w) +
      ∑ w ∈ (words m).filter (fun w => w.take (t+1) ∈ hitWords 1 (t+1)), F w := by
  simp only [Finset.sum_filter,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  have hl : w.take (t+1) ∈ words (t+1) := mem_words.mpr (by simp [List.length_take,mem_words.mp hw,ht])
  obtain ⟨hp,hd⟩ := prefix_partition hl
  rw [List.take_take] at hp
  simp only [Nat.min_eq_left (by omega : t ≤ t+1)] at hp
  have hs : w.take (t+1) ∈ ballots (t+1) ↔ BallotFrom 0 (w.take (t+1)) :=
    Finset.mem_filter.trans (and_iff_right hl)
  have hf : w.take (t+1) ∈ hitWords 1 (t+1) ↔ FirstHitPath 1 (w.take (t+1)) :=
    Finset.mem_filter.trans (and_iff_right hl)
  by_cases hb : BallotFrom 0 (w.take (t+1)) <;> by_cases hh : FirstHitPath 1 (w.take (t+1)) <;>
    simp_all

private theorem telescope_hits (m L n : ℕ) (h : L+n ≤ m) (F : List Bool → ℝ) :
    (∑ w ∈ (words m).filter (fun w => w.take L ∈ ballots L), F w) =
      (∑ w ∈ (words m).filter (fun w => w.take (L+n) ∈ ballots (L+n)), F w) +
      ∑ i ∈ Finset.range n, ∑ w ∈ (words m).filter (fun w => w.take (L+i+1) ∈ hitWords 1 (L+i+1)), F w := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih (by omega),one_hit_step (t := L+n) (by omega) F,Finset.sum_range_succ]
    simp only [Nat.add_assoc]
    ring

private theorem split_late_event {m T : ℕ} (ht : T ≤ m) (F : List Bool → ℝ) :
    (∑ w ∈ (words m).filter (fun w => w.take T ∈ ballots T), F w) =
      (∑ w ∈ ballots m, F w)+∑ w ∈ lateHitEvent m T, F w := by
  simp only [lateHitEvent,Finset.sum_filter]
  rw [show ballots m=(words m).filter (BallotFrom 0) from rfl,Finset.sum_filter,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hb : BallotFrom 0 w
  · have ht' : w.take T ∈ words T := mem_words.mpr (by simp [List.length_take,mem_words.mp hw,ht])
    have hmem := mem_ballots.mpr ⟨mem_words.mp ht',take_ballot hb T⟩
    simp [hb,hmem]
  · simp [hb]

/-- The late event used at each rank has exactly the probability to
which the late change-of-measure theorem applies. -/
theorem late_event_probability (c : ℝ) (m T : ℕ) :
    (∑ w ∈ lateHitEvent m T, signMass c (c*m) w)=lateHitMass c m T := by
  simp only [lateHitEvent,lateHitMass,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hp : w.take T ∈ ballots T <;> by_cases hb : BallotFrom 0 w <;> simp [hp,hb]

noncomputable def eventSiteMass (c : ℝ) (m : ℕ) (A : Finset (List Bool)) (k : ℤ) :=
  ∑ w ∈ A, if ((wordParts w).sum:ℤ)=k then signMass c (c*m) w else 0

theorem eventSiteMass_rank (c : ℝ) (m : ℕ) (A : Finset (List Bool)) (k : ℕ) :
    eventSiteMass c m A k = rankEvent c m k A := by
  simp only [eventSiteMass,rankEvent,Finset.sum_filter,Nat.cast_inj]

/-- At every integer site the partition is exact, independently of a
saddle condition or any numerical estimate. -/
theorem rank_hit_decomposition (c : ℝ) {m L T : ℕ} (hL : L ≤ T) (hT : T ≤ m) (k : ℤ) :
    prefixSiteMass c m L k = eventSiteMass c m (ballots m) k+eventSiteMass c m (lateHitEvent m T) k+
      ∑ i ∈ Finset.range (T-L), prefixEventSiteMass c m (L+i+1) (hitWords 1 (L+i+1)) k := by
  let F := fun w => if ((wordParts w).sum:ℤ)=k then signMass c (c*m) w else 0
  have he : L+(T-L)=T := by omega
  have h := telescope_hits m L (T-L) (by omega) F
  rw [he,split_late_event hT] at h
  exact h

/-- Subtracting the discarded rank profiles commutes with the three
signed orders, even at the endpoints of the supports. -/
theorem difference_hit_decomposition (c : ℝ) {m L T : ℕ} (hL : L ≤ T) (hT : T ≤ m) (r : Fin 3) (k : ℤ) :
    rankDifference r k (eventSiteMass c m (ballots m)) =
      rankDifference r k (prefixSiteMass c m L) - rankDifference r k (eventSiteMass c m (lateHitEvent m T)) -
      ∑ i ∈ Finset.range (T-L), rankDifference r k (prefixEventSiteMass c m (L+i+1) (hitWords 1 (L+i+1))) := by
  have h : prefixSiteMass c m L = eventSiteMass c m (ballots m)+eventSiteMass c m (lateHitEvent m T)+
      ∑ i ∈ Finset.range (T-L), prefixEventSiteMass c m (L+i+1) (hitWords 1 (L+i+1)) := by
    funext j
    simpa only [Pi.add_apply,Finset.sum_apply] using rank_hit_decomposition c hL hT j
  rw [h,map_add,map_add,map_sum]; abel

end CentralUnimodality.MarkedExcursion
