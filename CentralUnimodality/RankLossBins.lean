module

public import CentralUnimodality.LateRankLoss

/-! Sum the discarded profiles on their odd lattice of first-hit times.
The intervals use the actual ceiling cuts, including bins of zero length. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

/-- An upper bound on this signed quantity is the loss in mass, forward
growth, or negative second difference when the event is discarded. -/
noncomputable def signedRank (r : Fin 3) (j : ℤ) (A : ℤ → ℝ) :=
  if r=2 then -rankDifference r j A else rankDifference r j A

noncomputable def firstRankLoss (c : ℝ) (m t : ℕ) (r : Fin 3) (j : ℤ) :=
  signedRank r j (prefixEventSiteMass c m t (hitWords 1 t))

noncomputable def earlyRankLoss (c : ℝ) (m L T : ℕ) (r : Fin 3) (j : ℤ) :=
  ∑ i ∈ Finset.range (T-L), firstRankLoss c m (L+i+1) r j

theorem early_loss_split (c : ℝ) (m : ℕ) {L S T : ℕ} (hLS : L ≤ S) (hST : S ≤ T) (r : Fin 3) (j : ℤ) :
    earlyRankLoss c m L T r j = earlyRankLoss c m L S r j+earlyRankLoss c m S T r j := by
  unfold earlyRankLoss
  rw [show T-L=(S-L)+(T-S) by omega,Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show L+(S-L+i)+1=S+i+1 by omega]

theorem ballot_signed_loss (c : ℝ) {m L T : ℕ} (hL : L ≤ T) (hT : T ≤ m) (r : Fin 3) (j : ℤ) :
    signedRank r j (eventSiteMass c m (ballots m)) = signedRank r j (prefixSiteMass c m L) -
      signedRank r j (eventSiteMass c m (lateHitEvent m T)) - earlyRankLoss c m L T r j := by
  have H := difference_hit_decomposition c hL hT r j
  unfold earlyRankLoss firstRankLoss signedRank
  by_cases hr : r=2 <;> simp only [hr,ite_true,ite_false,Finset.sum_neg_distrib] at H ⊢ <;> linarith only [H]

private theorem firstRankLoss_even (c : ℝ) (m t : ℕ) (ht : 0<t) (he : t%2=0) (r : Fin 3) (j : ℤ) :
    firstRankLoss c m t r j=0 := by
  have H := first_hit_incompatible 0 (t-1) (by rintro ⟨d,hd⟩; omega)
  rw [show t-1+1=t by omega] at H
  have hs : prefixEventSiteMass c m t (hitWords 1 t)=0 := by
    rw [show hitWords 1 t=∅ from H]; funext x; simp [prefixEventSiteMass]
  simp [firstRankLoss,signedRank,hs]

/-- Enumerate d exactly once for each possible first hit at 2d+1 after
the first cut and through the second. No unsigned estimate discards parity. -/
theorem early_loss_odd (c : ℝ) (m L T : ℕ) (r : Fin 3) (j : ℤ) :
    earlyRankLoss c m L T r j =
      ∑ d ∈ Finset.Ico ((L+1)/2) ((T+1)/2), firstRankLoss c m (2*d+1) r j := by
  let I := (Finset.range (T-L)).filter (fun i => (L+i+1)%2=1)
  have keep : (∑ i ∈ I, firstRankLoss c m (L+i+1) r j)=earlyRankLoss c m L T r j := by
    apply Finset.sum_subset (Finset.filter_subset ..)
    intro i hi hnot
    have h : (L+i+1)%2≠1 := fun hh => hnot (Finset.mem_filter.mpr ⟨hi,hh⟩)
    exact firstRankLoss_even c m _ (by omega) (by omega) r j
  rw [← keep]
  apply Finset.sum_bij' (fun i _ => (L+i)/2) (fun d _ => 2*d-L)
  · intro i hi
    obtain ⟨ht,ho⟩ := Finset.mem_filter.mp hi
    have := Finset.mem_range.mp ht; exact Finset.mem_Ico.mpr (by omega)
  · intro d hd; obtain ⟨hd₁,hd₂⟩ := Finset.mem_Ico.mp hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by omega⟩
  · intro i hi; obtain ⟨_,ho⟩ := Finset.mem_filter.mp hi; omega
  · intro d hd; obtain ⟨_,_⟩ := Finset.mem_Ico.mp hd; omega
  · intro i hi
    obtain ⟨_,ho⟩ := Finset.mem_filter.mp hi
    rw [show 2*((L+i)/2)+1=L+i+1 by omega]

/-- There are at most m((w-v)/2+1/4096) possible odd hitting times in
the verifier bin (ceil(vm),ceil(wm)], valid for every m≥4096. -/
theorem first_hit_bin_count {m : ℕ} (hm : 4096 ≤ m) {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) :
    let L := ⌈v*m⌉₊
    let T := ⌈w*m⌉₊
    ((Finset.Ico ((L+1)/2) ((T+1)/2)).card:ℝ) ≤ m*((w-v)/2+1/4096) := by
  let L := ⌈v*m⌉₊
  let T := ⌈w*m⌉₊
  have hLT : L ≤ T := Nat.ceil_mono (mul_le_mul_of_nonneg_right hvw (Nat.cast_nonneg _))
  have upper : (T:ℝ)<w*m+1 := Nat.ceil_lt_add_one (mul_nonneg (hv.trans hvw) (Nat.cast_nonneg _))
  have lower : v*m ≤ (L:ℝ) := Nat.le_ceil _
  have hcard : 2*(Finset.Ico ((L+1)/2) ((T+1)/2)).card+L ≤ T+1 := by rw [Nat.card_Ico]; omega
  have hreal : 2*((Finset.Ico ((L+1)/2) ((T+1)/2)).card:ℝ)+L ≤ (T:ℝ)+1 := by exact_mod_cast hcard
  have hm' : (4096:ℝ) ≤ m := by exact_mod_cast hm
  change ((Finset.Ico ((L+1)/2) ((T+1)/2)).card:ℝ) ≤ _
  linarith only [hreal,upper,lower,hm']

/-- A uniform cap at each odd hit in a time bin gives the full signed
budget of that bin, irrespective of the signs of the actual differences. -/
theorem early_loss_bin_bound {m : ℕ} (hm : 4096 ≤ m) {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w)
    (c : ℝ) (r : Fin 3) (j : ℤ) {C : ℝ} (hC : 0 ≤ C)
    (bound : ∀ d : ℕ, ⌈v*m⌉₊ < 2*d+1 → 2*d+1 ≤ ⌈w*m⌉₊ → firstRankLoss c m (2*d+1) r j ≤ C) :
    earlyRankLoss c m ⌈v*m⌉₊ ⌈w*m⌉₊ r j ≤ m*((w-v)/2+1/4096)*C := by
  rw [early_loss_odd]
  apply (Finset.sum_le_sum (fun d hd => bound d (by have := Finset.mem_Ico.mp hd; omega)
    (by have := Finset.mem_Ico.mp hd; omega))).trans
  simpa only [Finset.sum_const,nsmul_eq_mul] using mul_le_mul_of_nonneg_right (first_hit_bin_count hm hv hvw) hC

end CentralUnimodality.MarkedExcursion
