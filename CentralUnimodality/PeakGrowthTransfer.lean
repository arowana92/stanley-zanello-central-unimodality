module

public import CentralUnimodality.OddTimeQuadrature

/-! Transfer a signed adjacent difference through the path decomposition.
At each hitting time one auxiliary tilt controls the full loss in growth. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

noncomputable def growthDifference (c : ℝ) (k : ℤ) (F : ℤ→ℝ) :=
  F (k+1)-exp (-2*c)*F k

theorem growth_event_tilt {m j : ℕ} {c z : ℝ} (hc : 0≤c) (hz : 0≤z)
    (hsmall : 2*z≤1/8192) (A : Finset (List Bool)) (hA : A⊆words m)
    {M J : ℝ}
    (hM : rankChange c z (j+1:ℕ) m*rankEvent (c+z) m (j+1) A≤M)
    (hJ : rankChange c z (j+1:ℕ) m*|rankEvent (c+z) m (j+2) A-rankEvent (c+z) m (j+1) A|≤J) :
    growthDifference c (j+1:ℕ) (eventSiteMass c m A) ≤
      (1001/1000)*(J+2*(c+z)*M) := by
  let R := rankChange c z (j+1:ℕ) m
  have hR : 0≤R := (rankChange_pos ..).le
  have h₀ : rankEvent c m (j+1) A=R*rankEvent (c+z) m (j+1) A := by
    simpa only [sub_self,mul_zero,exp_zero,one_mul] using change_at_neighbor c z (j+1) (j+1) A hA
  have hX := mul_nonneg hR (rankEvent_nonneg (c+z) m (j+1) A)
  have hM' : 0≤M := hX.trans hM
  have h₁ := (change_difference_bounds c hz hsmall j A hA).1
  dsimp only at h₁
  rw [← mul_sub,abs_mul,abs_of_nonneg hR] at h₁
  have hstep : 1-exp (-2*c)≤2*c := by linarith only [add_one_le_exp (-2*c)]
  have hbase := mul_le_mul_of_nonneg_right hstep (rankEvent_nonneg c m (j+1) A)
  have hm := h₀.le.trans hM
  have hmc := mul_le_mul_of_nonneg_left hm (show 0≤2*c by positivity)
  have hmz := mul_le_mul_of_nonneg_left hM (show 0≤(1001/1000)*(2*z) by positivity)
  have hJ' := mul_le_mul_of_nonneg_left hJ (by norm_num : (0:ℝ)≤1001/1000)
  have hcost := mul_nonneg hc hM'
  change eventSiteMass c m A ((j+2:ℕ):ℤ)-exp (-2*c)*eventSiteMass c m A (j+1:ℕ)≤_
  rw [eventSiteMass_rank,eventSiteMass_rank]
  dsimp only [R] at *
  linarith only [h₁,hbase,hmc,hmz,hJ',hcost]

/-- Scaled form of the tilt estimate. The same bound applies to a late
event or to a single first hit with its own suffix standard deviation. -/
theorem scaled_growth_event {m j : ℕ} {c z σ P M J Λ : ℝ} (hc : 0≤c) (hz : 0≤z)
    (hsmall : 2*z≤1/8192) (hσ : 0<σ) (hP : 0<P) (hΛ : 2*(c+z)*σ≤Λ)
    (A : Finset (List Bool)) (hA : A⊆words m) (hj : meanRank c m=(j+1:ℕ))
    (hM : σ*rankChange c z (meanRank c m) m*
      |rankDifference 0 (j+1:ℕ) (eventSiteMass (c+z) m A)|≤P*M)
    (hJ : σ^2*rankChange c z (meanRank c m) m*
      |rankDifference 1 (j+1:ℕ) (eventSiteMass (c+z) m A)|≤P*J) :
    σ^2/P*growthDifference c (j+1:ℕ) (eventSiteMass c m A) ≤ (1001/1000)*(J+Λ*M) := by
  let R := rankChange c z (j+1:ℕ) m
  have hX : 0≤R*rankEvent (c+z) m (j+1) A := mul_nonneg (rankChange_pos ..).le (rankEvent_nonneg ..)
  rw [hj] at hM hJ
  change σ*R*|eventSiteMass (c+z) m A (j+1:ℕ)|≤_ at hM
  change σ^2*R*|eventSiteMass (c+z) m A (j+2:ℕ)-eventSiteMass (c+z) m A (j+1:ℕ)|≤_ at hJ
  rw [eventSiteMass_rank,abs_of_nonneg (rankEvent_nonneg ..),mul_assoc] at hM
  rw [eventSiteMass_rank,eventSiteMass_rank,mul_assoc] at hJ
  have hM₀ : 0≤M := nonneg_of_mul_nonneg_right ((mul_nonneg hσ.le hX).trans hM) hP
  have mass := (le_div_iff₀ hσ).mpr (by simpa only [mul_comm σ _] using hM)
  have slope := (le_div_iff₀ (sq_pos_of_pos hσ)).mpr (by simpa only [mul_comm (σ^2) _] using hJ)
  have H := growth_event_tilt hc hz hsmall A hA mass slope
  have K := mul_le_mul_of_nonneg_right H (sq_nonneg σ)
  have HΛ := mul_le_mul_of_nonneg_right hΛ (mul_nonneg hP.le hM₀)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hP).mpr
  field_simp at K
  linarith only [K,HΛ]

/-- Positivity after subtracting every discarded contribution implies a
strict inequality of the original two integer rank counts. The pre-factor
can be any positive normalization, for instance the suffix variance divided
by the surviving prefix mass. -/
theorem growth_from_hit_margins {m L T j : ℕ} {c a pre early late : ℝ}
    (hL : L≤T) (hT : T≤m) (ha : 0<a) (hgap : early+late<pre)
    (hP : pre≤a*growthDifference c (j+1:ℕ) (prefixSiteMass c m L))
    (hE : (∑ d∈Finset.Ico ((L+1)/2) ((T+1)/2),
      a*growthDifference c (j+1:ℕ) (prefixEventSiteMass c m (2*d+1) (hitWords 1 (2*d+1))))≤early)
    (hS : a*growthDifference c (j+1:ℕ) (eventSiteMass c m (lateHitEvent m T))≤late) :
    rankCount m (j+1)<rankCount m (j+2) := by
  let k : ℤ := (j+1:ℕ)
  let F := eventSiteMass c m (ballots m)
  let P := prefixSiteMass c m L
  let S := eventSiteMass c m (lateHitEvent m T)
  let hit (d : ℕ) := prefixEventSiteMass c m (2*d+1) (hitWords 1 (2*d+1))
  let D := Finset.Ico ((L+1)/2) ((T+1)/2)
  have E (r : Fin 3) : signedRank r k F=signedRank r k P-signedRank r k S-
      ∑ d∈D,signedRank r k (hit d) := by
    rw [show (∑ d∈D,signedRank r k (hit d))=earlyRankLoss c m L T r k from (early_loss_odd ..).symm]
    exact ballot_signed_loss c hL hT r k
  have mass := E 0
  have slope := E 1
  change F k=P k-S k-∑ d∈D,hit d k at mass
  change F (k+1)-F k=P (k+1)-P k-(S (k+1)-S k)-∑ d∈D,(hit d (k+1)-hit d k) at slope
  rw [Finset.sum_sub_distrib] at slope
  change (∑ d∈D,a*(hit d (k+1)-exp (-2*c)*hit d k))≤early at hE
  rw [← Finset.mul_sum,Finset.sum_sub_distrib,← Finset.mul_sum] at hE
  change pre≤a*(P (k+1)-exp (-2*c)*P k) at hP
  change a*(S (k+1)-exp (-2*c)*S k)≤late at hS
  have H : 0<a*(F (k+1)-exp (-2*c)*F k) := by
    linarith only [hgap,hP,hS,hE,congrArg (a*·) slope,
      congrArg ((a*(1-exp (-2*c)))*·) mass]
  have H' := (rank_step_iff c m (j+1)).mpr
  apply H'
  have hh := sub_pos.mp (pos_of_mul_pos_right H ha.le)
  change exp (-2*c)*eventSiteMass c m (ballots m) (j+1:ℕ)<eventSiteMass c m (ballots m) (j+2:ℕ) at hh
  rwa [eventSiteMass_rank,eventSiteMass_rank] at hh

end CentralUnimodality.MarkedExcursion
