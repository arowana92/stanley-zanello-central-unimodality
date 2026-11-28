module

public import CentralUnimodality.RankLossBins

/-! The right-flank sign tests act on the strict-partition counts.
All loss budgets are in the original label law and the normalization
is the actual surviving prefix probability. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

/-- The signed lower bounds that result after removing the first-hit
times and the late event from the normalized surviving prefix. -/
theorem ballot_rank_margins {m L T : ℕ} (hL : L ≤ T) (hT : T ≤ m)
    (c : ℝ) {σ P : ℝ} (k : ℤ) (pre loss : Fin 3 → ℝ)
    (hpre : ∀ r, pre r ≤ σ^(r.val+1)/P*signedRank r k (prefixSiteMass c m L))
    (hloss : ∀ r, σ^(r.val+1)/P*(earlyRankLoss c m L T r k+
      signedRank r k (eventSiteMass c m (lateHitEvent m T))) ≤ loss r) (r : Fin 3) :
    pre r-loss r ≤ σ^(r.val+1)/P*signedRank r k (eventSiteMass c m (ballots m)) := by
  rw [ballot_signed_loss c hL hT]
  linarith only [hpre r,hloss r]

/-- Positive adjusted growth and positive negative curvature margins give
the two strict conclusions for integer ranks. Each test uses its own cut,
so both implications can be applied independently. -/
theorem integer_rank_signs (c : ℝ) (hc : 0 ≤ c) (m j : ℕ) {σ P G J K : ℝ} (hσ : 0<σ) (hP : 0<P)
    (h₀ : G ≤ σ/P*signedRank 0 (j+1:ℕ) (eventSiteMass c m (ballots m)))
    (h₁ : J ≤ σ^2/P*signedRank 1 (j+1:ℕ) (eventSiteMass c m (ballots m)))
    (h₂ : K ≤ σ^3/P*signedRank 2 (j+1:ℕ) (eventSiteMass c m (ballots m))) :
    (0 < J+σ*(1-exp (-2*c))*G → rankCount m (j+1) < rankCount m (j+2)) ∧
      (0 < K → rankCount m j*rankCount m (j+2) < rankCount m (j+1)^2) := by
  let A := eventSiteMass c m (ballots m)
  let F := fun t => rankEvent c m t (ballots m)
  have hh (t : ℕ) : A (t:ℤ)=F t := eventSiteMass_rank ..
  have hsuc : ((j+1:ℕ):ℤ)+1=(j+2:ℕ) := by omega
  have hprev : ((j+1:ℕ):ℤ)-1=j := by omega
  change G ≤ σ/P*A (j+1:ℕ) at h₀
  change J ≤ σ^2/P*(A ((j+1:ℕ)+1)-A (j+1:ℕ)) at h₁
  change K ≤ σ^3/P*(-(A ((j+1:ℕ)-1)+A ((j+1:ℕ)+1)-2*A (j+1:ℕ))) at h₂
  rw [hsuc,hh,hh] at h₁
  rw [hh] at h₀
  rw [hprev,hsuc,hh,hh,hh] at h₂
  have hu : 0 ≤ 1-exp (-2*c) := sub_nonneg.mpr (exp_le_one_iff.mpr (by linarith))
  constructor
  · intro hg
    apply (rank_step_iff c m (j+1)).mpr
    change exp (-2*c)*F (j+1)<F (j+2)
    have H := add_le_add h₁ (mul_le_mul_of_nonneg_left h₀ (mul_nonneg hσ.le hu))
    have he : σ^2/P*(F (j+2)-F (j+1))+σ*(1-exp (-2*c))*(σ/P*F (j+1)) =
        σ^2/P*(F (j+2)-exp (-2*c)*F (j+1)) := by ring
    rw [he] at H
    exact sub_pos.mp (pos_of_mul_pos_right (hg.trans_le H) (by positivity))
  · intro hk
    apply rank_curvature_of_tilt c m j
    have hh' := pos_of_mul_pos_right (hk.trans_le h₂) (by positivity)
    linarith only [hh']

/-- The Gaussian prefix theorem in the signed coordinates used by the
three discarded-path bounds. -/
theorem prefix_signed_margins {m L : ℕ} (hm : 4096 ≤ m) (hM : 3685 ≤ m-L)
    {c f : ℝ} (hc : 0 < c) (hs : 2*c*((m:ℝ)*√m) ≤ 25) (hf : 0 ≤ f) (hf' : f < 1)
    (hL : (L:ℝ) ≤ f*m) {j : ℤ} (hj : meanRank c m=j) :
    let σ := √(suffixVariance c (m-L))
    let P := live c (c*m) L 1
    let B := varianceLimit m c f σ
    let pre : Fin 3 → ℝ := fun r => if r=0 then 3989/10000*exp (-B/2)-5/1000
      else if r=1 then -(1/4) else -(normalHeight*(B/(1+B/2)-exp (-B/2))+10/1000)
    ∀ r : Fin 3, pre r ≤ σ^(r.val+1)/P*signedRank r j (prefixSiteMass c m L) := by
  obtain ⟨H₀,H₁,H₂⟩ := right_prefix_differences hm hM hc hs hf hf' hL hj
  let σ := √(suffixVariance c (m-L))
  let P := live c (c*m) L 1
  let A := prefixSiteMass c m L
  let V := varianceLimit m c f σ
  change _ ≤ σ*(A j/P) at H₀
  change |σ^2*(A (j+1)/P-A j/P)| < _ at H₁
  change σ^3*(A (j-1)/P+A (j+1)/P-2*(A j/P)) ≤ _ at H₂
  dsimp only
  intro r
  fin_cases r
  · change 3989/10000*exp (-V/2)-5/1000 ≤ σ^1/P*A j
    apply H₀.trans_eq; ring
  · change -(1/4) ≤ σ^2/P*(A (j+1)-A j)
    apply ((abs_le.mp H₁.le).1).trans_eq; ring
  · change -(normalHeight*(V/(1+V/2)-exp (-V/2))+10/1000) ≤
        σ^3/P*(-(A (j-1)+A (j+1)-2*A j))
    apply (neg_le_neg H₂).trans_eq; ring

end CentralUnimodality.MarkedExcursion
