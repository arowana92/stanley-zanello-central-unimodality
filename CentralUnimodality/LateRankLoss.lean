module

public import CentralUnimodality.LateRankMoments

/-! The rank-resolved late losses at an original saddle, expressed using
the parameter bin and the auxiliary drift cap in the right-flank verifier. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

noncomputable def lateHeightParameter (g Δ h : ℝ) := (g/2*(1-g^2/(12*4096))+Δ/2)*(h*(1-h/2))

noncomputable def lateRankAllowance (m L T : ℕ) (g G Δ h : ℝ) (r : Fin 3) :=
  let a := lateHeightParameter g Δ h
  let cap := (G+Δ)/2-a
  exp (Δ^2*(labelSquares m/(m:ℝ)^3)/8-a^2/2)*(2*(cap/√m)+(4/5)/√L)*lateFourierBudget (T-L:ℕ) r.val

/-- The original label parameter in the mass and both signed differences
of the complete late event. The bin can choose its own nonnegative rank shift. -/
theorem late_rank_loss {m L T j : ℕ} (hm : 4096 ≤ m) (hL : 0<L) (hLT : L<T) (hT : T≤m)
    {c z g G Δ h : ℝ} (hc : 0 ≤ c) (hz : 0 ≤ z) (hg : 0 ≤ g)
    (hlo : g ≤ 2*c*((m:ℝ)*√m)) (hhi : 2*c*((m:ℝ)*√m) ≤ G)
    (hΔ : Δ=2*z*((m:ℝ)*√m)) (hshift : Δ ≤ 32) (hsmall : g^2 ≤ 12*4096)
    (hh : 0 ≤ h) (hh' : h ≤ 1) (hcut : h*m ≤ T)
    (hheight : lateHeightParameter g Δ h ≤ (6/25)*64)
    (hcap : 0 ≤ (G+Δ)/2-lateHeightParameter g Δ h)
    (hcap' : (G+Δ)/2-lateHeightParameter g Δ h ≤ (6/25)*64)
    (hj : meanRank c m=(j+1:ℕ)) :
    let F := fun k => rankEvent c m k (lateHitEvent m T)
    let U := lateRankAllowance m L T g G Δ h
    F (j+1) ≤ U 0 ∧
      F (j+2)-F (j+1) ≤ 1001/1000*U 1+1001/1000*(2*z)*U 0 ∧
      -(F j-2*F (j+1)+F (j+2)) ≤ U 2+2*(1001/1000)*(2*z)*U 1 := by
  let a := lateHeightParameter g Δ h
  let cap := (G+Δ)/2-a
  let A := lateHitEvent m T
  let R := rankChange c z (meanRank c m) m
  let W : ℤ → ℝ := R • eventSiteMass (c+z) m A
  have hm' : (4096:ℝ) ≤ m := by exact_mod_cast hm
  have hr : (64:ℝ) ≤ √m := (le_sqrt (by norm_num) (Nat.cast_nonneg _)).mpr (by linarith only [hm'])
  have hp : 0<√(m:ℝ) := by linarith
  obtain ⟨hb,hcond,he⟩ := late_bin_parameters hm hT hc hz hg hlo hsmall hh hh' hcut
  rw [← hΔ] at hb hcond he
  change 0 ≤ a/√m at hb
  have ha : a/√m ≤ 6/25 := (div_le_iff₀ hp).mpr (by dsimp only [a]; linarith only [hheight,hr])
  have hc' : cap/√m ≤ 6/25 := (div_le_iff₀ hp).mpr (by dsimp only [cap,a]; linarith only [hcap',hr])
  have harg : (c+z)*m-a/√m ≤ cap/√m := by
    rw [sub_div' hp.ne',div_le_div_iff_of_pos_right hp]
    dsimp only [cap]; linarith only [hhi,hΔ]
  apply rank_event_loss hz (small_rank_shift hm hz hΔ hshift) hj A (Finset.filter_subset ..) W
    (lateRankAllowance m L T g G Δ h) (fun k => ?_)
  · intro r k
    change |rankDifference r k (R • eventSiteMass (c+z) m A)| ≤ _
    rw [map_smul,smul_eq_mul,abs_mul,abs_of_pos (rankChange_pos ..)]
    have H := late_rank_moments hc hz hb ha (div_nonneg hcap hp.le) hc' hL hLT hT harg hcond r k
    apply H.trans_eq
    rw [show z^2*labelSquares m/2-m*(a/√m)^2/2=Δ^2*(labelSquares m/(m:ℝ)^3)/8-a^2/2 from he]
    rfl
  · change R*eventSiteMass (c+z) m A (k:ℤ)=R*rankEvent (c+z) m k A
    rw [eventSiteMass_rank]

end CentralUnimodality.MarkedExcursion
