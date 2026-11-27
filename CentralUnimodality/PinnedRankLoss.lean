module

public import CentralUnimodality.PinnedFirstHit
public import CentralUnimodality.RankEventLoss

/-! The three-block first-hit bound at an original saddle and the signed
costs of restoring the original label tilt at its two neighbours. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

/-- Bound on one time, before restoring the original tilt. The final
standard deviation is computed from the remaining labels after that hit. -/
noncomputable def pinnedRankAllowance (m d : ℕ) (c z γ Δ v e : ℝ) (r : Fin 3) :=
  let β := (γ+Δ)*e/4
  let x := v/3-2/4096
  let F := 2*β+(4/5)/√x
  let σ := √(suffixVariance (c+z) (m-(2*d+1)))
  exp (Δ^2*(labelSquares m/(m:ℝ)^3)/8 - v*(1-e/2)^2*(γ+Δ)*(γ*(1-γ^2/(6*m))+Δ)/8) *
    ((1/2+β/128)*F^2/(√x*((m:ℝ)*√m))) * (shortSuffixLimit r/σ^(r.val+1))

/-- The actual ranked event of a first hit at this time, with the original
label parameter. Order one needs an upper bound, order two a lower bound. -/
theorem pinned_rank_loss {m d : ℕ} (hm : 4096 ≤ m) {c z γ Δ v e : ℝ} (hc : 0 ≤ c) (hz : 0 ≤ z)
    (hγ : γ=2*c*((m:ℝ)*√m)) (hΔ : Δ=2*z*((m:ℝ)*√m)) (hmax : γ+Δ ≤ 57) (hshift : Δ ≤ 32)
    (he : e ≤ 15/16+1/4096) (hlo : v*m ≤ 2*(d:ℝ)+1) (hhi : 2*(d:ℝ)+1 ≤ e*m)
    (hcore : 80 ≤ (v/3-2/4096)*m) {j : ℕ} (hj : meanRank c m=(j+1:ℕ)) :
    let A := (words m).filter (fun w => w.take (2*d+1) ∈ hitWords 1 (2*d+1))
    let F := fun k => rankEvent c m k A
    let U := pinnedRankAllowance m d c z γ Δ v e
    F (j+1) ≤ U 0 ∧
      F (j+2)-F (j+1) ≤ 1001/1000*U 1+1001/1000*(2*z)*U 0 ∧
      -(F j-2*F (j+1)+F (j+2)) ≤ U 2+2*(1001/1000)*(2*z)*U 1 := by
  let A := (words m).filter (fun w => w.take (2*d+1) ∈ hitWords 1 (2*d+1))
  let U := pinnedRankAllowance m d c z γ Δ v e
  let R := rankChange c z (meanRank c m) m
  let X (k : ℕ) := R*rankEvent (c+z) m k A
  let S := prefixEventSiteMass (c+z) m (2*d+1) (hitWords 1 (2*d+1))
  let W : ℤ → ℝ := R • S
  have hm' : (4096:ℝ) ≤ m := by exact_mod_cast hm
  have hstep := small_rank_shift hm hz hΔ hshift
  have hΔ' : 0 ≤ Δ := by rw [hΔ]; positivity
  have hγ' : 0 ≤ γ := by rw [hγ]; positivity
  have hγ₂ := pow_le_pow_left₀ hγ' (by linarith only [hmax,hΔ'] : γ ≤ 57) 2
  have hb : 2*d+1+255 ≤ m := by
    have H : 2*(d:ℝ)+1+255 ≤ m := by nlinarith only [hhi,hm',mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (α:=ℝ) m)]
    exact_mod_cast H
  have hpin := pinned_hit_bin (d := d) hm (add_nonneg hc hz) (by linarith only [hγ,hΔ] : γ+Δ=2*(c+z)*((m:ℝ)*√m))
    hmax he hlo hhi hcore
  have bound (r : Fin 3) (k : ℤ) : |rankDifference r k W| ≤ U r := by
    have H := first_hit_rank_bound hm (by omega : 2*d+1 ≤ m) (by omega) hc hz hγ hΔ hmax
      (by linarith only [hγ₂,hm']) (by linarith only [he]) hlo hhi r k
    change |rankDifference r k (R • S)| ≤ _
    rw [map_smul,smul_eq_mul,abs_mul,abs_of_pos (rankChange_pos ..)]
    apply H.trans
    have hU : 0 ≤ shortSuffixLimit r := by unfold shortSuffixLimit; split <;> norm_num
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpin (exp_pos _).le) (by positivity)
  have hX (k : ℕ) : W (k:ℤ)=X k := by
    change R*prefixEventSiteMass _ _ _ _ _=_
    rw [prefixEventSiteMass_rankEvent]
  exact rank_event_loss hz hstep hj A (Finset.filter_subset ..) W U hX bound

end CentralUnimodality.MarkedExcursion
