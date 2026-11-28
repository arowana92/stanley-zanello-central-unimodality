module

public import CentralUnimodality.LateEndpointRank
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Apply the endpoint row contraction to the characteristic function of
the paths discarded after the late cut, with the original saddle normalizer. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

noncomputable def lateRankCharacter (v θ : ℝ) (m T : ℕ) :=
  ∑ w ∈ lateHitEvent m T, (signMass v (v*m) w:ℂ)*phase (θ*(wordParts w).sum)

/-- Joint height and rank tilting at the saddle. The complete oscillating
prefix row survives the change of probability measure. -/
theorem late_rank_character_of_ruin {c z b Q : ℝ} (hc : 0 ≤ c) (hQ : 0 ≤ Q) (hb : 0 ≤ b) (θ : ℝ)
    {m T : ℕ} (hm : 0 < m) (hT : T ≤ m) (hcut : b*m ≤ (tanh (c*m)/m+z)*prefixLabels m T)
    (hr : ∀ H : ℕ, ruin (c+z) (m-T) H ≤ exp (-b*H)*(exp ((m-T:ℕ)*b^2/2)*Q)) :
    rankChange c z (meanRank c m) m * ‖lateRankCharacter (c+z) θ m T‖ ≤
      exp (z^2*labelSquares m/2-m*b^2/2)*Q*endpointNorm (wallRow (c+z) ((c+z)*m-b) m θ 0 T) := by
  let v := c+z
  let W := endpointNorm (wallRow v (v*m-b) m θ 0 T)
  have h := late_endpoint_of_ruin θ T (m-T) hr
  dsimp only at h
  rw [Nat.add_sub_of_le hT] at h
  have hf := (rank_character_le_row (c+z) θ (lateHitEvent m T) (Finset.filter_subset ..)).trans h
  have HH := mul_le_mul_of_nonneg_left hf (rankChange_pos c z (meanRank c m) m).le
  apply HH.trans
  change rankChange c z (meanRank c m) m*(W*(_*(exp _*Q))) ≤ _*Q*W
  rw [show rankChange c z (meanRank c m) m*(W*((coshProduct v (v*m-b) T/coshProduct v (v*m) T)*(exp ((m-T:ℕ)*b^2/2)*Q))) =
    (jointCost c z b m T*exp ((m-T:ℕ)*b^2/2))*(Q*W) by unfold jointCost rankChange; dsimp only [v]; ring,show exp (z^2*labelSquares m/2-m*b^2/2)*Q*W=exp (z^2*labelSquares m/2-m*b^2/2)*(Q*W) by ring]
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg hQ (endpointNorm_nonneg _))
  apply (mul_le_mul_of_nonneg_right (joint_cost_bound hm hT hc hb z) (exp_pos _).le).trans
  rw [← exp_add,Nat.cast_sub hT,exp_le_exp]
  nlinarith only [mul_le_mul_of_nonneg_left hcut hb]

theorem late_rank_character {c z b : ℝ} (hc : 0 ≤ c) (hz : 0 ≤ z) (hb : 0 ≤ b) (θ : ℝ)
    {m T : ℕ} (hm : 0 < m) (hT : T ≤ m) (hcut : b*m ≤ (tanh (c*m)/m+z)*prefixLabels m T) :
    rankChange c z (meanRank c m) m * ‖lateRankCharacter (c+z) θ m T‖ ≤
      exp (z^2*labelSquares m/2-m*b^2/2)*endpointNorm (wallRow (c+z) ((c+z)*m-b) m θ 0 T) := by
  simpa only [mul_one] using late_rank_character_of_ruin (z:=z) hc (by norm_num : (0:ℝ)≤1) hb θ hm hT hcut (by
    intro H; rw [mul_one,← exp_add]
    apply (suffix_ruin (add_nonneg hc hz) hb (m-T) H).trans (exp_le_exp.mpr _)
    linarith only [hb])

private theorem down_rectangle {x : ℝ} (hx : |x| ≤ 6/25) :
    9/25 ≤ upChance (-x) ∧ upChance (-x) ≤ 31/50 := by
  have upper (y : ℝ) (hy : y ≤ 6/25) : tanh y ≤ 6/25 := by
    rcases le_total 0 y with h|h
    · exact (tanh_le_linear h).trans hy
    · rw [tanh_eq_sinh_div_cosh]
      exact (div_nonpos_of_nonpos_of_nonneg (sinh_nonpos_iff.mpr h) (cosh_pos _).le).trans (by norm_num)
  have h₁ := upper x (abs_le.mp hx).2
  have h₂ := upper (-x) (by linarith only [(abs_le.mp hx).1])
  rw [tanh_neg] at h₂
  constructor <;> linarith only [h₁,h₂,up_drift x,up_total x]

theorem live_length_antitone (c u : ℝ) : Antitone (fun t => live c u t 1) := by
  apply antitone_nat_of_succ_le
  intro t
  have H := prefix_first_hit c u t
  linarith only [H,Finset.sum_nonneg (s:=hitWords 1 (t+1)) (fun w _ => (signMass_pos c u w).le)]

/-- The .20 pair contraction for every full block between the early
prefix and the late cut. The remaining prefix contributes its survival bound.
The assertions on b and U are the numerical parameter restrictions in the bins. -/
theorem late_wall_blocks {v b U : ℝ} (hv : 0≤v) (hb' : b≤6/25) (hU' : U≤6/25) (θ : ℝ)
    {m p l k T : ℕ} (hT : T≤m) (hblocks : T=p+k*(2*l)) (hcap : v*m-b≤U) :
    endpointNorm (wallRow v (v*m-b) m θ 0 T) ≤ live v (v*m-b) p 1*
        ((1+exp (-(1/5)*l*sin (l*θ/2)^2))/2)^k := by
  have pcap (i : ℕ) : v*m-b-v*i ≤ U := by linarith only [hcap,mul_nonneg hv (Nat.cast_nonneg (α:=ℝ) i)]
  have H := (paired_wall_powers v (v*m-b) m θ 0 p l k).1 (by
    intro i _ hi
    apply down_rectangle (abs_le.mpr ⟨?_,(pcap i).trans hU'⟩)
    have hil : (i:ℝ) ≤ m := by exact_mod_cast hi.le.trans (hblocks ▸ hT)
    linarith only [mul_le_mul_of_nonneg_left hil hv,hb'])
  rw [← hblocks] at H
  rw [live_ballots]; exact H

theorem late_rank_blocks {c z b U : ℝ} (hc : 0 ≤ c) (hz : 0 ≤ z) (hb : 0 ≤ b)
    (hb' : b ≤ 6/25) (hU : 0 ≤ U) (hU' : U ≤ 6/25) (θ : ℝ)
    {m p l k T : ℕ} (hp : 0 < p) (hm : 0 < m) (hT : T ≤ m) (hblocks : T=p+k*(2*l))
    (hcap : (c+z)*m-b ≤ U) (hcut : b*m ≤ (tanh (c*m)/m+z)*prefixLabels m T) :
    rankChange c z (meanRank c m) m * ‖lateRankCharacter (c+z) θ m T‖ ≤
      exp (z^2*labelSquares m/2-m*b^2/2)*(2*U+(4/5)/√p)*
        ((1+exp (-(1/5)*l*sin (l*θ/2)^2))/2)^k := by
  have hv := add_nonneg hc hz
  have H := late_wall_blocks hv hb' hU' θ hT hblocks hcap
  have HH := live_upper_of_cap (c:=c+z) (u:=(c+z)*m-b) hU hp (fun i _ => by linarith only [hcap,mul_nonneg hv (Nat.cast_nonneg (α:=ℝ) i)])
  apply (late_rank_character hc hz hb θ hm hT hcut).trans
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (H.trans (mul_le_mul_of_nonneg_right HH (by positivity))) (exp_pos _).le

end CentralUnimodality.MarkedExcursion
