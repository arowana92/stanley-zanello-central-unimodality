module

public import CentralUnimodality.InnerArcs
public import CentralUnimodality.SmoothReturnInverse

/-! Fourier decay for a first return. Pinning the endpoint to height one
uses the exact first-hit bound on the terminal segment. The prefix retains
its survival probability and the intervening killed blocks retain their
Fourier cancellation. -/
@[expose] public section

namespace CentralUnimodality
open Real PowerSeries

/-- A surviving walk ending at one reaches zero on appending one down-step. -/
theorem killedAt_one_cap (ω : ℝ) {a : ℕ} (ha : 0 < a) (t : ℕ) :
    ‖killedAt ω a t 1‖ ≤ (2:ℝ)^t/((t:ℝ)+1) := by
  rw [← hitAt_succ]
  apply (hitAt_norm ..).trans
  have h := first_hit_half ha (Nat.succ_pos t)
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at h
  rw [le_div_iff₀ (by positivity)]
  push_cast at h
  rw [pow_succ] at h
  linarith only [h]

/-- A terminal segment of length t pays a factor 1/(t+1), uniformly over
the height where it starts. All k middle blocks retain their row bound. -/
theorem killed_bridge_blocks {ω q : ℝ} {L : ℕ} (h : KilledBound ω L q) (hq : 0≤q)
    (p k t : ℕ) :
    ‖killedAt ω 1 (p+k*L+t) 1‖/(2:ℝ)^(p+k*L+t) ≤
      survival ((p+1)/2)*q^k/((t:ℝ)+1) := by
  have hpre (s : Finset ℤ) := killed_prefix_blocks h hq 1 p k s
  simp only [Nat.cast_one,survivors_one_card,ballot_survival] at hpre
  have pre (s : Finset ℤ) := (div_le_iff₀ (by positivity)).mp (hpre s)
  have cap := killedAt_split_cap pre (fun y hy => killedAt_one_cap ω hy t) (by positivity)
  rw [div_le_iff₀ (by positivity)]
  apply cap.trans_eq
  rw [pow_add]
  ring

private theorem orient_conj (ω : ℝ) (x : ℤ) :
    areaCharacter ω (-x) = (starRingEnd ℂ) (areaCharacter ω x) := by
  rw [areaCharacter,areaCharacter,← Complex.exp_conj]
  congr 1
  simp

private theorem upper_arch_character (ω : ℝ) (d : ℕ) :
    (∑ w ∈ dycks d, areaCharacter ω (walkArea w+(2*d+1))) =
      areaCharacter ω 1*killedAt ω 1 (2*d) 1 := by
  rw [killedAt,Finset.mul_sum,dycks,ballots]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w hw
  have len := mem_words.mp hw
  by_cases hb : BallotFrom 0 w <;> by_cases hd : displacement w=0
  all_goals simp [positive_one_iff,hb,hd,sum_heights,len,← areaCharacter_add]
  congr 1
  omega

/-- Removing the first and last steps costs a factor one half after the
two orientations of the excursion are combined. -/
theorem returnSymbol_bridge (ω : ℝ) (d : ℕ) :
    ‖returnSymbol ω (d+1)‖ ≤ (‖killedAt ω 1 (2*d) 1‖/(2:ℝ)^(2*d))/2 := by
  let Z := ∑ w ∈ dycks d, areaCharacter ω (walkArea w+(2*d+1))
  have sum : (∑ w ∈ firstReturns (2*(d+1)), areaCharacter ω (walkArea w)) =
      Z+(starRingEnd ℂ) Z := by
    rw [MarkedExcursion.sum_firstReturn_orientations]
    simp only [Z,orient_conj,map_sum]
  have nZ : ‖Z‖=‖killedAt ω 1 (2*d) 1‖ := by
    dsimp only [Z]
    rw [upper_arch_character,norm_mul,norm_areaCharacter,one_mul]
  have h := norm_add_le Z ((starRingEnd ℂ) Z)
  rw [Complex.norm_conj,nZ] at h
  rw [returnSymbol,coeff_walkSeries]
  change ‖(2:ℂ)⁻¹^(2*(d+1))*(∑ w ∈ firstReturns (2*(d+1)), areaCharacter ω (walkArea w))‖≤_
  rw [sum,norm_mul,norm_pow,norm_inv,show ‖(2:ℂ)‖=(2:ℝ) by norm_num]
  apply (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq
  rw [show 2*(d+1)=2*d+2 by omega,pow_add,inv_pow]
  ring

end CentralUnimodality
