module

public import CentralUnimodality.PeakFrequencyScale
public import CentralUnimodality.SpatialInnerTail
public import CentralUnimodality.PackedTrialTail
public import CentralUnimodality.CorrectedTimeBins
public import CentralUnimodality.RationalRetainedCost
public import CentralUnimodality.CompactPhaseIntegral

/-! Above rescaled time 114 the small-arc bound on the signed staircase
law is cheaper than approximating its return convolution. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Real Set Witness ReturnSplit

theorem outer_cell_amplitude {n δ i : ℕ} (hs : δ≤1) (hn : 7200≤n+δ) (high : 228≤ i)
    {ξ : ℝ} (nn : 0≤ξ) (band : |ξ|≤1728) (cell : |ξ|^(2/3:ℝ)∈halfInterval i) :
    |signedAmplitude n δ (ξ/cellScale (n+δ))-spectralTrial ξ|≤(outerCellAllowance i:ℝ) := by
  let N := n+δ
  let S := cellScale N
  let u := |ξ|^(2/3:ℝ)
  let z := sqrt (u/(2*(N:ℝ)))
  have n0 : 0<N := by dsimp only [N]; omega
  have np : (0:ℝ)<N := by exact_mod_cast n0
  have nr : (7200:ℝ)≤N := by exact_mod_cast hn
  have sp : 0<S := cellScale_pos n0
  obtain ⟨range,phase⟩ := peak_frequency_scale n0 band
  have low : (i:ℝ)/2≤u := cell.1
  have ir : (228:ℝ)≤ i := by exact_mod_cast high
  have up : 0<u := by linarith only [low,ir]
  have uc : u≤144 := range.2
  have zpos : 0<z := sqrt_pos_of_pos (div_pos up (by positivity))
  have z2 : z^2=u/(2*(N:ℝ)) := sq_sqrt (by positivity)
  have scale : 2*(N:ℝ)*z^2=u := by rw [z2]; field_simp
  have zmax : z≤0.1 := by
    apply (sq_le_sq₀ zpos.le (by norm_num : (0:ℝ)≤0.1)).mp
    rw [z2,div_le_iff₀ (by positivity)]
    linarith only [nr,uc]
  have z3 : z^3=ξ/S := by
    apply (sq_eq_sq₀ (by positivity) (div_nonneg nn sp.le)).mp
    change (ξ/S/2)^2=(u/N)^3/32 at phase
    rw [show (z^3)^2=(z^2)^3 by ring,z2]
    calc
      (u/(2*(N:ℝ)))^3=4*((u/N)^3/32) := by ring
      _=(ξ/S)^2 := by rw [← phase]; ring
  have cf := (signed_conditional_le_corank (z^3) n δ hs).trans (corank_inner_001 hs (by omega) zpos zmax)
  rw [z3,← Nat.cast_add (R:=ℝ),show 0.186*(2*(N:ℝ))*z^2=0.186*u by rw [mul_assoc,scale]] at cf
  have amp := (amplitude_le_magnitude n δ (ξ/S)).trans cf
  have trial : |spectralTrial ξ|≤1/10^14 := trial_tail (v:=u) ⟨by linarith only [low,ir],by linarith only [uc]⟩
  have price := scaledNegExp_sound (x:=0.186*(i:ℚ)/2) (by positivity)
  push_cast at price
  have ex := (Real.exp_le_exp.mpr (show -(0.186*u)≤-(0.186*(i:ℝ)/2) by linarith only [low])).trans price
  apply (abs_sub _ _).trans
  unfold outerCellAllowance
  push_cast
  linarith only [amp,trial,ex]

end CentralUnimodality.PolynomialTrial
