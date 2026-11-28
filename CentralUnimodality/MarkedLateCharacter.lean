module

public import CentralUnimodality.MarkedFrequencyGrid
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Apply the closed-bin Fourier estimates to the actual discarded
late-crossing rank transform at both signs of the frequency. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real BinArithmetic FrequencyGrid

theorem chance_interval {A x : ℝ} (h : |x|≤A) :
    (1-A)/2 ≤ upChance (-x) ∧ upChance (-x) ≤ (1+A)/2 := by
  have ht : -A≤tanh x ∧ tanh x≤A := by
    rcases le_total 0 x with hx|hx
    · have hp : 0≤tanh x := by rw [tanh_eq_sinh_div_cosh]; exact div_nonneg (sinh_nonneg_iff.mpr hx) (cosh_pos _).le
      exact ⟨by linarith only [(abs_nonneg x).trans h,hp],(tanh_le_linear hx).trans (abs_le.mp h).2⟩
    · have hp : tanh x≤0 := by rw [tanh_eq_sinh_div_cosh]; exact div_nonpos_of_nonpos_of_nonneg (sinh_nonpos_iff.mpr hx) (cosh_pos _).le
      have hh := tanh_le_linear (neg_nonneg.mpr hx)
      rw [tanh_neg] at hh
      exact ⟨by linarith only [hh,(abs_le.mp h).1],hp.trans ((abs_nonneg x).trans h)⟩
  constructor <;> linarith only [ht.1,ht.2,up_total x,up_drift x]

theorem marked_wall_transform {v b U : ℝ} {m : ℕ} (hm : 4096≤m)
    (hv : 0≤v) (hb' : b≤6/25) (hU' : U≤6/25) (hcap : v*m-b≤U)
    (i : Fin 180) {θ : ℝ} (hlo : (edge i:ℝ)≤sizeScale m*|θ|) (hhi : sizeScale m*|θ|≤(edge (i+1:ℕ):ℝ)) :
    let L := timeCut m (3/40)
    let T := timeCut m (37/40)
    endpointNorm (wallRow v (v*m-b) m θ 0 T) ≤ live v (v*m-b) L 1*(weight i:ℝ) := by
  let L := timeCut m (3/40)
  let T := timeCut m (37/40)
  let k := blocks i
  let l := (T-L)/(2*k)
  let p := T-k*(2*l)
  have hk : 0<k := by dsimp [k,blocks]; omega
  obtain ⟨_,_,hT,hpL,hpT,_,_⟩ := marked_block_geometry hm hk hhi
  change T≤m at hT
  have hblocks : T=p+k*(2*l) := hpT
  have hpre (j : ℕ) : v*m-b-v*j≤U := by linarith only [hcap,mul_nonneg hv (Nat.cast_nonneg (α:=ℝ) j)]
  have H := opposite_wall_powers v (v*m-b) m θ 0 p l k (by
    intro j _ hj
    have hjm : (j:ℝ)≤m := by exact_mod_cast hj.le.trans (hblocks ▸ hT)
    have hA : |v*m-b-v*j|≤6/25 := abs_le.mpr ⟨by
      linarith only [mul_le_mul_of_nonneg_left hjm hv,hb'],(hpre j).trans hU'⟩
    have h := chance_interval hA
    exact ⟨(by norm_num : (9/25:ℝ)≤(1-6/25)/2).trans h.1,h.2.trans_eq (by norm_num)⟩)
  rw [← hblocks] at H
  change endpointNorm (wallRow v (v*m-b) m θ 0 T)≤(∑ w ∈ ballots p, signMass v (v*m-b) w)*(twoHarmonicFactor l θ)^k at H
  rw [← live_ballots] at H
  have hρ : 0≤(twoHarmonicFactor l θ)^k := by dsimp only [twoHarmonicFactor]; positivity
  exact H.trans (mul_le_mul (live_length_antitone v (v*m-b) hpL) (bin_bounds hm i hlo hhi) hρ (live_nonneg ..))

end CentralUnimodality.MarkedExcursion
