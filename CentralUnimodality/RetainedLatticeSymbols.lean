module

public import CentralUnimodality.CorrectedLatticeSymbols
public import CentralUnimodality.NormalizedCells

/-! The corrected symbol error bounds on the full retained frequency
band, at every half-length from 300,000. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit
open Real Set Witness PowerSeries

theorem retained_scaling {N : ℕ} (hn : 300000≤N) {ξ : ℝ} (hξ : |ξ|≤1728) :
    let S := cellScale N
    let u := |ξ|^(2/3:ℝ)
    let τ := u/(N:ℝ)
    u∈Icc (0:ℝ) 144 ∧ 0≤τ ∧ (ξ/S/2)^2=τ^3/32 ∧ |ξ/S/2| *(2*(N:ℝ)+1)≤9/8 := by
  let S := cellScale N
  let u := |ξ|^(2/3:ℝ)
  have nn := abs_nonneg ξ
  have cube : u^3=ξ^2 := by dsimp only [u]; rw [← rpow_natCast _ 3,← rpow_mul nn]; norm_num
  have u0 : 0≤u := rpow_nonneg nn _
  have en : (300000:ℝ)≤N := by exact_mod_cast hn
  have np : (0:ℝ)<N := by linarith only [en]
  have sp : 0<S := cellScale_pos (by omega)
  have norm : S^2=(2*(N:ℝ))^3 := by dsimp [S,cellScale]; rw [mul_pow,sq_sqrt (by positivity)]; ring
  have cap : u≤144 := by
    apply le_of_pow_le_pow_left₀ (n:=3) (by decide) (by norm_num)
    rw [cube,← sq_abs]
    exact (pow_le_pow_left₀ nn hξ 2).trans (by norm_num)
  refine ⟨⟨u0,cap⟩,div_nonneg u0 np.le,?_,?_⟩
  · change (ξ/S/2)^2=(u/(N:ℝ))^3/32
    rw [div_pow,div_pow,div_pow,norm,← cube]; field_simp; ring
  · change |ξ/S/2| *(2*(N:ℝ)+1)≤9/8
    have rt : (774:ℝ)≤sqrt (2*N) := le_sqrt_of_sq_le (by linarith only [en])
    have h := mul_le_mul_of_nonneg_right hξ (show 0≤2*(N:ℝ)+1 by positivity)
    have t := mul_le_mul_of_nonneg_left rt (show 0≤2*(N:ℝ) by positivity)
    rw [abs_div,abs_div,abs_of_pos sp,abs_of_pos (by norm_num : (0:ℝ)<2)]
    field_simp [sp]
    dsimp only [S,cellScale]
    linarith only [h,t,en]

theorem retained_symbol_bounds {N j σ : ℕ} (hn : 300000≤N) (hj : j≤N) (hs : σ≤1) {ξ : ℝ}
    (hξ : |ξ|≤1728) :
    let ω := ξ/cellScale N/2
    let τ := |ξ|^(2/3:ℝ)/(N:ℝ)
    let v := j*τ
    ‖coeff (2*j+σ) (fairSeries (areaCharacter ω) words)-(freeCurve v*(1-τ*freeLogCorrection σ v):ℝ)‖
      ≤τ^2*(freeCurve v*freeLogRemainder v τ+freeCurve v*(freeLogCorrection σ v)^2/2) ∧
    ‖coeff (2*j) (fairSeries (areaCharacter ω) bridges)/(survival j:ℂ)-(bridgeCurve v*(1-τ*bridgeLogCorrection v):ℝ)‖
      ≤τ^2*(bridgeCurve v*bridgeLogRemainder v τ+bridgeCurve v*(bridgeLogCorrection v)^2/2) := by
  obtain ⟨_,t0,phase,angle⟩ := retained_scaling hn hξ
  have J : (j:ℝ)≤N := by exact_mod_cast hj
  have s : (σ:ℝ)≤1 := by exact_mod_cast hs
  have bound {a : ℝ} (h : a≤2*(N:ℝ)+1) := (mul_le_mul_of_nonneg_left h (abs_nonneg (ξ/cellScale N/2))).trans angle
  exact ⟨free_corrected_symbol hs t0 phase (bound (by linarith only [J,s])) _ rfl,
    bridge_corrected_symbol t0 phase (bound (by linarith only [J])) _ rfl⟩

end CentralUnimodality.ReturnSplit
