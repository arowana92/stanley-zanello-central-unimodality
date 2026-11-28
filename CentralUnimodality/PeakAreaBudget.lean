module

public import CentralUnimodality.PeakBridgeCoordinates
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! An outward bound on the centered bridge mass from the uniformly
marked vertex, preserving the exponential until the two tilts combine. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic.Peak
open Real

theorem scaled_fair_hit {m d : ℕ} (hm : 4096≤m) {v r : ℝ} (hr : 0<r)
    (hv : 1/4096≤v) (hl : v*m≤2*(d:ℝ)+1) (hs : r≤√(v-1/4096)) :
    survival d/(2*(d+1)) ≤ (4/5)/r^3/sizeScale m := by
  have hM : (4096:ℝ)≤m := by exact_mod_cast hm
  have hm' : (0:ℝ)<m := by linarith only [hM]
  have hroot : r*√m≤√(2*(d:ℝ)) := calc
    _ ≤ √(v-1/4096)*√m := mul_le_mul_of_nonneg_right hs (sqrt_nonneg _)
    _ = √((v-1/4096)*m) := (sqrt_mul (sub_nonneg.mpr hv) _).symm
    _ ≤ _ := sqrt_le_sqrt (by linarith only [hl,hM])
  have hp := (mul_pos hr (sqrt_pos.mpr hm')).trans_le hroot
  have hd : 0<d := by
    by_contra! H
    have := Nat.eq_zero_of_le_zero H
    simp [this] at hp
  have H := (fair_hit_upper hd).le
  rw [fair_hit_survival] at H
  apply H.trans
  rw [div_div (4/5:ℝ) (r^3) (sizeScale m)]
  apply div_le_div_of_nonneg_left (by norm_num) (mul_pos (pow_pos hr 3) (mul_pos hm' (sqrt_pos.mpr hm')))
  have hs' := pow_le_pow_left₀ (mul_nonneg hr.le (sqrt_nonneg _)) hroot 3
  rw [mul_pow,pow_succ (√(m:ℝ)),pow_succ (√(2*(d:ℝ))),sq_sqrt hm'.le,sq_sqrt (by positivity)] at hs'
  exact hs'

theorem marked_bridge_budget {m d : ℕ} (hm : 4096≤m) {c : ℝ} (hc : 0≤c) (B : SaddleBin) (C : TimeBin)
    (hg : 0≤B.lower+C.shift) (hg' : ((B.lower+C.shift:ℚ):ℝ)≤2*c*sizeScale m)
    (hG : 2*c*sizeScale m≤C.lam) (hv : epsilon≤C.v) (hve : C.v≤C.e)
    (he : C.e≤1) (hmax : C.lam≤57) (hr : 0<rootLo (C.v-epsilon))
    (hl : (C.v:ℝ)*m≤2*(d:ℝ)+1) (hh : 2*(d:ℝ)+1≤(C.e:ℝ)*m) :
    (∑ w∈hitWords 1 (2*d+1),signMass c (c*d) w) ≤
      (areaBudget C:ℝ)/sizeScale m*
        exp (((C.lam*C.e/256+(areaY C)^2/4-areaSave B C:ℚ):ℝ)) := by
  let Y := (areaY C:ℝ)
  let y := c*(2*(d:ℝ)+1)*√((d:ℝ)+1)
  let p := (rootHi (22/7):ℝ)
  have hp : √π≤p := (sqrt_le_sqrt (show π≤((22/7:ℚ):ℝ) by push_cast; linarith only [pi_lt_d4])).trans
    (root_enclosure (by norm_num : (0:ℚ)≤22/7)).2
  have hv' : 1/4096≤(C.v:ℝ) := by simpa [epsilon] using (Rat.cast_le (K:=ℝ)).mpr hv
  have he' : 0≤(C.e:ℝ) := by
    have H := (Rat.cast_le (K:=ℝ)).mpr hve
    linarith only [hv',H]
  have hGN : 0≤(C.lam:ℝ) := (by dsimp [sizeScale]; positivity : 0≤2*c*sizeScale m).trans hG
  have hq : (C.lam:ℝ)*(C.e:ℝ)/256≤1 := by
    have HH := (Rat.cast_le (K:=ℝ)).mpr hmax
    have HC := (Rat.cast_le (K:=ℝ)).mpr he
    norm_num only [Rat.cast_ofNat,Rat.cast_one] at HH HC
    nlinarith only [mul_le_mul HH HC he' (by norm_num : (0:ℝ)≤57)]
  have hn : 0≤(C.e+epsilon)/2 := by
    have he₀ : 0≤C.e := by exact_mod_cast he'
    dsimp [epsilon]; positivity
  have hrt := (root_enclosure hn).2
  dsimp only [epsilon] at hrt; push_cast at hrt
  have ⟨hd,hy,hcst⟩ := centered_time_bounds hm hc (by exact_mod_cast hg) hg' hG hv' hl hh hrt hq
  have eqy : Y=(C.lam:ℝ)*(C.e:ℝ)*(rootHi ((C.e+epsilon)/2):ℝ)/2 := by dsimp [Y,areaY]; push_cast; rfl
  change y≤_ at hy
  dsimp only [epsilon] at eqy
  rw [← eqy] at hy
  have hy₀ : 0≤y := by dsimp [y]; positivity
  have hy' := mul_le_mul hy (add_le_add hp (min_le_min hp hy))
    (add_nonneg (sqrt_nonneg _) (le_min (sqrt_nonneg _) hy₀)) (hy₀.trans hy)
  have hb₁ : 1+y/2*(√π+min (√π) y)≤1+Y*(p+min p Y)/2 := by linarith only [hy']
  have hreal : (areaSave B C:ℝ)=((B.lower+C.shift:ℚ):ℝ)^2*(C.v:ℝ)*((C.v:ℝ)^2-(1/4096)^2)/96*
      (1-((C.lam:ℝ)*(C.e:ℝ)/256)^2/6) := by dsimp [areaSave,epsilon]; push_cast; rfl
  rw [← hreal] at hcst
  have hE : exp (c*d+y^2/4-c^2*d*(d+1)*(2*(d:ℝ)+1)/6*(1-(c*d)^2/6)) ≤
      exp (((C.lam*C.e/256+(areaY C)^2/4-areaSave B C:ℚ):ℝ)) := by
    apply exp_le_exp.mpr; push_cast
    dsimp only [Y] at hy
    linarith only [hd,hcst,pow_le_pow_left₀ hy₀ hy 2]
  have hf := scaled_fair_hit hm (by exact_mod_cast hr : 0<(rootLo (C.v-epsilon):ℝ)) hv' hl (by
    have HS := (root_enclosure (sub_nonneg.mpr hv)).1
    dsimp only [epsilon] at HS; push_cast at HS; exact HS)
  have H := tilted_hit_gaussian d hc
  have hfair := (div_nonneg (survival_pos d).le (by positivity : (0:ℝ)≤2*(d+1))).trans hf
  apply H.trans ((mul_le_mul (mul_le_mul hf hE (exp_pos _).le hfair) hb₁
    (by change 0≤1+y/2*(√π+min (√π) y); positivity) (mul_nonneg hfair (exp_pos _).le)).trans_eq _)
  dsimp only [areaBudget,p,Y]; push_cast; ring

end CentralUnimodality.MarkedExcursion.BinArithmetic.Peak
