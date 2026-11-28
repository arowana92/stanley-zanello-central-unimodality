module

public import CentralUnimodality.PeakGrowthNumbers
public import CentralUnimodality.DiscountedLiveCap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Sound outward rounding of the survival discount and parity-reflection
factor for the last cut at 37/40 of the total length. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic.Peak
open Real

theorem live_budget_upper {a f : ℚ} (hf : 0<rootLo f) (hfn : 0≤f) :
    discountedLive (a:ℝ) (f:ℝ)≤(liveBudget a f:ℝ) := by
  have hrt : 0<(rootLo f:ℝ) := by exact_mod_cast hf
  have H := decay_upper (show 0≤(12/25)*a^2*f from mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hfn)
  push_cast at H
  have Q := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤4/5) hrt (root_enclosure hfn).1
  have V := mul_le_mul Q H (exp_pos _).le (by positivity)
  dsimp only [discountedLive,liveBudget]; push_cast
  rw [show -(12/25:ℝ)*(a:ℝ)^2*(f:ℝ)= -(12/25*(a:ℝ)^2*(f:ℝ)) by ring]
  exact add_le_add (le_refl _) (V.trans_eq (by ring))

def lateProb (B : SaddleBin) (C : LateBin) :=
  decay (-C.expo)*(min 1 ((21/25)/(C.height*rootLo (1-finalCut-epsilon))))*
    liveBudget C.cap firstCut/B.denom

theorem late_prob_bound {B : SaddleBin} {C : LateBin} {m : ℕ} {c E : ℝ}
    (hm : 4096≤m) (hd : 0<B.denom) (ha : 0<C.height) (hc : 0≤C.cap)
    (hc' : C.cap≤6/25*64) (hden : (B.denom:ℝ)≤live c (c*m) (timeCut m firstCut) 1*√m)
    (hE : 0≤E) (hex : E≤(decay (-C.expo):ℝ)) :
    let L := timeCut m firstCut
    let T := timeCut m finalCut
    E*reflectedLateFactor ((C.height:ℝ)/√m) (m-T)*liveCap ((C.cap:ℝ)/√m) L ≤
      live c (c*m) L 1*(lateProb B C:ℝ) := by
  let L := timeCut m firstCut
  let T := timeCut m finalCut
  let P := live c (c*m) L 1
  let f := 1-finalCut-epsilon
  have hM : (4096:ℝ)≤m := by exact_mod_cast hm
  have hm' : (0:ℝ)<m := by linarith
  have hr := sqrt_pos.mpr hm'
  have hr64 : 64≤√(m:ℝ) := (le_sqrt (by norm_num) hm'.le).mpr (by linarith only [hM])
  have hcR : 0≤(C.cap:ℝ) := by exact_mod_cast hc
  have haR : 0<(C.height:ℝ) := by exact_mod_cast ha
  have hdR : 0<(B.denom:ℝ) := by exact_mod_cast hd
  have hPP : 0<P := pos_of_mul_pos_left (hdR.trans_le hden) hr.le
  have hL : (firstCut:ℝ)*m≤L := Nat.le_ceil _
  have hT : (T:ℝ)<(finalCut:ℝ)*m+1 := Nat.ceil_lt_add_one (by norm_num [finalCut])
  have ht : T≤m := by
    norm_num [finalCut] at hT
    exact_mod_cast (show (T:ℝ)≤m by linarith only [hT,hM])
  have hpart : (f:ℝ)*m≤(m-T:ℕ) := by
    rw [Nat.cast_sub ht]; dsimp only [f,epsilon]; push_cast
    linarith only [hT,hM]
  have hf : 0≤f := by decide +kernel
  have hrt : 0<(rootLo f:ℝ) := by exact_mod_cast (show 0<rootLo f by decide +kernel)
  have hh : (rootLo f:ℝ)*√m≤√(m-T:ℕ) := calc
    _ ≤ √(f:ℝ)*√m := mul_le_mul_of_nonneg_right (root_enclosure hf).1 hr.le
    _ = √((f:ℝ)*m) := (sqrt_mul (by exact_mod_cast hf) _).symm
    _ ≤ _ := sqrt_le_sqrt hpart
  have hprod : (C.height:ℝ)*(rootLo f:ℝ)≤(C.height:ℝ)/√m*√(m-T:ℕ) := by
    have H := mul_le_mul_of_nonneg_left hh (div_nonneg haR.le hr.le)
    rwa [show (C.height:ℝ)/√m*((rootLo f:ℝ)*√m)=(C.height:ℝ)*(rootLo f:ℝ) by field_simp] at H
  let Q := min 1 ((21/25)/(C.height*rootLo f))
  have hq : reflectedLateFactor ((C.height:ℝ)/√m) (m-T)≤(Q:ℝ) := by
    dsimp only [reflectedLateFactor,Q]; push_cast
    exact min_le_min_left _ (div_le_div_of_nonneg_left (by norm_num) (mul_pos haR hrt) hprod)
  have hq₀ : 0≤reflectedLateFactor ((C.height:ℝ)/√m) (m-T) := le_min (by norm_num) (by positivity)
  have hcap : (C.cap:ℝ)/√m≤6/25 := (div_le_iff₀ hr).mpr (by
    have H := (Rat.cast_le (K:=ℝ)).mpr hc'; push_cast at H; linarith only [H,hr64])
  have liveBound := scaled_live_cap (by omega : 0<m) (show 0<(firstCut:ℝ) by norm_num [firstCut]) hL hcR hcap
  have hb := live_budget_upper (a:=C.cap) (show 0<rootLo firstCut by decide +kernel) (show 0≤firstCut by decide +kernel)
  have hbudget : 0≤(liveBudget C.cap firstCut:ℝ) := (show 0≤discountedLive (C.cap:ℝ) (firstCut:ℝ) by
    dsimp only [discountedLive]; positivity).trans hb
  let U := (liveBudget C.cap firstCut:ℝ)
  have H : liveCap ((C.cap:ℝ)/√m) L≤P*U/B.denom := by
    apply (liveBound.trans (div_le_div_of_nonneg_right hb hr.le)).trans
    apply (div_le_div_iff₀ hr hdR).mpr
    linarith only [mul_le_mul_of_nonneg_right hden hbudget]
  have hleft := mul_nonneg hE hq₀
  have hfirst := mul_le_mul hex hq hq₀ (hE.trans hex)
  have H' := (mul_le_mul_of_nonneg_left H hleft).trans (mul_le_mul_of_nonneg_right hfirst (by positivity : 0≤P*U/(B.denom:ℝ)))
  apply H'.trans_eq
  dsimp only [lateProb,Q,U,f]; push_cast; ring

end CentralUnimodality.MarkedExcursion.BinArithmetic.Peak
