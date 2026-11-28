module

public import CentralUnimodality.PeakAreaBudget
public import CentralUnimodality.PeakLateProbability
public import CentralUnimodality.FifthsFirstHit
public import CentralUnimodality.RankBinExponent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! The two recorded early estimates bound the same tilted first-hit event.
The area exponent and the label exponent are combined before rounding. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic.Peak
open Real

def hitFactor (C : TimeBin) := if C.area then areaBudget C else fifthsBudget C
def earlyProb (B : SaddleBin) (C : TimeBin) := hitFactor C*decay (-(timeExponent B C))

theorem upper_base_exponent {m : ℕ} (hm : 4096≤m) {g γ d v e : ℝ}
    (hg : 0≤g) (hgγ : g≤γ) (hγ : γ≤25) (hd : 0≤d) (hv : 0≤v) :
    d^2*(labelSquares m/(m:ℝ)^3)/8-v*(1-e/2)^2*(γ+d)*(γ*(1-γ^2/(6*m))+d)/8 ≤
    d^2*(energy:ℝ)/8-v*(1-e/2)^2*(g+d)*(g*(1-g^2/(6*4096))+d)/8 := by
  have hbase := bin_cubic_drift (by exact_mod_cast hm : (4096:ℝ)≤m) hg hgγ hγ
  have hs := pow_le_pow_left₀ hg (hgγ.trans hγ) 2
  have hf : 0≤g*(1-g^2/(6*4096)) := mul_nonneg hg (by linarith only [hs])
  have H := mul_le_mul (add_le_add hgγ (le_refl d)) (add_le_add hbase (le_refl d))
    (add_nonneg hf hd) (add_nonneg (hg.trans hgγ) hd)
  linarith only [mul_le_mul_of_nonneg_left H (mul_nonneg hv (sq_nonneg (1-e/2))),
    mul_le_mul_of_nonneg_left (bin_energy hm) (sq_nonneg d)]

theorem fifths_budget_upper {m d : ℕ} (hm : 4096≤m) {c : ℝ} (hc : 0≤c) (B : SaddleBin) (C : TimeBin)
    (hOK : timeOK B C=true) (hβ : C.beta=C.lam*C.e/4) (hG : 2*c*sizeScale m≤C.lam)
    (hl : (C.v:ℝ)*m≤2*(d:ℝ)+1) (hh : 2*(d:ℝ)+1≤(C.e:ℝ)*m) :
    (∑ w∈hitWords 1 (2*d+1),signMass c (c*d) w)≤(fifthsBudget C:ℝ)/sizeScale m := by
  obtain ⟨_,_,_,_,_,_,hfr,hgr,_,_,_,_,hf₀,hg₀,hβmax,_⟩ := of_decide_eq_true hOK
  let f := C.v/5-2*epsilon
  let g := 3*C.v/5-epsilon
  have hM : (4096:ℝ)≤m := by exact_mod_cast hm
  have hf : 0<(f:ℝ) := by exact_mod_cast hf₀
  have hgR : 0≤g := by change 80≤4096*g at hg₀; linarith only [hg₀]
  have hgrR : 0<(rootLo g:ℝ) := by exact_mod_cast hgr
  have hm' : (0:ℝ)<m := by linarith only [hM]
  have hs : 0<sizeScale m := mul_pos hm' (sqrt_pos.mpr hm')
  have he : 0≤(C.e:ℝ) := by
    by_contra! H; linarith only [mul_nonpos_of_nonpos_of_nonneg H.le hm'.le,hh,Nat.cast_nonneg (α:=ℝ) d]
  have hLam : 0≤(C.lam:ℝ) := (by positivity : 0≤2*c*sizeScale m).trans hG
  have hβ' : (C.beta:ℝ)=(C.lam:ℝ)*(C.e:ℝ)/4 := by rw [hβ]; push_cast; rfl
  have hβ₀ : 0≤(C.beta:ℝ) := hβ' ▸ by positivity
  have hβH := (Rat.cast_le (K:=ℝ)).mpr hβmax
  rw [hβ] at hβH; push_cast at hβH
  have heqf : (f:ℝ)=(C.v:ℝ)/5-2/4096 := by dsimp [f,epsilon]; push_cast; ring
  have heqg : (g:ℝ)=3*(C.v:ℝ)/5-1/4096 := by dsimp [g,epsilon]; push_cast; rfl
  have hgF : (80:ℝ)≤4096*(g:ℝ) := by exact_mod_cast hg₀
  have hg' : (0:ℝ)≤(g:ℝ) := by exact_mod_cast hgR
  have hgM : 80≤(g:ℝ)*m := hgF.trans (by linarith only [mul_le_mul_of_nonneg_left hM hg'])
  have H := fifths_hit_budget hm hc hG hl hh hβH (heqf ▸ hf) (heqg ▸ hgM)
  dsimp only at H
  rw [← hβ',← heqf,← heqg] at H
  have hfin := live_budget_upper (a:=C.beta) hfr hf₀.le
  have hfn : 0≤discountedLive (C.beta:ℝ) (f:ℝ) := by dsimp [discountedLive]; positivity
  have hpow := pow_le_pow_left₀ hfn hfin 2
  have hcoef : 0≤1/2+(C.beta:ℝ)/128 := by positivity
  have hprod := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hcoef) (by norm_num : (0:ℝ)≤43/50)
  have hr := mul_le_mul_of_nonneg_right (root_enclosure hgR).1 hs.le
  apply H.trans ((div_le_div_of_nonneg_right hprod (by positivity)).trans _)
  change _≤(fifthsBudget C:ℝ)/sizeScale m
  unfold fifthsBudget; push_cast
  rw [div_div _ (rootLo g:ℝ) (sizeScale m)]
  exact div_le_div_of_nonneg_left (by positivity) (mul_pos hgrR hs) hr

theorem early_hit_probability {m d : ℕ} (hm : 4096≤m) {c γ : ℝ} (hc : 0≤c)
    (B : SaddleBin) (C : TimeBin) (hOK : timeOK B C=true) (hg : 0≤B.lower)
    (hgγ : (B.lower:ℝ)≤γ) (hγ : γ≤25)
    (hbase : C.base=C.shift^2*energy/8-C.v*(1-C.e/2)^2*(B.lower+C.shift)*(B.lower*(1-B.lower^2*epsilon/6)+C.shift)/8)
    (hβ : C.beta=C.lam*C.e/4) (hgam : 2*c*sizeScale m=γ+C.shift) (hG : γ+C.shift≤C.lam)
    (hl : (C.v:ℝ)*m≤2*(d:ℝ)+1) (hh : 2*(d:ℝ)+1≤(C.e:ℝ)*m) :
    let X := (C.shift:ℝ)^2*(labelSquares m/(m:ℝ)^3)/8-
      (C.v:ℝ)*(1-(C.e:ℝ)/2)^2*(γ+C.shift)*(γ*(1-γ^2/(6*m))+C.shift)/8
    exp X*(∑ w∈hitWords 1 (2*d+1),signMass c (c*d) w) ≤ (earlyProb B C:ℝ)/sizeScale m := by
  let X := (C.shift:ℝ)^2*(labelSquares m/(m:ℝ)^3)/8-
    (C.v:ℝ)*(1-(C.e:ℝ)/2)^2*(γ+C.shift)*(γ*(1-γ^2/(6*m))+C.shift)/8
  let s := sizeScale m
  have hs : 0<s := by
    have h : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
    exact mul_pos h (sqrt_pos.mpr h)
  obtain ⟨_,_,hv₀,hve,he,hvr,_,_,_,hd,_,hmax,_,_,_,hx⟩ := of_decide_eq_true hOK
  have hv : epsilon≤C.v := by linarith only [hv₀]
  have hv' : 0≤C.v := by dsimp [epsilon] at hv; linarith only [hv]
  have hX : X≤(C.base:ℝ) := by
    rw [hbase]; dsimp only [epsilon]; push_cast
    convert upper_base_exponent (d:=(C.shift:ℝ)) (v:=(C.v:ℝ)) (e:=(C.e:ℝ)) hm (by exact_mod_cast hg) hgγ hγ (by exact_mod_cast hd) (by exact_mod_cast hv') using 1; ring
  have hExp := decay_upper (neg_nonneg.mpr hx)
  simp only [Rat.cast_neg,neg_neg] at hExp
  have hG' := hgam.le.trans hG
  by_cases ha : C.area=true
  · let A := C.lam*C.e/256+(areaY C)^2/4-areaSave B C
    have H := marked_bridge_budget hm hc B C (add_nonneg hg hd) (by rw [hgam]; push_cast; linarith only [hgγ])
      hG' hv hve he.le hmax hvr hl hh
    let F := ∑ w∈hitWords 1 (2*d+1),signMass c (c*d) w
    have hF : 0≤F := Finset.sum_nonneg (fun _ _ => (signMass_pos ..).le)
    have hN : 0≤(areaBudget C:ℝ)/s := nonneg_of_mul_nonneg_left (hF.trans H) (exp_pos _)
    have heq : C.base+A=timeExponent B C := by simp only [A,timeExponent,ha,ite_true]; ring
    have HR := congrArg (fun q : ℚ => (q:ℝ)) heq
    push_cast only [Rat.cast_add] at HR
    have hexp := (exp_le_exp.mpr (show X+(A:ℝ)≤(timeExponent B C:ℝ) by linarith only [hX,HR])).trans hExp
    have pr := mul_le_mul_of_nonneg_left H (exp_pos X).le
    rw [show exp X*((areaBudget C:ℝ)/s*exp (A:ℝ))=(areaBudget C:ℝ)/s*exp (X+(A:ℝ)) by rw [exp_add]; ring] at pr
    apply pr.trans ((mul_le_mul_of_nonneg_left hexp hN).trans_eq _)
    simp only [earlyProb,hitFactor,ha,ite_true,Rat.cast_mul]; ring
  · have H := fifths_budget_upper hm hc B C hOK hβ hG' hl hh
    have hF := Finset.sum_nonneg (fun w (_ : w∈hitWords 1 (2*d+1)) => (signMass_pos c (c*d) w).le)
    have HE : timeExponent B C=C.base := by simp [timeExponent,ha]
    have e := (exp_le_exp.mpr hX).trans (show exp (C.base:ℝ)≤(decay (-(timeExponent B C)):ℝ) by rw [← HE]; exact hExp)
    apply (mul_le_mul e H hF ((exp_pos _).le.trans e)).trans_eq
    rw [show earlyProb B C=fifthsBudget C*decay (-(timeExponent B C)) by simp [earlyProb,hitFactor,ha]]
    push_cast; ring

end CentralUnimodality.MarkedExcursion.BinArithmetic.Peak
