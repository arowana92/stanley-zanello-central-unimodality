module

public import CentralUnimodality.PeakGrowthWitnesses
public import CentralUnimodality.LivePrefixVariance
public import CentralUnimodality.ScaledPrefixSurvival
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Enclose the genuine independent suffix variance and surviving prefix
mass with the outward-rounded numbers used by the inner growth bins. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic.Peak
open Real

theorem prefix_scales {m i : ℕ} {c : ℝ} (h : SaddleAt (bin i) m c) (hG : (bin i).upper≤9) :
    let B := bin i
    let L := timeCut m firstCut
    let σ := √(suffixVariance c (m-L))
    sizeScale m*(B.zlo:ℝ)≤σ ∧ σ≤sizeScale m*(B.zhi:ℝ) := by
  let B := bin i
  let L := timeCut m firstCut
  let f := firstCut+epsilon
  have hM : (4096:ℝ)≤m := by exact_mod_cast h.large
  have hm : (0:ℝ)<m := by linarith
  have hs : 0≤sizeScale m := by dsimp [sizeScale]; positivity
  have hgn : 0≤(B.upper:ℝ) := (mul_nonneg (by linarith only [h.positive] : 0≤2*c) hs).trans h.upper
  have hG' : (B.upper:ℝ)≤9 := by exact_mod_cast hG
  obtain ⟨_,hLT,hTm,_,hL,_⟩ := cut_geometry h.large (show 1/14≤firstCut by decide +kernel) (show firstCut≤1/10 by decide +kernel)
  have hl : (firstCut:ℝ)*m≤L := Nat.le_ceil _
  have hLm : L≤m := hLT.le.trans hTm
  have hlo : (1-(f:ℝ))*m≤(m-L:ℕ) := by rw [Nat.cast_sub hLm]; change (L:ℝ)≤(f:ℝ)*m at hL; linarith only [hL]
  have hhi : ((m-L:ℕ):ℝ)≤(1-(firstCut:ℝ))*m := by rw [Nat.cast_sub hLm]; linarith only [hl]
  have hf : 0≤1-(f:ℝ) := by norm_num [f,firstCut,epsilon]
  have Hlo := (bin_suffix_scale h.large h.positive.le h.upper hf zero_le_one hlo
    (show ((m-L:ℕ):ℝ)≤1*m by rw [one_mul]; exact_mod_cast Nat.sub_le m L) (by linarith only [hG'])).1
  have Hhi := (bin_suffix_scale h.large h.positive.le h.upper hf (by norm_num [firstCut] : 0≤1-(firstCut:ℝ)) hlo hhi
    (by norm_num [firstCut]; linarith only [hG'])).2
  let X := (1-(B.upper/128)^2)*(1-f)^3/12
  let Y := (1-firstCut+epsilon)^3/12
  have hX : 0≤X := by
    have h₀ : 0≤B.upper := by exact_mod_cast hgn
    have h₁ : B.upper/128≤1 := by linarith only [hG]
    have h₂ := pow_le_pow_left₀ (div_nonneg h₀ (by norm_num : (0:ℚ)≤128)) h₁ 2
    dsimp only [X]
    exact div_nonneg (mul_nonneg (by linarith only [h₂]) (pow_nonneg (by decide +kernel : 0≤1-f) 3)) (by norm_num)
  have hx := (root_enclosure hX).1
  dsimp only [X] at hx; push_cast at hx
  have hy := (root_enclosure (show 0≤Y by decide +kernel)).2
  dsimp only [Y,firstCut,epsilon] at hy; push_cast at hy
  change sizeScale m*(rootLo X:ℝ)≤_ ∧ _≤sizeScale m*(rootHi Y:ℝ)
  constructor
  · apply (mul_le_mul_of_nonneg_left hx hs).trans
    simpa only [L,B,sizeScale,mul_one,Rat.cast_sub,Rat.cast_one] using Hlo
  · apply Hhi.trans
    apply mul_le_mul_of_nonneg_left _ hs
    simpa only [firstCut,Y,epsilon,Rat.cast_div,Rat.cast_ofNat] using hy

theorem prefix_denominator {m i : ℕ} {c : ℝ} (h : SaddleAt (bin i) m c)
    (hg : 0≤(bin i).lower) (hx : survivalExponent (bin i).lower≤256) :
    ((bin i).denom:ℝ) ≤ live c (c*m) (timeCut m firstCut) 1*√m := by
  let B := bin i
  let f := firstCut+epsilon
  let U := prefixU B.lower
  let L := timeCut m firstCut
  have hM : (4096:ℝ)≤m := by exact_mod_cast h.large
  have hm : (0:ℝ)<m := by linarith
  have hr := sqrt_pos.mpr hm
  have hl : (firstCut:ℝ)*m≤L := Nat.le_ceil _
  have hL : 255≤L := by
    norm_num [firstCut] at hl
    exact_mod_cast (show (255:ℝ)≤L by linarith only [hM,hl])
  have hLf := (cut_geometry h.large (show 1/14≤firstCut by decide +kernel) (show firstCut≤1/10 by decide +kernel)).2.2.2.2.1
  change (L:ℝ)≤(f:ℝ)*m at hLf
  have hK : (0:ℝ)<(prefixK:ℝ) := by exact_mod_cast (show 0<prefixK by decide +kernel)
  have hscale : (prefixK:ℝ)*√(f:ℝ)≤79/100 := by
    apply (mul_le_mul_of_nonneg_left (root_enclosure (show 0≤f by decide +kernel)).2 hK.le).trans
    have HC := (Rat.cast_le (K:=ℝ)).mpr (show prefixK*rootHi f≤79/100 by decide +kernel)
    push_cast at HC; exact HC
  have hf : 0≤1-(f:ℝ) := by norm_num [f,firstCut,epsilon]
  have hu : (U:ℝ)=(B.lower:ℝ)*(1-(f:ℝ))/2 := by dsimp only [U,prefixU,f]; push_cast; rfl
  have hU : 0≤(U:ℝ) := hu ▸ div_nonneg (mul_nonneg (by exact_mod_cast hg) hf) (by norm_num)
  have hpar (t : ℕ) (ht : t<L) : (U:ℝ)/√m≤c*m-c*t := by
    apply (div_le_iff₀ hr).mpr
    have htime : (t:ℝ)≤(f:ℝ)*m := (show (t:ℝ)≤L by exact_mod_cast ht.le).trans hLf
    have HC := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htime h.positive.le) hr.le
    have HS := mul_le_mul_of_nonneg_right h.lower hf
    change (B.lower:ℝ)*(1-(f:ℝ))≤2*c*((m:ℝ)*√m)*(1-(f:ℝ)) at HS
    rw [hu]; linarith only [HC,HS]
  have H := scaled_prefix_survival h.large hL hU (by norm_num [f,firstCut,epsilon] : 0≤(f:ℝ)) hK hscale hLf hpar
  let x := survivalExponent B.lower
  have he := lowerExp_le hx
  change (lowerExp x:ℝ)≤exp (-(x:ℝ)) at he
  have heq : (x:ℝ)=(U:ℝ)/64+(U:ℝ)/(prefixK:ℝ)+(f:ℝ)*(U:ℝ)^2/2 := by
    dsimp only [x,survivalExponent,U,f]; push_cast; rfl
  rw [heq] at he
  apply ((Rat.cast_le (K:=ℝ)).mpr (lowerGrid_le (2*U*(1-U/64)+prefixK*lowerExp x))).trans
  push_cast
  exact (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left he hK.le)).trans H

end CentralUnimodality.MarkedExcursion.BinArithmetic.Peak
