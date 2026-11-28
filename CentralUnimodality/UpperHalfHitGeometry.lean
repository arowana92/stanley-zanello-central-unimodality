module

public import CentralUnimodality.UpperHalfFirstSuffix
public import CentralUnimodality.PinnedFirstHit

/-! The middle third of a centered first hit always has small single-site
parameters. The original and remaining suffix scales use the same tilt. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

theorem far_pinned_hit {m d : ℕ} (hm : 4096 ≤ m) (ht : 2*d+1 ≤ m)
    {c v e γ : ℝ} (hc : 0 ≤ c) (hcm : c*m ≤ 1) (hγ : γ=2*c*((m:ℝ)*√m))
    (hlo : v*m ≤ 2*(d:ℝ)+1) (hhi : 2*(d:ℝ)+1 ≤ e*m) (hcore : 80 ≤ (v/3-2/4096)*m) :
    let R := √(v/3-2/4096)
    (∑ w ∈ hitWords 1 (2*d+1), signMass c (c*d) w) ≤ (γ*e/2+(4/5)/R)^2/(R*((m:ℝ)*√m)) := by
  have hprob : upChance (c*d) ≤ 1 := by
    have hn : 0 ≤ upChance (-(c*d)) := by dsimp only [upChance]; positivity
    linarith only [up_total (c*d),hn]
  let a := (2*d+1)/3
  have hmid (i : ℕ) (hi : i ∈ Finset.range ((2*d+1)-2*a)) :
      |c*d-c*a-c*i| ≤ 21/100 := by
    have hi' := Finset.mem_range.mp hi
    have ha : 6*d ≤ m+1+6*a := by dsimp only [a]; omega
    have hb : 6*a+6*i ≤ m+1+6*d := by dsimp only [a] at *; omega
    have ha' : 6*(d:ℝ) ≤ m+1+6*(a:ℝ) := by exact_mod_cast ha
    have hb' : 6*(a:ℝ)+6*i ≤ m+1+6*(d:ℝ) := by exact_mod_cast hb
    have hM : (4:ℝ) ≤ m := by exact_mod_cast (show 4≤m by omega)
    have hc' : c ≤ 1/4 := by linarith only [mul_le_mul_of_nonneg_left hM hc,hcm]
    apply abs_le.mpr ⟨?_,?_⟩
    · linarith only [mul_le_mul_of_nonneg_left hb' hc,hcm,hc']
    · linarith only [mul_le_mul_of_nonneg_left ha' hc,hcm,hc',mul_nonneg hc (Nat.cast_nonneg (α:=ℝ) i)]
  have H := pinned_hit_bin_of_middle hm hc hγ hprob hmid hlo hhi hcore
  dsimp only at H ⊢
  simpa only [one_mul,show 2*(γ*e/4)=γ*e/2 by ring] using H

theorem far_suffix_ratio {m L t : ℕ} (hm : 0<m) (hLt : L ≤ t) (ht : t ≤ m) {e c σ σ' : ℝ}
    (he : 0 ≤ e) (he' : e<1) (hcut : (t:ℝ) ≤ e*m) (hσ : 0 ≤ σ) (hσ' : 0<σ')
    (hV : suffixVariance c (m-L)=σ^2) (hV' : suffixVariance c (m-t)=σ'^2)
    (r : Fin 3) (hr : r.val ≤ 1) : (σ/σ')^(r.val+1) ≤ 1/(1-e)^3 := by
  have hmp : 0<(m:ℝ) := by exact_mod_cast hm
  have hex : 0<1-e := by linarith
  have hpos : 0<m-t := by
    have H : (t:ℝ)<m := hcut.trans_lt (by nlinarith only [mul_lt_mul_of_pos_right he' hmp])
    have hn : t<m := by exact_mod_cast H
    omega
  have h := suffix_variance_ratio c hpos (Nat.sub_le_sub_left hLt m)
  rw [hV,hV'] at h
  have hmB : (1-e)*(m:ℝ) ≤ (m-t:ℕ) := by rw [Nat.cast_sub ht]; linarith only [hcut]
  have h₀ := pow_le_pow_left₀ (mul_nonneg hex.le hmp.le) hmB 3
  rw [mul_pow] at h₀
  have h₁ := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) (m-L)) (show ((m-L:ℕ):ℝ) ≤ m by exact_mod_cast Nat.sub_le m L) 3
  have H : σ^2*(1-e)^3 ≤ σ'^2 := by
    apply le_of_mul_le_mul_right (a:=(m:ℝ)^3) _ (pow_pos hmp 3)
    linarith only [mul_le_mul_of_nonneg_left h₀ (sq_nonneg σ),h,mul_le_mul_of_nonneg_left h₁ (sq_nonneg σ')]
  have H₂ : (σ/σ')^2 ≤ 1/(1-e)^3 := by
    rw [div_pow,div_le_div_iff₀ (pow_pos hσ' 2) (pow_pos hex 3),one_mul]; exact H
  have cap : 1 ≤ 1/(1-e)^3 := (one_le_div (pow_pos hex 3)).mpr
    (by simpa using pow_le_pow_left₀ hex.le (by linarith only [he] : 1-e ≤ 1) 3)
  fin_cases r
  · change (σ/σ')^1 ≤ _
    rw [pow_one]; by_cases hratio : 1 ≤ σ/σ'
    · exact (by nlinarith only [mul_nonneg (sub_nonneg.mpr hratio) (div_nonneg hσ hσ'.le)] : σ/σ' ≤ (σ/σ')^2).trans H₂
    · exact (le_of_not_ge hratio).trans cap
  · exact H₂
  · exact False.elim (by norm_num at hr)

end CentralUnimodality.MarkedExcursion
