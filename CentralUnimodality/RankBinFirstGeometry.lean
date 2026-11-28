module

public import CentralUnimodality.RankBinSetup

/-! Geometry of a nonempty first-hit interval with the exact rounded cut
and the actual variance of the remaining labels. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic
open Real

theorem cutAt_bounds {B : SaddleBin} (hl : 0 ≤ B.fraction) (i : ℕ) :
    0 ≤ cutAt B i ∧ cutAt B i ≤ cutAt B (i+1) ∧ cutAt B (i+1) ≤ lateCut := by
  unfold cutAt
  exact ⟨le_min (by norm_num [lateCut]) (by positivity),min_le_min_left _ (by push_cast; linarith),min_le_left ..⟩

theorem hit_cut_geometry {m k : ℕ} (hm : 4096 ≤ m) {v w e chunk : ℚ}
    (hv : 0 ≤ v) (hvw : v ≤ w) (hw : w ≤ lateCut) (he : e=w+epsilon)
    (ht₀ : timeCut m v < 2*k+1) (ht₁ : 2*k+1 ≤ timeCut m w)
    (hx : chunk=v/3-2*epsilon) (hcore : 80 ≤ 4096*chunk) :
    (v:ℝ)*m ≤ 2*(k:ℝ)+1 ∧ 2*(k:ℝ)+1 ≤ (e:ℝ)*m ∧ 80 ≤ ((v:ℝ)/3-2/4096)*m ∧
      0 ≤ (e:ℝ) ∧ (e:ℝ) ≤ 15/16+1/4096 ∧ 2*k+1 ≤ m := by
  have hM : (4096:ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0<(m:ℝ) := by linarith
  have hw₀ : 0 ≤ (w:ℝ) := by exact_mod_cast hv.trans hvw
  have H₀ : (v:ℝ)*m ≤ timeCut m v := Nat.le_ceil _
  have H₁ : (timeCut m w:ℝ)<(w:ℝ)*m+1 := Nat.ceil_lt_add_one (by positivity)
  have ht : 2*(k:ℝ)+1 ≤ timeCut m w := by exact_mod_cast ht₁
  have he' : (e:ℝ)=(w:ℝ)+1/4096 := by rw [he]; norm_num [epsilon]
  have hex : (chunk:ℝ)=(v:ℝ)/3-2/4096 := by rw [hx]; norm_num [epsilon]
  have hcore' : (80:ℝ) ≤ 4096*(chunk:ℝ) := by exact_mod_cast hcore
  have hc₀ : 0 ≤ (chunk:ℝ) := by linarith only [hcore']
  have hcut : (w:ℝ) ≤ 15/16 := by simpa [lateCut] using (Rat.cast_le (K:=ℝ)).mpr hw
  have hhi : 2*(k:ℝ)+1 ≤ (e:ℝ)*m := by rw [he']; linarith only [ht,H₁,hM]
  have hecap : (e:ℝ) ≤ 15/16+1/4096 := by linarith only [he',hcut]
  have hn : 2*(k:ℝ)+1 ≤ m := hhi.trans (by nlinarith only [hp.le,mul_le_mul_of_nonneg_right hecap hp.le])
  refine ⟨H₀.trans (by exact_mod_cast ht₀.le),hhi,?_,by linarith only [he',hw₀],hecap,by exact_mod_cast hn⟩
  rw [← hex]
  exact hcore'.trans (by linarith only [mul_le_mul_of_nonneg_right hM hc₀])

theorem hit_suffix_scale {m k : ℕ} (hm : 4096 ≤ m) {c z γ shift G : ℝ} {v w e lo : ℚ}
    (hc : 0 ≤ c) (hz : 0 ≤ z) (hγ : γ=2*c*sizeScale m) (hΔ : shift=2*z*sizeScale m)
    (hG : γ ≤ G) (hcap : G+shift ≤ 57) (hv : 0 ≤ v) (hvw : v ≤ w) (hw : w ≤ lateCut)
    (he : e=w+epsilon) (hlo : (v:ℝ)*m ≤ 2*(k:ℝ)+1) (hhi : 2*(k:ℝ)+1 ≤ (e:ℝ)*m)
    (ht : 2*k+1 ≤ m) {lam : ℚ} (hlam : (lam:ℝ)=G+shift)
    (hroot : lo=rootLo ((1-(lam*(1-v)/128)^2)*(1-e)^3/12)) :
    sizeScale m*(lo:ℝ) ≤ √(suffixVariance (c+z) (m-(2*k+1))) := by
  have hM : 0 ≤ (m:ℝ) := Nat.cast_nonneg _
  have hs : 0 ≤ sizeScale m := by dsimp [sizeScale]; positivity
  have hLam : 0 ≤ G+shift := by
    have h₁ : 0 ≤ γ := hγ ▸ by positivity
    have h₂ : 0 ≤ shift := hΔ ▸ by positivity
    linarith only [h₁,h₂,hG]
  have hv₀ : 0 ≤ (v:ℝ) := by exact_mod_cast hv
  have hw₁ : (w:ℝ) ≤ 15/16 := by simpa [lateCut] using (Rat.cast_le (K:=ℝ)).mpr hw
  have hv₁ : (v:ℝ) ≤ 15/16 := ((Rat.cast_le (K:=ℝ)).mpr hvw).trans hw₁
  have he₁ : (e:ℝ) ≤ 1 := by rw [he]; norm_num [epsilon]; linarith only [hw₁]
  have hβ₀ : 0 ≤ 1-(v:ℝ) := by linarith only [hv₁]
  have hU : (G+shift)*(1-(v:ℝ)) ≤ 128 := by nlinarith only [hcap,mul_nonneg hLam hv₀]
  have hC : 2*(c+z)*sizeScale m ≤ G+shift := by linarith only [hγ,hΔ,hG]
  have hcut : ((m-(2*k+1):ℕ):ℝ)=(m:ℝ)-(2*(k:ℝ)+1) := by rw [Nat.cast_sub ht]; push_cast; rfl
  have H := (bin_suffix_scale hm (add_nonneg hc hz) hC (sub_nonneg.mpr he₁) hβ₀
    (show (1-(e:ℝ))*m ≤ (m-(2*k+1):ℕ) by rw [hcut]; linarith only [hhi])
    (show ((m-(2*k+1):ℕ):ℝ) ≤ (1-(v:ℝ))*m by rw [hcut]; linarith only [hlo]) hU).1
  let X := (1-(lam*(1-v)/128)^2)*(1-e)^3/12
  have eq : (X:ℝ)=(1-((G+shift)*(1-(v:ℝ))/128)^2)*(1-(e:ℝ))^3/12 := by
    dsimp only [X]; push_cast; rw [hlam]
  have hX : 0 ≤ (X:ℝ) := by
    rw [eq]
    have hratio : 0 ≤ (G+shift)*(1-(v:ℝ))/128 := by positivity
    have hup : (G+shift)*(1-(v:ℝ))/128 ≤ 1 := by linarith only [hU]
    apply div_nonneg (mul_nonneg _ (pow_nonneg (sub_nonneg.mpr he₁) 3)) (by norm_num)
    linarith only [pow_le_pow_left₀ hratio hup 2]
  have HH := (root_enclosure (show 0≤X by exact_mod_cast hX)).1
  rw [eq] at HH
  rw [hroot]
  exact (mul_le_mul_of_nonneg_left HH hs).trans H

end CentralUnimodality.MarkedExcursion.BinArithmetic
