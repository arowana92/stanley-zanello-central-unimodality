module

public import CentralUnimodality.RankBinSetup

/-! Cover the continuum of original saddles by the certified bins. The
rightmost interval includes its upper endpoint. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic
open Real

def corankStart (curve : Bool) : ℚ := if curve then 15/16 else 3/4

theorem checked_cover (curve : Bool) {γ : ℝ}
    (hl : (1199/100)*(corankStart curve:ℝ) ≤ γ) (hu : γ ≤ 25) :
    ∃ i : ℕ, checkSigns curve i=true ∧ ((saddleBin curve i).lower:ℝ) ≤ γ ∧
      γ ≤ ((saddleBin curve i).upper:ℝ) := by
  let b : ℝ := (1199/100)*(corankStart curve:ℝ)
  let i := ⌊(γ-b)/2⌋₊
  have h₁ : (i:ℝ) ≤ (γ-b)/2 := Nat.floor_le (by linarith only [hl,show b=(1199/100)*(corankStart curve:ℝ) from rfl])
  have h₂ : (γ-b)/2 < (i:ℝ)+1 := Nat.lt_floor_add_one _
  have hbase : ((saddleBin curve i).lower:ℝ)=b+2*i := by
    cases curve <;> norm_num [saddleBin,corankStart,b]
  have hc : checkSigns curve i=true := by
    cases curve
    · apply growth_bin_checks (i := ⟨i,?_⟩)
      have he : b=(1199/100)*(3/4:ℝ) := by norm_num [b,corankStart]
      have hn : (i:ℝ)<9 := by linarith only [h₁,he,hu]
      exact_mod_cast hn
    · apply curvature_bin_checks (i := ⟨i,?_⟩)
      have he : b=(1199/100)*(15/16:ℝ) := by norm_num [b,corankStart]
      have hn : (i:ℝ)<7 := by linarith only [h₁,he,hu]
      exact_mod_cast hn
  refine ⟨i,hc,by rw [hbase]; linarith only [h₁],?_⟩
  change γ ≤ ((min 25 ((saddleBin curve i).lower+2):ℚ):ℝ)
  rw [Rat.cast_min,Rat.cast_add,hbase]
  norm_num only [Rat.cast_ofNat]
  exact le_min hu (by linarith only [h₂])

/-- Choose a positive saddle and a checked row for the requested rank,
for both the growth window and its narrower curvature window. -/
theorem checked_rank_saddle (curve : Bool) {m k : ℕ} (hm : 4096 ≤ m) (hk : k ≤ staircaseDegree m)
    (hlo : (corankStart curve:ℝ)*sizeScale m ≤ (staircaseDegree m:ℝ)-k)
    (hhi : (staircaseDegree m:ℝ)-k ≤ 2*sizeScale m) :
    ∃ (i : ℕ) (c : ℝ), checkSigns curve i=true ∧ SaddleAt (saddleBin curve i) m c ∧
      meanRank c m=k := by
  obtain ⟨c,hc,he,h₁,h₂⟩ := saddle_rank hm hk hhi
  have hp : 0<(m:ℝ) := by exact_mod_cast (show 0<m by omega)
  have hs : 0<sizeScale m := mul_pos hp (sqrt_pos.mpr hp)
  let γ := 2*c*sizeScale m
  have hlow : (1199/100)*(corankStart curve:ℝ) ≤ γ := by
    apply (le_of_mul_le_mul_right _ hs)
    change _ ≤ γ*sizeScale m at h₁
    linarith only [hlo,h₁]
  have hstart : 0<(corankStart curve:ℝ) := by cases curve <;> norm_num [corankStart]
  have hc' : 0<c := by
    by_contra! H
    have hu : γ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hs.le
    linarith only [hlow,hstart,hu]
  obtain ⟨i,hi,hg,hG⟩ := checked_cover curve hlow h₂.le
  exact ⟨i,c,hi,⟨hm,hc',hg,hG⟩,he⟩

end CentralUnimodality.MarkedExcursion.BinArithmetic
