module

public import CentralUnimodality.OppositePairEnergy
public import CentralUnimodality.RankBinSetup

/-! Rounded time cuts and the largest even block shared by all k blocks
give a pointwise bound at every frequency of a closed rational bin. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real BinArithmetic

def frequencyEnergy (v W ε A : ℚ) : ℚ := v^2*(W^3-W*ε^2)*(max 0 (1-A^2/6))^2/120

def blockFraction (k : ℕ) : ℚ := (17/20-1/4096)/k-2/4096
def binAngle (k : ℕ) (w : ℚ) : ℚ := w*(17/20+1/4096)/(128*k)

def binFactor (k : ℕ) (v w : ℚ) : ℚ :=
  let W := blockFraction k
  let A := binAngle k w
  3/8+upperNegExp (frequencyEnergy v W (1/4096) A)/2+
    upperNegExp (frequencyEnergy (2*v) W (1/4096) (2*A))/8

private theorem energy_cast (v W ε A : ℚ) : (frequencyEnergy v W ε A:ℝ) =
    (v:ℝ)^2*((W:ℝ)^3-W*(ε:ℝ)^2)*(max 0 (1-(A:ℝ)^2/6))^2/120 := by
  unfold frequencyEnergy; push_cast; rfl

private theorem energy_nonneg (v W ε A : ℚ) (h : 0≤W^3-W*ε^2) : 0≤frequencyEnergy v W ε A := by
  unfold frequencyEnergy; positivity

private theorem energy_abs (l : ℕ) (θ : ℝ) : oppositeEnergy l |θ|=oppositeEnergy l θ := by
  rcases le_total 0 θ with h|h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h]; dsimp only [oppositeEnergy]; congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_neg,neg_div,sin_neg,neg_sq]

private theorem cut_span {m : ℕ} (hm : 4096≤m) :
    let L := timeCut m (3/40)
    let T := timeCut m (37/40)
    0<L ∧ L≤T ∧ T≤m ∧ (17/20-1/4096)*(m:ℝ) ≤ (T-L:ℕ) ∧
      ((T-L:ℕ):ℝ) ≤ (17/20+1/4096)*(m:ℝ) := by
  let L := timeCut m (3/40)
  let T := timeCut m (37/40)
  have hM : (4096:ℝ)≤m := by exact_mod_cast hm
  have h₁ : (3/40:ℝ)*m ≤ L := by simpa [L,timeCut] using (Nat.le_ceil ((3/40:ℝ)*m))
  have h₂ : (L:ℝ)<(3/40:ℝ)*m+1 := by simpa [L,timeCut] using Nat.ceil_lt_add_one (by positivity : 0≤(3/40:ℝ)*m)
  have h₃ : (37/40:ℝ)*m ≤ T := by simpa [T,timeCut] using (Nat.le_ceil ((37/40:ℝ)*m))
  have h₄ : (T:ℝ)<(37/40:ℝ)*m+1 := by simpa [T,timeCut] using Nat.ceil_lt_add_one (by positivity : 0≤(37/40:ℝ)*m)
  have hLT : L≤T := by exact_mod_cast (show (L:ℝ)≤T by linarith)
  change 0<L ∧ L≤T ∧ T≤m ∧ _
  refine ⟨by exact_mod_cast (show (0:ℝ)<L by linarith),hLT,by exact_mod_cast (show (T:ℝ)≤m by linarith),?_⟩
  change _ ≤ ((T-L:ℕ):ℝ) ∧ ((T-L:ℕ):ℝ) ≤ _
  rw [Nat.cast_sub hLT]; constructor <;> linarith

theorem marked_block_geometry {m k : ℕ} (hm : 4096≤m) (hk : 0<k) {w : ℚ} {θ : ℝ}
    (hw : (m:ℝ)*√m*|θ|≤w) :
    let L := timeCut m (3/40)
    let T := timeCut m (37/40)
    let l := (T-L)/(2*k)
    0<L ∧ L≤T ∧ T≤m ∧ L≤T-k*(2*l) ∧ T=T-k*(2*l)+k*(2*l) ∧
      (blockFraction k:ℝ)*m ≤ 2*l ∧ (l:ℝ)*|θ| ≤ binAngle k w := by
  obtain ⟨hL,hLT,hT,hlo,hhi⟩ := cut_span hm
  let d := timeCut m (37/40)-timeCut m (3/40)
  let l := d/(2*k)
  have hk' : (0:ℝ)<k := by exact_mod_cast hk
  have hk₂ : 0<2*k := by omega
  have ha : (2*k)*l≤d := Nat.mul_div_le d (2*k)
  have hb : d<(2*k)*(l+1) := Nat.lt_mul_div_succ d hk₂
  have ha' : (2*(k:ℝ))*l≤d := by exact_mod_cast ha
  have hb' : (d:ℝ)<(2*(k:ℝ))*(l+1) := by exact_mod_cast hb
  have hm' : (4096:ℝ)≤m := by exact_mod_cast hm
  have hr : 64≤√(m:ℝ) := (le_sqrt (by norm_num) (Nat.cast_nonneg _)).mpr (by linarith)
  change (17/20-1/4096)*(m:ℝ)≤d at hlo
  change (d:ℝ)≤(17/20+1/4096)*(m:ℝ) at hhi
  rw [show 2*k*l=k*(2*l) by ring] at ha
  refine ⟨hL,hLT,hT,by dsimp [l,d] at ha; omega,by dsimp [l,d] at ha; omega,?_,?_⟩
  · change (blockFraction k:ℝ)*m≤2*l
    unfold blockFraction; push_cast
    apply le_of_mul_le_mul_left (a:=(k:ℝ)) _ hk'
    field_simp [hk'.ne']
    nlinarith only [hb',hlo,mul_le_mul_of_nonneg_right hm' hk'.le]
  · change (l:ℝ)*|θ|≤(binAngle k w:ℝ)
    unfold binAngle; push_cast
    apply (le_div_iff₀ (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right (ha'.trans hhi) (abs_nonneg θ)
    have hs := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg (α:=ℝ) m)) (abs_nonneg θ)
    linarith only [hh,hs,hw]

theorem marked_frequency_factor {m k : ℕ} (hm : 4096≤m) (hk : 0<k) {v w : ℚ} {θ : ℝ}
    (hv : 0≤v) (hlo : (v:ℝ)≤m*√m*|θ|) (hhi : (m:ℝ)*√m*|θ|≤w)
    (hW : 0≤blockFraction k) (hE : 0≤(blockFraction k)^3-blockFraction k*(1/4096)^2) :
    let l := (timeCut m (37/40)-timeCut m (3/40))/(2*k)
    twoHarmonicFactor l θ ≤ (binFactor k v w:ℝ) := by
  let l := (timeCut m (37/40)-timeCut m (3/40))/(2*k)
  let W := blockFraction k
  let A := binAngle k w
  obtain ⟨_,_,_,_,_,hblock,hangle⟩ := marked_block_geometry hm hk hhi
  have H (j : ℚ) (hj : 0≤j) :
      exp (-oppositeEnergy l (j*θ)) ≤ (upperNegExp (frequencyEnergy (j*v) W (1/4096) (j*A)):ℝ) := by
    have hj' : (0:ℝ)≤j := by exact_mod_cast hj
    have hab : |(j:ℝ)*θ|=j*|θ| := by rw [abs_mul,abs_of_nonneg hj']
    have hU : (l:ℝ)*|(j:ℝ)*θ|≤((j*A:ℚ):ℝ) := by
      rw [hab]; push_cast; linarith only [mul_le_mul_of_nonneg_left hangle hj']
    have hv' : ((j*v:ℚ):ℝ)≤m*√m*|(j:ℝ)*θ| := by
      rw [hab]; push_cast; linarith only [mul_le_mul_of_nonneg_left hlo hj']
    have hm' : (4096:ℝ)≤m := by exact_mod_cast hm
    have hε : 1≤((1/4096:ℚ):ℝ)*m := by norm_num; linarith only [hm']
    have HE := scaled_opposite_energy (m:=m) (by omega) (abs_nonneg ((j:ℝ)*θ)) hU
      (by exact_mod_cast hW : 0≤(W:ℝ)) hblock
      hε
      (by exact_mod_cast mul_nonneg hj hv) hv'
    rw [energy_abs,← energy_cast] at HE
    exact (exp_le_exp.mpr (neg_le_neg HE)).trans (upperNegExp_sound (energy_nonneg _ _ _ _ hE))
  have h₁ := H 1 (by decide)
  have h₂ := H 2 (by decide)
  norm_num only [Rat.cast_one,Rat.cast_ofNat,one_mul] at h₁ h₂
  change 3/8+exp (-oppositeEnergy l θ)/2+exp (-oppositeEnergy l (2*θ))/8 ≤ (binFactor k v w:ℝ)
  dsimp only [binFactor]; push_cast
  linarith only [h₁,h₂]

end CentralUnimodality.MarkedExcursion
