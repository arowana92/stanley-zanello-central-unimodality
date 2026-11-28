module

public import CentralUnimodality.QuarticLatticeLogs

/-! Explicit local log defects in the variables v=jτ and ω²=τ³/32.
Each remainder is nonnegative, including the two parity endpoints. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit

noncomputable def freeLogCorrection (σ : ℕ) (v : ℝ) := (2*σ+1:ℝ)*v^2/32+v^5/1920
noncomputable def bridgeLogCorrection (v : ℝ) := v^2/192+v^5/30720
noncomputable def freeLogRemainder (v τ : ℝ) := 13*v/192+τ/64+(v+τ)^4/384+(1/20)*(v+τ)^7/1792
noncomputable def bridgeLogRemainder (v τ : ℝ) :=
  (7*v^4+2*τ*v^3)/(180*32^2)+(1/1000)*(v+τ)^7/1792

private theorem fourth_power_bounds (t : ℕ) :
    (t:ℝ)^5/5≤fourthSum t ∧ fourthSum t≤((t:ℝ)+1)^5/5 := by
  induction t with
  | zero => norm_num [fourthSum]
  | succ t ih =>
    rw [fourthSum,Finset.sum_range_succ,← fourthSum,Nat.cast_succ]
    have n : 0≤(t:ℝ) := by positivity
    have a : 0≤(t:ℝ)^5/5+(t+1:ℝ)^4-(t+1:ℝ)^5/5 := by ring_nf; positivity
    have b : 0≤((t:ℝ)+1+1)^5/5-((t:ℝ)+1)^5/5-((t:ℝ)+1)^4 := by ring_nf; positivity
    constructor <;> linarith only [ih.1,ih.2,a,b]

private theorem sixth_power_bound (t : ℕ) : sixthSum t≤((t:ℝ)+1)^7/7 := by
  induction t with
  | zero => norm_num [sixthSum]
  | succ t ih =>
    rw [sixthSum,Finset.sum_range_succ,← sixthSum,Nat.cast_succ]
    have b : 0≤((t:ℝ)+1+1)^7/7-((t:ℝ)+1)^7/7-((t:ℝ)+1)^6 := by ring_nf; positivity
    linarith only [ih,b]

private theorem sixth_scaled {j t : ℕ} (ht : t≤2*j+1) {ω τ : ℝ} (hτ : 0≤τ) (hω : ω^2=τ^3/32) :
    ω^6*sixthSum t≤τ^2*((j:ℝ)*τ+τ)^7/1792 := by
  have hi : (t:ℝ)+1≤2*j+2 := by exact_mod_cast (show t+1≤2*j+2 by omega)
  have T := pow_le_pow_left₀ (by positivity) hi 7
  have sc : ω^6=(τ^3/32)^3 := by rw [← hω]; ring
  rw [sc]
  apply (mul_le_mul_of_nonneg_left (sixth_power_bound t) (by positivity : 0≤(τ^3/32)^3)).trans
  apply (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right T (by norm_num : (0:ℝ)≤7))
    (by positivity : 0≤(τ^3/32)^3)).trans_eq
  ring

private theorem fourth_scaled {j σ : ℕ} (hs : σ≤1) {ω τ : ℝ} (hω : ω^2=τ^3/32) :
    τ*((j:ℝ)*τ)^5/1920≤freeQuartic ω (2*j+σ) ∧
    freeQuartic ω (2*j+σ)≤τ*((j:ℝ)*τ)^5/1920+τ^2*((j:ℝ)*τ+τ)^4/384 := by
  have F := fourth_power_bounds (2*j+σ)
  push_cast at F
  have l := pow_le_pow_left₀ (by positivity : (0:ℝ)≤2*j)
    (le_add_of_nonneg_right (Nat.cast_nonneg (α:=ℝ) σ)) 5
  have s1 : (σ:ℝ)≤1 := by exact_mod_cast hs
  have u := pow_le_pow_left₀ (by positivity : (0:ℝ)≤2*j+σ+1)
    (show 2*(j:ℝ)+σ+1≤2*j+2 by linarith only [s1]) 5
  have a : (32/5:ℝ)*(j:ℝ)^5≤fourthSum (2*j+σ) := by linarith only [F.1,l]
  have pos : 0≤(32/5:ℝ)*(j:ℝ)^5+32*((j:ℝ)+1)^4-(2*(j:ℝ)+2)^5/5 := by ring_nf; positivity
  have b : fourthSum (2*j+σ)≤(32/5:ℝ)*(j:ℝ)^5+32*((j:ℝ)+1)^4 := by linarith only [F.2,u,pos]
  have h4 : ω^4=(τ^3/32)^2 := by rw [← hω]; ring
  unfold freeQuartic; rw [h4]
  constructor
  · linarith only [mul_le_mul_of_nonneg_left a (sq_nonneg (τ^3/32))]
  · linarith only [mul_le_mul_of_nonneg_left b (sq_nonneg (τ^3/32))]

theorem free_log_scaled {ω τ : ℝ} {j σ : ℕ} (hs : σ≤1) (hτ : 0≤τ) (hω : ω^2=τ^3/32)
    (ha : |ω| *(2*j+σ)≤9/8) (v : ℝ) (hv : v=j*τ) :
    0≤ -freeLog ω (2*j+σ)-v^3/24-τ*freeLogCorrection σ v ∧
    -freeLog ω (2*j+σ)-v^3/24-τ*freeLogCorrection σ v≤τ^2*freeLogRemainder v τ := by
  have H := free_quartic_log ω (t:=2*j+σ) (by push_cast; exact ha)
  have Q := fourth_scaled (j:=j) hs hω
  have E := sixth_scaled (j:=j) (t:=2*j+σ) (by omega) hτ hω
  have v0 : 0≤v := hv ▸ mul_nonneg (Nat.cast_nonneg _) hτ
  have poly : freeExponent ω (2*j+σ)-v^3/24-τ*((2*σ+1:ℝ)*v^2/32)=
      τ^2*(if σ=0 then v/192 else 13*v/192+τ/64) := by
    interval_cases σ <;> simp [freeExponent,hω,hv] <;> ring
  have p : 0≤freeExponent ω (2*j+σ)-v^3/24-τ*((2*σ+1:ℝ)*v^2/32) := by
    rw [poly]; split <;> positivity
  have q : freeExponent ω (2*j+σ)-v^3/24-τ*((2*σ+1:ℝ)*v^2/32)≤τ^2*(13*v/192+τ/64) := by
    rw [poly]; split
    · apply mul_le_mul_of_nonneg_left _ (sq_nonneg _); linarith only [v0,hτ]
    · exact le_rfl
  rw [← hv] at Q E
  dsimp only [freeLogCorrection,freeLogRemainder]
  constructor <;> linarith only [H.1,H.2,Q.1,Q.2,E,p,q]

theorem bridge_log_scaled {ω τ : ℝ} {j : ℕ} (hτ : 0≤τ) (hω : ω^2=τ^3/32)
    (ha : |ω| *(2*j)≤9/8) (v : ℝ) (hv : v=j*τ) :
    0≤ -bridgeLog ω j-v^3/96-τ*bridgeLogCorrection v ∧
    -bridgeLog ω j-v^3/96-τ*bridgeLogCorrection v≤τ^2*bridgeLogRemainder v τ := by
  have H := bridge_quartic_log ω ha
  have E := sixth_scaled (j:=j) (t:=2*j) (by omega) hτ hω
  rw [← hv] at E
  have h4 : ω^4=(τ^3/32)^2 := by rw [← hω]; ring
  have main : bridgeExponent ω j+bridgeQuartic ω j=v^3/96+τ*bridgeLogCorrection v+
      τ^2*(7*v^4+2*τ*v^3)/(180*32^2) := by
    simp only [bridgeExponent,bridgeQuartic,fourthSum_closed,bridgeLogCorrection,hω,h4,hv,Nat.cast_mul,Nat.cast_ofNat]
    ring
  have nn : 0≤τ^2*(7*v^4+2*τ*v^3)/(180*32^2) := by rw [hv]; positivity
  dsimp only [bridgeLogRemainder]
  constructor <;> linarith only [H.1,H.2,main,E,nn]

end CentralUnimodality.ReturnSplit
