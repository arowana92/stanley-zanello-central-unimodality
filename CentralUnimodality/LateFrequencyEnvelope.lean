module

public import CentralUnimodality.LateRankBlocks
public import CentralUnimodality.TiltedOuterFrequencies
public import CentralUnimodality.TiltedInnerFrequency

/-! Piecewise characteristic-function bounds for the actual late-hit
rank law. Discarding the incomplete block costs a factor of two. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

private theorem abs_angle (l : ℕ) (θ : ℝ) :
    sin (l*|θ|/2)^2 = sin (l*θ/2)^2 := by
  rcases le_total 0 θ with h|h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h,show (l:ℝ)*(-θ)/2= -(l*θ/2) by ring,sin_neg,neg_sq]

private theorem rounded_blocks {ρ η : ℝ} {d L : ℕ} (hL : 0 < L) (hη : 0 ≤ η)
    (hl : 1/2 ≤ ρ) (hu : ρ ≤ exp (-η*L)) : ρ^(d/L) ≤ 2*exp (-η*d) := by
  let k := d/L
  have hk : d ≤ (k+1)*L := (Nat.lt_mul_div_succ d hL).le.trans_eq (Nat.mul_comm ..)
  have H := pow_le_pow_left₀ (by linarith : 0 ≤ ρ) hu (k+1)
  rw [← exp_nat_mul] at H
  have he : ((k+1:ℕ):ℝ)*(-η*L) ≤ -η*d := by
    have h : (d:ℝ) ≤ ((k+1:ℕ):ℝ)*L := by exact_mod_cast hk
    nlinarith only [mul_le_mul_of_nonneg_left h hη]
  have H' := H.trans (exp_le_exp.mpr he)
  rw [pow_succ] at H'
  have hpos : 0 ≤ ρ^k := pow_nonneg (by linarith) _
  change ρ^k ≤ _
  nlinarith only [mul_le_mul_of_nonneg_left hl hpos,H']

/-- A per-step contraction on full pairs extends to the entire span T-L. -/
theorem late_rank_decay {c z b U η : ℝ} (hc : 0 ≤ c) (hz : 0 ≤ z) (hb : 0 ≤ b)
    (hb' : b ≤ 6/25) (hU : 0 ≤ U) (hU' : U ≤ 6/25) (θ : ℝ)
    {m L T l : ℕ} (hL : 0 < L) (hLT : L ≤ T) (hT : T ≤ m) (hl : 0 < l)
    (hcap : (c+z)*m-b ≤ U) (hcut : b*m ≤ (tanh (c*m)/m+z)*prefixLabels m T)
    (hη : 0 ≤ η) (hρ : (1+exp (-(1/5)*l*sin (l*θ/2)^2))/2 ≤ exp (-η*(2*l:ℕ))) :
    rankChange c z (meanRank c m) m * ‖lateRankCharacter (c+z) θ m T‖ ≤
      exp (z^2*labelSquares m/2-m*b^2/2)*(2*U+(4/5)/√L)*(2*exp (-η*(T-L:ℕ))) := by
  let d := T-L
  let block := 2*l
  let p := L+d%block
  let k := d/block
  have hbpos : 0 < block := by dsimp [block]; omega
  have hsplit : T=p+k*block := by
    have H := Nat.mod_add_div d block
    rw [Nat.mul_comm block] at H
    dsimp [p,k,d] at *; omega
  have hpL : L ≤ p := Nat.le_add_right ..
  have H := late_rank_blocks hc hz hb hb' hU hU' θ (hL.trans_le hpL) (by omega) hT hsplit hcap hcut
  apply H.trans
  have hpre : (4/5)/√(p:ℝ) ≤ (4/5)/√(L:ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (sqrt_pos.mpr (by exact_mod_cast hL))
      (Real.sqrt_le_sqrt (by exact_mod_cast hpL))
  have hr := rounded_blocks (d := d) hbpos hη (by linarith only [exp_pos (-(1/5)*(l:ℝ)*sin (l*θ/2)^2)]) hρ
  exact mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add (le_refl (2*U)) hpre) (exp_pos _).le) hr
    (by positivity) (by positivity)

noncomputable def innerPairRate (t : ℝ) := (14/25)/(17/2)*t^(2/3:ℝ)

/-- Small and outer arcs, with both endpoints of every outer arc covered.
The parameter restrictions are precisely those needed by the rank and height
change and the narrow probability rectangle. -/
theorem late_rank_arcs {c z b U : ℝ} (hc : 0 ≤ c) (hz : 0 ≤ z) (hb : 0 ≤ b)
    (hb' : b ≤ 6/25) (hU : 0 ≤ U) (hU' : U ≤ 6/25) (θ : ℝ)
    {m L T : ℕ} (hL : 0 < L) (hLT : L ≤ T) (hT : T ≤ m)
    (hcap : (c+z)*m-b ≤ U) (hcut : b*m ≤ (tanh (c*m)/m+z)*prefixLabels m T) :
    let H := rankChange c z (meanRank c m) m * ‖lateRankCharacter (c+z) θ m T‖
    let N := exp (z^2*labelSquares m/2-m*b^2/2)*(2*U+(4/5)/√L)
    (|θ| ≤ 1/8 → H ≤ N*(2*exp (-(innerPairRate |θ|)*(T-L:ℕ)))) ∧
    (∀ s : Fin 4, outerLo s ≤ |θ| → |θ| ≤ outerHi s →
      H ≤ N*(2*exp (-(pairRate s false:ℝ)*(T-L:ℕ)))) := by
  constructor
  · intro ht'
    by_cases hzero : θ=0
    · subst θ
      simp only [abs_zero,innerPairRate,zero_rpow (by norm_num : (2/3:ℝ) ≠ 0),mul_zero]
      apply late_rank_decay (l:=1) hc hz hb hb' hU hU' 0 hL hLT hT (by decide) hcap hcut le_rfl
      norm_num
    have ht := abs_pos.mpr hzero
    obtain ⟨hl,hscale,_⟩ := inner_spacing_energy ht ht'
    have H := inner_pair_contraction ht ht' false
    norm_num [pairWeight] at H
    rw [abs_angle] at H
    apply late_rank_decay hc hz hb hb' hU hU' θ hL hLT hT hl hcap hcut (by unfold innerPairRate; positivity)
    simp only [neg_mul] at H ⊢
    apply H.trans (exp_le_exp.mpr _)
    unfold innerPairRate
    push_cast
    nlinarith only [hscale]
  · intro s hlo hhi
    obtain ⟨hl,hmax,hsin⟩ := outer_spacing_data s hlo hhi
    have hη : 0 ≤ (pairRate s false:ℝ) := by fin_cases s <;> norm_num [pairRate,pairArc]
    apply late_rank_decay hc hz hb hb' hU hU' θ hL hLT hT hl hcap hcut hη
    have H := tilted_pair_rate s false hmax hsin
    rw [abs_angle] at H
    dsimp [pairWeight] at H
    push_cast at H ⊢
    convert H using 2; ring

end CentralUnimodality.MarkedExcursion
