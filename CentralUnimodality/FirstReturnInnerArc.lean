module

public import CentralUnimodality.FirstReturnFourier
import Mathlib.Analysis.Complex.ExponentialBounds

/-! An explicit bound on the conditional first-return characteristic
function throughout the small lattice arc. The terminal first-hit point
bound allows a single pinned segment of length floor(d/4). -/
@[expose] public section

namespace CentralUnimodality
open Real

private theorem prefix_ratio {d p : ℕ} (hd : 40≤d) (hp : d/8≤p) :
    survival ((p+1)/2) ≤ 5*survival d := by
  let K := (p+1)/2
  have sizes : 4*d≤25*(3*K+1) := by dsimp [K]; omega
  have sizes' : 4*(d:ℝ)≤25*(3*(K:ℝ)+1) := by exact_mod_cast sizes
  have low := survival_sq_lower (by omega : 1≤d)
  have high := survival_sq_three K
  have w := mul_le_mul_of_nonneg_right sizes' (sq_nonneg (survival d))
  apply (sq_le_sq₀ (survival_pos K).le (mul_nonneg (by norm_num) (survival_pos d).le)).mp
  apply le_of_mul_le_mul_left (a:=3*(K:ℝ)+1) _ (by positivity)
  nlinarith only [w,low,high]

private theorem exp_rounding_cap : exp (7/4) ≤ 25/4 := by
  have a : exp 1 ≤ 11/4 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have b : 5/4 ≤ exp (1/4) := by linarith only [Real.add_one_le_exp (1/4)]
  have prod : exp (7/4)*exp (1/4)=(exp 1)^2 := by
    rw [← Real.exp_add,← Real.exp_nat_mul]; norm_num
  linarith only [prod,mul_le_mul_of_nonneg_left b (exp_pos (7/4)).le,
    pow_le_pow_left₀ (exp_pos 1).le a 2]

/-- For j≥41 and θ=z³≤0.001, the signed first-return transform, divided by
its fair mass, is bounded by 125 exp(−0.30 j z²). At the staircase scaling
u=2N z² the exponent is −0.15 u j/N. -/
theorem returnSymbol_inner_001 {z : ℝ} (hz : 0<z) (hZ : z≤0.1) {j : ℕ} (hj : 41≤j) :
    ‖returnSymbol (z^3/2) j‖ ≤ returnMass j*(125*exp (-(0.30*(j:ℝ)*z^2))) := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
  let L := innerLength z
  let b := d/8
  let t := d/4
  let m := 2*d-b-t
  let k := m/L
  let p := b+m%L
  have steps := innerLength_bounds hz
  have hL : 0<L := by
    by_contra! he
    have zero : innerLength z=0 := Nat.le_zero.mp he
    rw [zero,Nat.cast_zero,mul_zero] at steps
    norm_num at steps
  have ht : b+t≤2*d := by dsimp [b,t]; omega
  have split : p+k*L+t=2*d := by
    have e := Nat.mod_add_div m L
    rw [Nat.mul_comm L] at e
    dsimp only [p,k,m] at e ⊢
    omega
  have middle : 13*d≤8*(k*L+L) := by
    have r := Nat.mod_lt m hL
    have e := Nat.mod_add_div m L
    rw [Nat.mul_comm L] at e
    dsimp only [p,k,m,b,t] at *; omega
  have mid : 13*(d:ℝ)≤8*((k:ℝ)*L+L) := by exact_mod_cast middle
  have dr : (40:ℝ)≤d := by exact_mod_cast (by omega : 40≤d)
  have loss : 0.1895*z^2*(L:ℝ)≤7/4 := by
    have z2 := pow_le_pow_left₀ hz.le hZ 2
    have upper : z^2*(L:ℝ)≤9+z^2 := steps.2
    nlinarith only [upper,z2]
  let q := exp (-(0.1895*z^2)*L)
  have decay : q^k ≤ (25/4)*exp (-(0.30*((d:ℝ)+1)*z^2)) := by
    dsimp only [q]
    rw [← Real.exp_nat_mul]
    have md : 0.30*((d:ℝ)+1) ≤ 0.1895*((k:ℝ)*L+L) := by linarith only [mid,dr]
    calc
      _ ≤ exp (7/4 + -(0.30*((d:ℝ)+1)*z^2)) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [mul_le_mul_of_nonneg_right md (sq_nonneg z),loss]
      _ ≤ _ := by rw [Real.exp_add]; exact mul_le_mul_of_nonneg_right exp_rounding_cap (exp_pos _).le
  have pref := prefix_ratio (d:=d) (p:=p) (by omega) (Nat.le_add_right b _)
  have atBridge := killed_bridge_blocks (killed_inner_001 hz hZ) (exp_pos _).le p k t
  change ‖killedAt (z^3/2) 1 (p+k*L+t) 1‖/(2:ℝ)^(p+k*L+t) ≤
    survival ((p+1)/2)*q^k/((t:ℝ)+1) at atBridge
  rw [split] at atBridge
  have arc := (returnSymbol_bridge (z^3/2) d).trans (div_le_div_of_nonneg_right atBridge (by norm_num))
  have prod := mul_le_mul pref decay (pow_nonneg (exp_pos _).le _) (mul_nonneg (by norm_num) (survival_pos d).le)
  have terminal : (d:ℝ)+1≤4*((t:ℝ)+1) := by
    exact_mod_cast (by dsimp [t]; omega : d+1≤4*(t+1))
  have mass : returnMass (d+1)=survival d/(2*((d:ℝ)+1)) := by
    rw [returnMass_succ,survival_succ]; field_simp; ring
  apply arc.trans
  rw [mass,Nat.cast_succ]
  apply (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right prod (by positivity)) (by norm_num)).trans
  have bound := mul_le_mul_of_nonneg_right terminal (survival_pos d).le
  field_simp
  nlinarith only [bound]

end CentralUnimodality
