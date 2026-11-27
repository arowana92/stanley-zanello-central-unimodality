module

public import CentralUnimodality.HitTiltCost
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Uniform exponents for time and saddle-parameter bins. The scale s
satisfies s²=m³ and the dimensionless parameters are γ=2cs and Δ=2zs. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

private theorem scaled_energy {m s : ℝ} (hm : 0 < m) (hs : s^2=m^3) (c : ℝ) :
    (2*c*s)^2/(6*m) = 2*(c*m)^2/3 := by
  rw [mul_pow,hs]
  field_simp
  ring

private theorem scaled_cost {m : ℕ} {s : ℝ} (hm : 0 < (m:ℝ)) (hs : s^2=(m:ℝ)^3) (z : ℝ) :
    (2*z*s)^2*(labelSquares m/(m:ℝ)^3)/8 = z^2*labelSquares m/2 := by
  rw [mul_pow,hs]
  field_simp
  ring

/-- Equation (6), uniformly across a time bin with endpoints v and e. -/
theorem first_hit_bin {m d : ℕ} (ht : 2*d+1 ≤ m) {c z s γ Δ v e : ℝ}
    (hc : 0 ≤ c) (hz : 0 ≤ z) (hs : s^2=(m:ℝ)^3) (hγ : γ=2*c*s) (hΔ : Δ=2*z*s)
    (hsmall : γ^2 ≤ 6*m) (he : e ≤ 2)
    (hlo : v*m ≤ 2*(d:ℝ)+1) (hhi : 2*(d:ℝ)+1 ≤ e*m) :
    rankChange c z (meanRank c m) m *
      (∑ w ∈ (words m).filter (fun w => w.take (2*d+1) ∈ hitWords 1 (2*d+1)),
        signMass (c+z) ((c+z)*m) w) ≤
      exp (Δ^2*(labelSquares m/(m:ℝ)^3)/8 -
        v*(1-e/2)^2*(γ+Δ)*(γ*(1-γ^2/(6*m))+Δ)/8) *
        ∑ w ∈ hitWords 1 (2*d+1), signMass (c+z) ((c+z)*d) w := by
  have hm : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hfactor : 0 ≤ 1-γ^2/(6*m) := sub_nonneg.mpr ((div_le_one (by positivity)).mpr hsmall)
  let F := (c+z)*(c*(1-γ^2/(6*m))+z)
  have hF : 0 ≤ F := mul_nonneg (add_nonneg hc hz) (add_nonneg (mul_nonneg hc hfactor) hz)
  have hwidth : (m:ℝ)*(1-e/2) ≤ m-d := by linarith
  have hsq := (sq_le_sq₀ (mul_nonneg hm.le (by linarith : 0 ≤ 1-e/2))
    ((mul_nonneg hm.le (by linarith : 0 ≤ 1-e/2)).trans hwidth)).mpr hwidth
  have hprod := mul_le_mul hlo hsq (sq_nonneg _) (by positivity : (0:ℝ) ≤ 2*d+1)
  have hscale : v*(1-e/2)^2*(γ+Δ)*(γ*(1-γ^2/(6*m))+Δ)/8 = v*(1-e/2)^2*s^2*F/2 := by
    dsimp [F]; rw [hγ,hΔ]; ring
  have hform : F = (c+z)*(c*(1-2*(c*m)^2/3)+z) := by
    dsimp [F]; rw [hγ,scaled_energy hm hs]
  apply (first_hit_change_bound ht hc hz).trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => (signMass_pos ..).le)
  apply exp_le_exp.mpr
  rw [hscale,hΔ,scaled_cost hm hs,hs]
  have bound := mul_le_mul_of_nonneg_right hprod hF
  rw [hform] at bound ⊢
  linarith only [bound]

/-- Equation (7) in the verifier's variables. The lower endpoint g of a
parameter bin can be used throughout it; the cut need only be at least hm. -/
theorem late_bin_parameters {m t : ℕ} (hM : 4096 ≤ m) (ht : t ≤ m) {c z g h : ℝ}
    (hc : 0 ≤ c) (hz : 0 ≤ z) (hg : 0 ≤ g) (hg' : g ≤ 2*c*((m:ℝ)*√m))
    (hsmall : g^2 ≤ 12*4096) (hh : 0 ≤ h) (hh' : h ≤ 1) (hcut : h*m ≤ t) :
    let s := (m:ℝ)*√m
    let Δ := 2*z*s
    let a := (g/2*(1-g^2/(12*4096))+Δ/2)*(h*(1-h/2))
    let b := a/√m
    0 ≤ b ∧ b*m ≤ (tanh (c*m)/m+z)*prefixLabels m t ∧
      z^2*labelSquares m/2-m*b^2/2 = Δ^2*(labelSquares m/(m:ℝ)^3)/8-a^2/2 := by
  dsimp only
  let M := (m:ℝ)
  let r := √M
  let s := M*r
  have hm : (4096:ℝ) ≤ M := by dsimp [M]; exact_mod_cast hM
  have hm' : 0 < M := by linarith
  have hr : 0 < r := Real.sqrt_pos.mpr hm'
  have hr2 : r^2=M := Real.sq_sqrt hm'.le
  have hs : s^2=M^3 := by dsimp [s]; rw [mul_pow,hr2]; ring
  let u := g/(2*r)
  have hu : 0 ≤ u := div_nonneg hg (by positivity)
  have hug : u ≤ c*M := by
    apply (div_le_iff₀ (by positivity)).mpr
    dsimp [M,r] at *; linarith only [hg']
  have hmono : tanh u ≤ tanh (c*M) := by
    rw [tanh_eq_sinh_div_cosh,tanh_eq_sinh_div_cosh,div_le_div_iff₀ (cosh_pos _) (cosh_pos _)]
    have hsub := sinh_nonneg_iff.mpr (sub_nonneg.mpr hug)
    rw [sinh_sub] at hsub
    linarith only [hsub]
  have hcubic := (tanh_cubic_lower hu).trans hmono
  have hid : r*(u-u^3/3) = g/2-g^3/(24*M) := by
    dsimp [u]; rw [← hr2]; field_simp; ring
  have hinv : g^3/(24*M) ≤ g^3/(24*4096) := by
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
    linarith
  have hdrift : g/2*(1-g^2/(12*4096)) ≤ r*tanh (c*M) := by
    have hc' := mul_le_mul_of_nonneg_left hcubic hr.le
    rw [hid] at hc'
    linarith only [hc',hinv]
  let K := g/2*(1-g^2/(12*4096)) + (2*z*s)/2
  let H := h*(1-h/2)
  let a := K*H
  have hK : 0 ≤ K := by
    apply add_nonneg (mul_nonneg (by positivity) (by linarith only [hsmall]))
    dsimp [s]; positivity
  have hH : 0 ≤ H := mul_nonneg hh (by linarith)
  have hT : (t:ℝ) ≤ M := by dsimp [M]; exact_mod_cast ht
  have hpoly := mul_nonneg (sub_nonneg.mpr hcut) (show 0 ≤ M-((t:ℝ)+h*M)/2 by
    nlinarith only [hT,mul_le_mul_of_nonneg_right hh' hm'.le])
  have hlabels : M^2*H ≤ prefixLabels m t := by
    unfold prefixLabels; dsimp only [M,H] at *; nlinarith only [hpoly,Nat.cast_nonneg (α := ℝ) t]
  have hK' : K ≤ s*(tanh (c*M)/M+z) := by
    have split : s*(tanh (c*M)/M+z) = r*tanh (c*M)+z*s := by
      dsimp only [s]; field_simp
    rw [split]; dsimp only [K]; linarith only [hdrift]
  have htop := mul_nonneg (show 0 ≤ s by dsimp [s]; positivity) (show 0 ≤ tanh (c*M)/M+z by
    apply add_nonneg _ hz
    rw [tanh_eq_sinh_div_cosh]
    exact div_nonneg (div_nonneg (sinh_nonneg_iff.mpr (mul_nonneg hc hm'.le)) (cosh_pos _).le) hm'.le)
  have hboth := mul_le_mul hK' hlabels (mul_nonneg (sq_nonneg M) hH) htop
  have hb : 0 ≤ a/r := div_nonneg (mul_nonneg hK hH) hr.le
  have hcond : a/r*M ≤ (tanh (c*M)/M+z)*prefixLabels m t := by
    let y := tanh (c*M)/M+z
    change K ≤ s*y at hK'
    change K*(M^2*H) ≤ (s*y)*prefixLabels m t at hboth
    change a/r*M ≤ y*_
    rw [div_mul_eq_mul_div,div_le_iff₀ hr]
    apply le_of_mul_le_mul_left _ hm'
    dsimp only [a,s] at hboth ⊢
    linarith only [hboth]
  refine ⟨hb,hcond,?_⟩
  change _ = (2*z*s)^2*(labelSquares m/M^3)/8-a^2/2
  rw [scaled_cost hm' hs]
  congr 1
  change M*(a/r)^2/2 = a^2/2
  rw [div_pow,hr2]; field_simp

theorem late_hit_bin {m t : ℕ} (hM : 4096 ≤ m) (ht : t ≤ m) {c z g h : ℝ}
    (hc : 0 ≤ c) (hz : 0 ≤ z) (hg : 0 ≤ g) (hg' : g ≤ 2*c*((m:ℝ)*√m))
    (hsmall : g^2 ≤ 12*4096) (hh : 0 ≤ h) (hh' : h ≤ 1) (hcut : h*m ≤ t) :
    let s := (m:ℝ)*√m
    let Δ := 2*z*s
    let a := (g/2*(1-g^2/(12*4096))+Δ/2)*(h*(1-h/2))
    rankChange c z (meanRank c m) m * lateHitMass (c+z) m t ≤
      exp (Δ^2*(labelSquares m/(m:ℝ)^3)/8-a^2/2) := by
  obtain ⟨hb,hcond,he⟩ := late_bin_parameters hM ht hc hz hg hg' hsmall hh hh' hcut
  apply (late_hit_change_bound (by omega : 0 < m) ht hc hz hb hcond).trans_eq
  rw [he]

end CentralUnimodality.MarkedExcursion
