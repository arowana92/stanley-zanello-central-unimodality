module

public import CentralUnimodality.OuterPrefixSurvival
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! The height above the absorbing level has constant fair expectation
when set to zero on a hit. Its conditional mean gives a lower bound for
the surviving term in the change between opposite homogeneous drifts. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

theorem surviving_height_sum (t : ℕ) :
    ∑ w ∈ ballots t, (1+(displacement w:ℝ)) = 2^t := by
  induction t with
  | zero =>
    have hz : ballots 0 = {[]} := by ext w; simp +contextual [ballots,words,BallotFrom]
    simp [hz,displacement]
  | succ t ih =>
    have H := split_live_hit t (fun w => 1+(displacement w:ℝ))
    have hz : ∑ w ∈ hitWords 1 (t+1), (1+(displacement w:ℝ))=0 := by
      apply Finset.sum_eq_zero
      intro w hw
      exact_mod_cast ((Finset.mem_filter.mp hw).2 : FirstHitPath 1 w).2.1
    rw [hz,add_zero] at H
    rw [H,pow_succ,← ih,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w _
    simp only [displacement_snoc,step,Int.cast_add,Int.cast_one,Int.cast_neg]
    ring

private theorem homogeneous_density (u : ℝ) (t : ℕ) :
    live 0 u t 1*((2:ℝ)^t*(cosh u)^t)=∑ w ∈ ballots t, exp (u*(displacement w:ℝ)) := by
  rw [live_ballots,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w hw
  simpa only [coshProduct,zero_mul,sub_zero,Finset.prod_const,Finset.card_range,
    (mem_ballots.mp hw).1,add_zero] using signMass_density 0 u w

/-- Jensen's tangent-line bound for the negative-drift survival.
P is the exact survival of the fair walk and (1/P)-1 is its conditional
mean displacement. -/
theorem negative_live_lower (u : ℝ) (t : ℕ) :
    let P := live 0 0 t 1
    P*exp (u-u/P-t*u^2/2) ≤ live 0 (-u) t 1 := by
  let P := live 0 0 t 1
  let C : ℝ := (ballots t).card
  let V : ℝ := 2^t
  let y := u-u/P
  have hP : 0<P := by dsimp [P]; rw [fair_live_exact]; exact survival_pos _
  have hV : 0<V := by dsimp [V]; positivity
  have hC : P*V=C := by simpa [P,V,C] using homogeneous_density 0 t
  have hD : ∑ w ∈ ballots t, (displacement w:ℝ)=V-C := by
    have H := surviving_height_sum t
    rw [Finset.sum_add_distrib] at H
    simpa [V,C] using (show _ = (2:ℝ)^t-∑ _w ∈ ballots t,(1:ℝ) by linarith only [H])
  have htan (x : ℝ) : exp y*(1+x-y)≤exp x := by
    have H := mul_le_mul_of_nonneg_left (add_one_le_exp (x-y)) (exp_pos y).le
    rw [← exp_add,show y+(x-y)=x by ring] at H
    linarith only [H]
  have Hsum := Finset.sum_le_sum (s:=ballots t) (fun w _ => htan (-u*(displacement w:ℝ)))
  rw [← Finset.mul_sum,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,hD] at Hsum
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at Hsum
  change exp y*(C+-u*(V-C)-C*y) ≤ _ at Hsum
  have hnorm : C+-u*(V-C)-C*y=C := by rw [← hC]; dsimp [y]; field_simp [hP.ne']; ring
  rw [hnorm,← homogeneous_density,cosh_neg] at Hsum
  have hpart : P*exp y≤live 0 (-u) t 1*(cosh u)^t := by
    apply le_of_mul_le_mul_right (a:=V) _ hV
    rw [← hC] at Hsum
    dsimp only [V] at Hsum ⊢
    linarith only [Hsum]
  have hcosh := pow_le_pow_left₀ (cosh_pos u).le (cosh_le_exp_half_sq u) t
  rw [← exp_nat_mul] at hcosh
  have H := hpart.trans (mul_le_mul_of_nonneg_left hcosh (live_nonneg ..))
  apply le_of_mul_le_mul_right (a:=exp ((t:ℝ)*(u^2/2))) _ (exp_pos _)
  apply le_trans _ H
  change P*exp (y-t*u^2/2)*exp ((t:ℝ)*(u^2/2))≤P*exp y
  rw [mul_assoc,← exp_add,show y-t*u^2/2+t*(u^2/2)=y by ring]

/-- Lower bound for the inhomogeneous prefix when each natural parameter
is at least u. The second summand retains its finite-time survival. -/
theorem prefix_survival_lower (c v u : ℝ) (t : ℕ) (hu : ∀ i<t, u≤v-c*i) :
    let P := live 0 0 t 1
    1-exp (-2*u)+P*exp (-u-u/P-t*u^2/2) ≤ live c v t 1 := by
  let P := live 0 0 t 1
  have H := mul_le_mul_of_nonneg_left (negative_live_lower u t) (exp_pos (-2*u)).le
  change exp (-2*u)*(P*exp (u-u/P-t*u^2/2)) ≤ _ at H
  rw [mul_left_comm,← exp_add,show -2*u+(u-u/P-t*u^2/2)= -u-u/P-t*u^2/2 by ring] at H
  apply le_trans _ (live_parameters 0 u c v t 1 (by simpa using hu))
  change 1-exp (-2*u)+P*exp (-u-u/P-t*u^2/2) ≤ live 0 u t 1
  rw [homogeneous_live u t 1,pow_one]
  linarith only [H]

end CentralUnimodality.MarkedExcursion
