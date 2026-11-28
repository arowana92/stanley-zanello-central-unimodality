module

public import CentralUnimodality.SpatialOuterTail

/-! Omitted frequencies for the polynomial trial ending at 12³.
The derivative order is retained in the tail integral. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

open Set Real intervalIntegral Witness

private noncomputable def majorant (r : ℕ) (ξ : ℝ) := 100*ξ^r*exp (-(0.157*ξ^(2/3:ℝ)))

private theorem majorant_integral {r : ℕ} (hr : r≤2) {b : ℝ} (hb : 1728≤b) :
    (∫ ξ in (1728:ℝ)..b, majorant r ξ)≤1200*12^(3*r+1)*exp (-(0.157*144)) := by
  let B := b^(1/3:ℝ)
  have bn : 0≤b := by linarith only [hb]
  have b3 : B^3=b := by dsimp [B]; rw [← rpow_natCast _ 3,← rpow_mul bn]; norm_num
  have ge : 12≤B := by
    apply le_of_pow_le_pow_left₀ (n:=3) (by decide) (rpow_nonneg bn _)
    rw [b3]; norm_num; exact hb
  let f := fun t : ℝ => t^3
  have cont : Continuous (majorant r) := by
    have := continuous_rpow_const (by norm_num : (0:ℝ)≤2/3)
    unfold majorant; fun_prop
  have df (t : ℝ) : HasDerivAt f (3*t^2) t := by simpa [f] using hasDerivAt_pow 3 t
  have sub := integral_comp_mul_deriv (a:=12) (b:=B) (g:=majorant r) (fun t _ => df t)
    (by apply Continuous.continuousOn; fun_prop) cont
  change (∫ t in (12:ℝ)..B, (majorant r ∘ f) t*(3*t^2))=∫ ξ in (12:ℝ)^3..B^3, majorant r ξ at sub
  rw [b3,show (12:ℝ)^3=1728 by norm_num] at sub
  rw [← sub]
  let k := 3*r
  let G := fun t : ℝ => -1200*t^(k+1)*exp (-(0.157*t^2))
  let d := fun t : ℝ => 1200*(2*0.157*t^2-((k:ℝ)+1))*t^k*exp (-(0.157*t^2))
  have der (t : ℝ) : HasDerivAt G (d t) t := by
    have E := (((hasDerivAt_pow 2 t).const_mul (-0.157:ℝ)).exp)
    convert (((hasDerivAt_pow (k+1) t).const_mul (-1200:ℝ)).mul E) using 1
    · funext s; dsimp [G]; simp only [neg_mul]
    · dsimp [d]; simp only [Nat.cast_succ,neg_mul,pow_succ]; ring
  have prim := integral_eq_sub_of_hasDerivAt (a:=12) (b:=B) (fun t _ => der t)
    (by apply Continuous.intervalIntegrable; dsimp [d]; fun_prop)
  apply (integral_mono_on ge _ _ (g:=d) ?_).trans
  · rw [prim]
    have neg : G B≤0 := by dsimp [G]; apply mul_nonpos_of_nonpos_of_nonneg _ (exp_pos _).le
                           exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (pow_nonneg (by linarith only [ge]) _)
    have left : -G 12=1200*(12:ℝ)^(3*r+1)*exp (-(0.157*144)) := by dsimp [G,k]; norm_num
    linarith only [neg,left]
  · apply Continuous.intervalIntegrable
    exact (cont.comp (continuous_id.pow 3)).mul (continuous_const.mul (continuous_id.pow 2))
  · apply Continuous.intervalIntegrable; dsimp [d]; fun_prop
  · intro t ht
    have nn : 0≤t := by linarith only [ht.1]
    have cube : (t^3)^(2/3:ℝ)=t^2 := by rw [← rpow_natCast _ 3,← rpow_mul nn]; norm_num
    have t2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤12) ht.1 2
    have rk : (k:ℝ)≤6 := by exact_mod_cast (show k≤6 by dsimp [k]; omega)
    have gain : 300*t^2≤1200*(2*0.157*t^2-((k:ℝ)+1)) := by linarith only [t2,rk]
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right gain (pow_nonneg nn k)) (exp_pos (-(0.157*t^2))).le
    dsimp [Function.comp_apply,majorant,f,d]; rw [cube,← pow_mul]; dsimp only [k] at h ⊢
    linarith only [h]

theorem moderate_inner_tail {n δ r : ℕ} (hs : δ≤1) (hn : 2049≤n+δ) (hr : r≤2) (x : ℝ)
    {b : ℝ} (hb : 1728≤b) (hS : b≤0.008*cellScale (n+δ)) :
    |∫ ξ in (1728:ℝ)..b, rankKernel n δ r x ξ|≤1200*12^(3*r+1)*exp (-(0.157*144)) := by
  have cm : Continuous (majorant r) := by
    have := continuous_rpow_const (by norm_num : (0:ℝ)≤2/3)
    unfold majorant; fun_prop
  apply (integral_abs_of_envelope hb (rankKernel_continuous _ _ _ hs x) cm ?_).trans (majorant_integral hr hb)
  intro ξ hξ
  have nn : 0≤ξ := by linarith only [hξ.1]
  have a := (amplitude_le_magnitude n δ _).trans (scaled_inner_magnitude hs hn (by linarith only [hξ.1]) (hξ.2.trans hS))
  rw [rankKernel,abs_mul,abs_mul,abs_pow,abs_of_nonneg nn]
  apply (mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (pow_nonneg nn r)) (abs_cos_le_one _)).trans
  exact (mul_le_mul_of_nonneg_right a (pow_nonneg nn r)).trans_eq (by unfold majorant; ring)

end CentralUnimodality.PolynomialTrial
