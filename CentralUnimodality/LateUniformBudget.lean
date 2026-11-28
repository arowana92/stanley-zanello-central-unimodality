module

public import CentralUnimodality.LateUniformOuter
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Real.Pi.Bounds

/-! Size-independent numerical bounds on the three scaled late Fourier
integrals. The same bounds cover both prefix cuts. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

private theorem gamma_caps :
    Gamma (3/2) ≤ 9/10 ∧ Gamma 3 ≤ 2 ∧ Gamma (9/2) ≤ 12 := by
  have hπ : √π ≤ 9/5 := (sqrt_le_left (by norm_num)).mpr (by linarith only [pi_lt_d2])
  have h₁ := Gamma_nat_add_half 1
  have h₄ := Gamma_nat_add_half 4
  norm_num [Nat.factorial] at h₁ h₄
  exact ⟨by linarith only [h₁,hπ],by norm_num,by linarith only [h₄,hπ]⟩

private theorem normalized_inner {M d σ : ℝ} (hp : 0<M) (hd : (837/1000)*M ≤ d)
    (hσ : 0 ≤ σ) (hσ' : σ ≤ (259/1000)*(M*√M)) (r : ℕ) :
    σ^(r+1)*((14/25)/(17/2)*d)^(-3*((r:ℝ)+1)/2) ≤ (201/10)^(r+1) := by
  let b := (14/25)/(17/2)*d
  have hb : 0<b := by dsimp [b]; linarith only [hd,hp]
  have hl : (2347/10000)*√M ≤ √b := by
    apply (le_sqrt (by positivity) hb.le).mpr
    rw [mul_pow,sq_sqrt hp.le]
    dsimp [b]; linarith only [hd,hp]
  have H := pow_le_pow_left₀ (by positivity : 0 ≤ (2347/10000)*√M) hl 3
  have hs3 : (√M)^3=M*√M := by rw [pow_succ,sq_sqrt hp.le]
  rw [mul_pow,hs3] at H
  have hr : σ/(√b)^3 ≤ 201/10 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [hσ',H,mul_nonneg hp.le (sqrt_nonneg M)]
  have HH := pow_le_pow_left₀ (div_nonneg hσ (by positivity : 0 ≤ (√b)^3)) hr (r+1)
  have he : ((√b)^3)^(r+1)=b^(3*((r:ℝ)+1)/2) := by
    rw [sqrt_eq_rpow,← rpow_natCast _ 3,← rpow_mul hb.le,← rpow_natCast _ (r+1),← rpow_mul hb.le]
    push_cast; congr 1; ring
  rw [div_pow,he] at HH
  change σ^(r+1)*b^(-3*((r:ℝ)+1)/2) ≤ _
  rw [show -3*((r:ℝ)+1)/2= -(3*((r:ℝ)+1)/2) by ring,rpow_neg hb.le,← div_eq_mul_inv]
  exact HH

noncomputable def lateUniformLimit (r : Fin 3) : ℝ :=
  if r=0 then 19 else if r=1 then 810 else 98000

/-- Uniform in all lengths M≥4096, for the two-thirds-power arc and
the four outer intervals together. -/
theorem late_uniform_budget {M d σ : ℝ} (hM : 4096 ≤ M) (hd : (837/1000)*M ≤ d)
    (hσ : 0 ≤ σ) (hσ' : σ ≤ (259/1000)*(M*√M)) (r : Fin 3) :
    σ^(r.val+1)*lateFourierBudget d r.val ≤ lateUniformLimit r := by
  have H := normalized_inner (by linarith : 0<M) hd hσ hσ' r.val
  let G := Gamma (3*((r.val:ℝ)+1)/2)
  have hG : 0 ≤ G := (Gamma_pos_of_pos (by positivity)).le
  let term (s : Fin 4) := exp (-(pairRate s false:ℝ)*d)*
    (2*((outerHi s)^(r.val+1)-(outerLo s)^(r.val+1))/((r.val:ℝ)+1))
  have hsum : σ^(r.val+1)*(∑ s : Fin 4, term s) ≤ 1/2 := by
    rw [Finset.mul_sum]
    apply (Finset.sum_le_sum (fun s _ => late_scaled_outer s r hM hd hσ hσ')).trans
    norm_num
  unfold lateFourierBudget
  rw [← mul_div_assoc,mul_add,div_le_iff₀ pi_pos]
  have hi := mul_le_mul_of_nonneg_right H hG
  have Htot : σ^(r.val+1)*(3*((14/25)/(17/2)*d)^(-3*((r.val:ℝ)+1)/2)*G)+
      σ^(r.val+1)*(∑ s : Fin 4, term s) ≤ 3*(201/10)^(r.val+1)*G+1/2 := by
    linarith only [hi,hsum]
  apply Htot.trans
  obtain ⟨H₀,H₁,H₂⟩ := gamma_caps
  fin_cases r <;> norm_num [lateUniformLimit,G] at * <;> linarith only [H₀,H₁,H₂,pi_gt_three]

end CentralUnimodality.MarkedExcursion
