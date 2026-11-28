module

public import CentralUnimodality.LateRankMoments

/-! A fixed upper bound on each of the four scaled outer-arc integrals.
It holds uniformly from length 4096, including the polynomial multiplier
for the second difference. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

private theorem normalized_decay {M : ℝ} (hM : 4096 ≤ M) :
    (M/4096)^6*exp (-M/100) ≤ exp (-(4096:ℝ)/100) := by
  have H := short_exp_decay (B:=M*255/4096) (a:=(4096:ℝ)/255/100) (by linarith) 6 (by norm_num)
  rw [show -((4096:ℝ)/255/100)*(M*255/4096)= -M/100 by ring,
    show -((4096:ℝ)/255/100)*255= -(4096:ℝ)/100 by ring] at H
  linarith only [H]

private theorem outer_number : 2*(4*(259/1000)*4096*64)^3*exp (-(4096:ℝ)/100) ≤ 1/8 := by
  have H := pow_le_pow_left₀ (exp_pos _).le (upperNegExp_sound (by decide +kernel : (0:ℚ)≤128/25)) 8
  rw [← exp_nat_mul] at H
  norm_num only [Nat.cast_ofNat,Rat.cast_div,Rat.cast_ofNat] at H
  rw [show -(1024/25:ℝ)= -(4096:ℝ)/100 by norm_num] at H
  have he : 2*(4*(259/1000)*4096*64)^3*(upperNegExp (128/25))^8 ≤ (1/8:ℚ) := by decide +kernel
  have hreal := (Rat.cast_le (K:=ℝ)).mpr he
  push_cast at hreal
  exact (mul_le_mul_of_nonneg_left H (by norm_num)).trans hreal

theorem late_scaled_outer (s : Fin 4) (r : Fin 3) {M d σ : ℝ} (hM : 4096 ≤ M)
    (hd : (837/1000)*M ≤ d) (hσ : 0 ≤ σ) (hσ' : σ ≤ (259/1000)*(M*√M)) :
    σ^(r.val+1)*(exp (-(pairRate s false:ℝ)*d)*
      (2*((outerHi s)^(r.val+1)-(outerLo s)^(r.val+1))/((r.val:ℝ)+1))) ≤ 1/8 := by
  have hrate : 13/1000 ≤ (pairRate s false:ℝ) := by fin_cases s <;> norm_num [pairRate,pairArc]
  have hp : 0<M := by linarith
  have hr : 64 ≤ √M := (le_sqrt (by norm_num) hp.le).mpr (by linarith)
  have hdpos : 0≤d := by linarith
  have Hexp : exp (-(pairRate s false:ℝ)*d) ≤ exp (-M/100) := by
    apply exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_right hrate hdpos,hd,hM]
  have hlo : 0≤outerLo s := by fin_cases s <;> norm_num [outerLo]
  have hhi : outerHi s ≤ 4 := by fin_cases s <;> norm_num [outerHi,pi_lt_four.le]
  have hh : 0 ≤ outerHi s := by fin_cases s <;> norm_num [outerHi,pi_pos.le]
  let q := r.val+1
  have hvol : 2*((outerHi s)^q-(outerLo s)^q)/((r.val:ℝ)+1) ≤ 2*4^q := by
    apply (div_le_iff₀ (by positivity)).mpr
    have H := pow_le_pow_left₀ hh hhi q
    nlinarith only [H,pow_nonneg hlo q,mul_nonneg (Nat.cast_nonneg (α:=ℝ) r.val) (by positivity : (0:ℝ) ≤ 4^q)]
  have hi : σ^q*(exp (-(pairRate s false:ℝ)*d)*(2*((outerHi s)^q-(outerLo s)^q)/((r.val:ℝ)+1))) ≤
      2*(4*σ)^q*exp (-M/100) := by
    have HH := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hvol (exp_pos _).le).trans
      (mul_le_mul_of_nonneg_right Hexp (by positivity))) (pow_nonneg hσ q)
    rw [mul_pow]; convert HH using 1; ring
  apply hi.trans
  let B := 4*(259/1000)*M^2/64
  have hsq := sq_sqrt hp.le
  have hroot : √M ≤ M/64 := by nlinarith only [mul_le_mul_of_nonneg_right hr (sqrt_nonneg M),hsq]
  have hB : 4*σ ≤ B := by
    have hh := mul_le_mul_of_nonneg_left hroot hp.le
    dsimp only [B]; linarith only [hσ',hh]
  have hB' : 1 ≤ B := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4096) hM 2
    dsimp [B]; linarith only [hh]
  have hpow := (pow_le_pow_left₀ (by positivity : 0 ≤ 4*σ) hB q).trans
    (pow_le_pow_right₀ hB' (by dsimp [q]; omega : q ≤ 3))
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num : (0:ℝ)≤2)) (exp_pos _).le).trans
  rw [show 2*B^3*exp (-M/100)=(2*(4*(259/1000)*4096*64)^3)*((M/4096)^6*exp (-M/100)) by dsimp [B]; ring]
  exact (mul_le_mul_of_nonneg_left (normalized_decay hM) (by norm_num)).trans outer_number

end CentralUnimodality.MarkedExcursion
