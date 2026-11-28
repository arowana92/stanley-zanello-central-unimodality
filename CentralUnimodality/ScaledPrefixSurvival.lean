module

public import CentralUnimodality.PrefixSurvivalLower
public import CentralUnimodality.RankBinSetup

/-! A uniform finite-time contribution to the survival denominator, in
the scaling of the first-hit and late-hit estimates. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

theorem fair_live_lower {t : ℕ} (ht : 255≤t) : 79/100≤live 0 0 t 1*√t := by
  have anchor : (79/100:ℝ)^2≤(2*128-1)*(survival 128)^2 := by
    rw [survival,Nat.centralBinom,Nat.choose_eq_factorial_div_factorial (by decide)]
    norm_num1
  have mono : Monotone (fun j : ℕ => (2*(j:ℝ)-1)*(survival j)^2) := by
    apply monotone_nat_of_le_succ
    intro j
    rw [survival_succ,Nat.cast_succ]; field_simp
    nlinarith only [sq_nonneg (survival j),mul_nonneg (sq_nonneg (survival j)) (Nat.cast_nonneg (α:=ℝ) j)]
  let j := (t+1)/2
  have hj : 128≤j := by dsimp [j]; omega
  have H := mono hj
  change (2*(128:ℕ)-1:ℝ)*(survival 128)^2≤(2*(j:ℝ)-1)*(survival j)^2 at H
  have hcast : 2*(j:ℝ)≤t+1 := by exact_mod_cast (show 2*j≤t+1 by dsimp [j]; omega)
  rw [fair_live_exact]
  apply (sq_le_sq₀ (by norm_num) (mul_nonneg (survival_pos _).le (sqrt_nonneg _))).mp
  rw [mul_pow,sq_sqrt (Nat.cast_nonneg _)]
  change _≤(survival j)^2*t
  norm_num only [Nat.cast_ofNat] at H
  nlinarith only [anchor,H,mul_le_mul_of_nonneg_right hcast (sq_nonneg (survival j))]

theorem negative_exp_quadratic {x : ℝ} (hx : 0≤x) : exp (-x)≤1-x+x^2/2 := by
  have h := Real.sum_le_exp_of_nonneg hx 3
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rw [exp_neg,inv_eq_one_div]
  apply (div_le_iff₀ (exp_pos _)).mpr
  have hp : 0≤1-x+x^2/2 := by nlinarith only [sq_nonneg (x-1)]
  nlinarith only [mul_le_mul_of_nonneg_left h hp,sq_nonneg (x^2)]

theorem scaled_prefix_survival {m L : ℕ} (hm : 4096≤m) (hL : 255≤L)
    {c v U f K : ℝ} (hU : 0≤U) (hf : 0≤f) (hK : 0<K) (hscale : K*√f≤79/100)
    (htime : (L:ℝ)≤f*m) (hpar : ∀ i<L, U/√m≤v-c*i) :
    2*U*(1-U/64)+K*exp (-(U/64+U/K+f*U^2/2)) ≤ live c v L 1*√m := by
  have hm' : (4096:ℝ)≤m := by exact_mod_cast hm
  have hm₀ : (0:ℝ)<m := by linarith
  have hr : 0<√(m:ℝ) := sqrt_pos.mpr hm₀
  have h64 : 64≤√(m:ℝ) := (le_sqrt (by norm_num) hm₀.le).mpr (by linarith)
  have hL₀ : (0:ℝ)<L := by exact_mod_cast (show 0<L by omega)
  let P := live 0 0 L 1
  let q := U/√m
  have hP : 0<P := by dsimp [P]; rw [fair_live_exact]; exact survival_pos _
  have hs : K≤P*√m := by
    have H := sqrt_le_sqrt htime
    rw [sqrt_mul hf] at H
    have HK := mul_le_mul_of_nonneg_right hscale hr.le
    have H₂ := mul_le_mul_of_nonneg_left (fair_live_lower hL) hr.le
    have H₃ := mul_le_mul_of_nonneg_left H hK.le
    apply le_of_mul_le_mul_right (a:=√(L:ℝ)) _ (sqrt_pos.mpr hL₀)
    dsimp only [P]; linarith only [HK,H₂,H₃]
  have hq : 0≤q := div_nonneg hU hr.le
  have hqU : q*√m=U := div_mul_cancel₀ U hr.ne'
  have hquo : q≤U/64 := by exact div_le_div_of_nonneg_left hU (by norm_num) h64
  have hpart : q/P≤U/K := by
    apply (div_le_div_iff₀ hP hK).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hs hq,congrArg (· * P) hqU]
  have hvar : (L:ℝ)*q^2 ≤ f*U^2 := by
    have H := mul_le_mul_of_nonneg_right htime (sq_nonneg q)
    have he := congrArg (·^2) hqU
    rw [mul_pow,sq_sqrt hm₀.le] at he
    linarith only [H,congrArg (f*·) he]
  have hsurv := prefix_survival_lower c v q L hpar
  change 1-exp (-2*q)+P*exp (-q-q/P-L*q^2/2)≤_ at hsurv
  have HG := exp_le_exp.mpr (show -(U/64+U/K+f*U^2/2)≤ -q-q/P-L*q^2/2 by linarith only [hquo,hpart,hvar])
  have hterm := mul_le_mul hs HG (exp_pos _).le (mul_nonneg hP.le hr.le)
  have hbase := negative_exp_quadratic (by linarith only [hq] : 0≤2*q)
  rw [← neg_mul] at hbase
  have hlim := mul_le_mul_of_nonneg_left hquo hU
  have H₀ := mul_le_mul_of_nonneg_right hbase hr.le
  have H := mul_le_mul_of_nonneg_right hsurv hr.le
  nlinarith only [H,H₀,hterm,hqU,congrArg (q*·) hqU,hlim]

end CentralUnimodality.MarkedExcursion
