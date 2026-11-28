module

public import CentralUnimodality.RankBinExponent
public import CentralUnimodality.LateUniformBudget

/-! Compare the late-event envelope with its rational probability factor
at every length in the saddle bin. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic
open Real

private theorem late_prefactor {M L P den root cap : ℝ} (hM : 0<M) (hden : 0<den)
    (hroot : 0<root) (hcap : 0 ≤ cap) (hP : den ≤ P*√M) (hL : root*√M ≤ √L) :
    (2*(cap/√M)+(4/5)/√L)/P ≤ (2*cap+(4/5)/root)/den := by
  have hr := sqrt_pos.mpr hM
  have hPp : 0<P := pos_of_mul_pos_left (hden.trans_le hP) hr.le
  have hLp := (mul_pos hroot hr).trans_le hL
  have hshift : (4/5:ℝ)/√L ≤ (4/5)/(root*√M) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos hroot hr) hL
  have he : 2*(cap/√M)+(4/5)/(root*√M)=(2*cap+(4/5)/root)/√M := by ring
  apply (div_le_div_of_nonneg_right (add_le_add (le_refl _) hshift) hPp.le).trans
  rw [he,div_div]
  exact div_le_div_of_nonneg_left (by positivity) hden (by rwa [mul_comm])

theorem late_scale_to_bin {m L T : ℕ} {g G σ P : ℝ} {l d a cap x den : ℚ}
    (hm : 4096 ≤ m) (ht : (837/1000)*(m:ℝ) ≤ (T-L:ℕ))
    (hσ : 0 ≤ σ) (hu : σ ≤ (259/1000)*sizeScale m) (hl : 0 ≤ l)
    (hroot : 0<rootLo l) (hL : (l:ℝ)*m ≤ L) (hden : 0<den) (hP : (den:ℝ) ≤ P*√m)
    (ha : lateHeightParameter g d lateCut=(a:ℝ)) (hcap : 0 ≤ cap)
    (hc : (G+d)/2-a=(cap:ℝ)) (hx : x=d^2*energy/8-a^2/2) (hn : x ≤ 0) (r : Fin 3) :
    σ^(r.val+1)/P*lateRankAllowance m L T g G d lateCut r ≤
      ((decay (-x)*(2*cap+(4/5)/rootLo l)/den:ℚ):ℝ)*lateUniformLimit r := by
  have hm' : (4096:ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0<(m:ℝ) := by linarith
  have hdl : 0<(den:ℝ) := by exact_mod_cast hden
  have hpr : 0<P := pos_of_mul_pos_left (hdl.trans_le hP) (sqrt_nonneg _)
  have hrt : 0<(rootLo l:ℝ) := by exact_mod_cast hroot
  have hl' : 0 ≤ (l:ℝ) := by exact_mod_cast hl
  have hc' : 0 ≤ (cap:ℝ) := by exact_mod_cast hcap
  have hLs : (rootLo l:ℝ)*√m ≤ √L := calc
    _ ≤ √(l:ℝ)*√m := mul_le_mul_of_nonneg_right (root_enclosure hl).1 (sqrt_nonneg _)
    _ = √((l:ℝ)*m) := (sqrt_mul hl' _).symm
    _ ≤ _ := sqrt_le_sqrt hL
  have hprob := late_prefactor hp hdl hrt hc' hP hLs
  have hE := late_bin_exponential hm hx hn
  have hprod := mul_le_mul hE hprob (by positivity) ((exp_pos _).le.trans hE)
  have HB := late_uniform_budget hm' ht hσ hu r
  have hA : 0 ≤ lateUniformLimit r := by fin_cases r <;> norm_num [lateUniformLimit]
  let E := exp ((d:ℝ)^2*(labelSquares m/(m:ℝ)^3)/8-(a:ℝ)^2/2)
  let F := (2*((cap:ℝ)/√m)+(4/5)/√L)/P
  have hpF : 0 ≤ E*F := by dsimp only [E,F]; positivity
  have H := mul_le_mul HB hprod hpF hA
  dsimp only [lateRankAllowance]
  rw [ha,hc]
  push_cast
  calc
    _ = (σ^(r.val+1)*lateFourierBudget (T-L:ℕ) r.val)*(E*F) := by dsimp [E,F]; ring
    _ ≤ _ := H
    _ = _ := by ring

end CentralUnimodality.MarkedExcursion.BinArithmetic
