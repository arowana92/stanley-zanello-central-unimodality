module

public import CentralUnimodality.PolynomialGaussianDefect
public import CentralUnimodality.LatticeCubicInputs
import Mathlib.Analysis.Calculus.MeanValue

/-! Convert the checked differential-equation residuals into uniform
value and derivative bounds for the two elementary input functions. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

open Real Set

theorem cubic_enclosure {f f' : ℝ → ℝ} {a V η e : ℝ} (ha : 0≤a) (hη : 0≤η)
    (hf : ∀ x, HasDerivAt f (f' x) x) (h₀ : |f 0-1|≤e)
    (hode : ∀ x∈Icc 0 V, |f' x+3*a*x^2*f x|≤η)
    {v : ℝ} (hv : v∈Icc 0 V) : |f v-exp (-(a*v^3))|≤e+V*η := by
  let g := fun x => exp (a*x^3)*f x
  let d := fun x => exp (a*x^3)*(f' x+3*a*x^2*f x)
  have dg (x : ℝ) : HasDerivAt g (d x) x := by
    have mon : HasDerivAt (fun t : ℝ => a*t^3) (3*a*x^2) x := by
      convert (((hasDerivAt_id x).pow 3).const_mul a) using 1 <;> simp; ring
    convert mon.exp.mul (hf x) using 1
    dsimp only [d]; ring
  have derBound (x : ℝ) (hx : x∈Ico 0 v) : ‖d x‖≤exp (a*v^3)*η := by
    rw [Real.norm_eq_abs,show |d x|=exp (a*x^3)*|f' x+3*a*x^2*f x| by
      simp [d,abs_mul,abs_of_pos (exp_pos _)]]
    have ord := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1 hx.2.le 3) ha
    exact mul_le_mul (exp_le_exp.mpr ord) (hode x ⟨hx.1,hx.2.le.trans hv.2⟩) (abs_nonneg _) (exp_pos _).le
  have dist := norm_image_sub_le_of_norm_deriv_le_segment' (a:=0) (b:=v)
    (fun x _ => (dg x).hasDerivWithinAt) derBound v ⟨hv.1,le_rfl⟩
  simp only [g,zero_pow (by decide : 3≠0),mul_zero,exp_zero,one_mul,Real.norm_eq_abs,sub_zero] at dist
  have triangle := abs_add_le (exp (a*v^3)*f v-f 0) (f 0-1)
  rw [sub_add_sub_cancel] at triangle
  have total := triangle.trans (add_le_add dist h₀)
  have hp := exp_pos (a*v^3)
  have ee : 1≤exp (a*v^3) := one_le_exp (mul_nonneg ha (pow_nonneg hv.1 3))
  have H : |f v-exp (-(a*v^3))|=|exp (a*v^3)*f v-1|/exp (a*v^3) := by
    have id : exp (a*v^3)*f v-1=exp (a*v^3)*(f v-exp (-(a*v^3))) := by
      rw [mul_sub,← exp_add,add_neg_cancel,exp_zero]
    rw [id,abs_mul,abs_of_pos hp]
    field_simp
  rw [H,div_le_iff₀ hp]
  have h₁ := mul_le_mul_of_nonneg_right ee ((abs_nonneg _).trans h₀)
  have h₂ := mul_le_mul_of_nonneg_left hv.2 (mul_nonneg hp.le hη)
  linarith only [total,h₁,h₂]

private theorem certified_input (a : List ℤ) (k : ℤ) {c : ℝ} (hc : 0≤c)
    (hk : (k:ℝ)=3*c*256*64^2)
    (hbudget : odeBudget a k*10^22≤2*2^120)
    (hzero : (endpointNumerator a-2*2^120).natAbs*10^22≤2*2^120)
    {v : ℝ} (hv : v∈Icc (0:ℝ) 256) :
    |value a v-exp (-(c*v^3))|≤2/10^22 ∧
    |deriv (value a) v+3*c*v^2*exp (-(c*v^3))|≤1/(256*10^22)+3*c*256^2*(2/10^22) := by
  have budget : (odeBudget a k:ℝ)*10^22≤2*2^120 := by exact_mod_cast hbudget
  have zero : |(endpointNumerator a:ℝ)-2*2^120| * 10^22≤2*2^120 := by
    have H := (Nat.cast_le (α:=ℤ)).mpr hzero
    push_cast [Int.natCast_natAbs] at H
    exact_mod_cast H
  have initial : |value a 0-1|≤1/10^22 := by
    rw [value_zero,show (endpointNumerator a:ℝ)/(2*2^120)-1=((endpointNumerator a:ℝ)-2*2^120)/(2*2^120) by ring,
      abs_div,abs_of_pos (by positivity : (0:ℝ)<2*2^120)]
    norm_num at zero ⊢
    linarith only [zero]
  have ode (x : ℝ) (hx : x∈Icc (0:ℝ) 256) : |deriv (value a) x+3*c*x^2*value a x|≤1/(256*10^22) := by
    have H := ode_value_bound a k hx
    rw [hk,show 256*deriv (value a) x+3*c*256*64^2*(x/64)^2*value a x =
      256*(deriv (value a) x+3*c*x^2*value a x) by ring,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<256)] at H
    linarith only [H,budget]
  have hv₀ : |value a v-exp (-(c*v^3))|≤2/10^22 := by
    have exact := cubic_enclosure hc (by norm_num) (fun x => (value_hasDerivAt a x).differentiableAt.hasDerivAt)
      initial ode hv
    linarith only [exact]
  refine ⟨hv₀,?_⟩
  have id : deriv (value a) v+3*c*v^2*exp (-(c*v^3))=
    (deriv (value a) v+3*c*v^2*value a v)-3*c*v^2*(value a v-exp (-(c*v^3))) := by ring
  rw [id]
  apply (abs_sub ..).trans
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤3*c*v^2)]
  apply add_le_add (ode v hv)
  exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv.1 hv.2 2) (by positivity))
    hv₀ (abs_nonneg _) (by positivity)

theorem gaussian_inputs {v : ℝ} (hv : v∈Icc (0:ℝ) 256) :
    |value freeCandidate v-ReturnSplit.freeCurve v|≤2/10^22 ∧
    |deriv (value freeCandidate) v+(v^2/8)*ReturnSplit.freeCurve v|≤2/10^18 ∧
    |value bridgeCandidate v-ReturnSplit.bridgeCurve v|≤2/10^22 ∧
    |deriv (value bridgeCandidate) v+(v^2/32)*ReturnSplit.bridgeCurve v|≤5/10^19 := by
  obtain ⟨fa,ba,fz,bz⟩ := gaussian_budgets
  have F := certified_input freeCandidate 131072 (c:=1/24) (by norm_num) (by norm_num) fa fz hv
  have B := certified_input bridgeCandidate 32768 (c:=1/96) (by norm_num) (by norm_num) ba bz hv
  have eqF : (1/24:ℝ)*v^3=v^3/24 := by ring
  have eqB : (1/96:ℝ)*v^3=v^3/96 := by ring
  rw [eqF,show 3*(1/24:ℝ)*v^2=v^2/8 by ring] at F
  rw [eqB,show 3*(1/96:ℝ)*v^2=v^2/32 by ring] at B
  exact ⟨F.1,F.2.trans (by norm_num),B.1,B.2.trans (by norm_num)⟩

end CentralUnimodality.PolynomialTrial
