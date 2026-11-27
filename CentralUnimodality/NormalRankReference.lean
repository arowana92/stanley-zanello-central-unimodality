module

public import CentralUnimodality.FreeSuffixArcs
public import CentralUnimodality.GaussianMixtureBounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Real.Pi.Bounds

/-! Continuous Gaussian inversion with the lattice rank normalization, and
the Taylor costs of replacing its finite differences by derivatives. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real MeasureTheory

noncomputable def normalDensity (x : ℝ) := normalHeight*bell x

/-- The reference Gaussian is integrated over the real line. -/
theorem normal_rank_inverse {σ : ℝ} (hσ : 0 < σ) (s : ℝ) :
    (∫ θ : ℝ, (exp (-(σ^2*θ^2/2)):ℂ)*phase (-θ*s)) =
      ((2*π/σ*normalDensity (s/σ):ℝ):ℂ) := by
  let b := σ^2/2
  have hb : 0 < b := by dsimp [b]; positivity
  have h := fourierIntegral_gaussian (b := (b:ℂ)) (by simpa using hb) (-s:ℂ)
  have hi (θ : ℝ) : (exp (-(σ^2*θ^2/2)):ℂ)*phase (-θ*s) =
      Complex.exp (Complex.I*(-(s:ℂ))*θ)*Complex.exp (-(b:ℂ)*(θ:ℂ)^2) := by
    unfold phase
    rw [Complex.ofReal_exp,mul_comm]
    dsimp only [b]; push_cast; congr 2 <;> ring
  simp_rw [hi]
  rw [h]
  have hr : ((π:ℂ)/b)^(1/2:ℂ) = (√(π/b):ℂ) := by
    rw [sqrt_eq_rpow,Complex.ofReal_cpow (by positivity)]; push_cast; rfl
  rw [hr]
  have he : -(-(s:ℂ))^2/(4*b)= ((-((s/σ)^2)/2:ℝ):ℂ) := by
    dsimp [b]; push_cast; field_simp; ring
  rw [he,← Complex.ofReal_exp,← Complex.ofReal_mul]
  apply congrArg (fun v : ℝ => (v:ℂ))
  have hs : √(π/b)=√(2*π)/σ := by
    dsimp [b]; rw [show π/(σ^2/2)=(2*π)/σ^2 by ring,Real.sqrt_div (by positivity),
      Real.sqrt_sq hσ.le]
  rw [hs,normalDensity,normalHeight,bell]
  have hp : 0 < √(2*π) := by positivity
  field_simp
  nlinarith only [sq_sqrt (by positivity : (0:ℝ) ≤ 2*π)]

private theorem density_derivative (x : ℝ) :
    HasDerivAt normalDensity (-x*normalDensity x) x := by
  have h := (((((hasDerivAt_id' x).pow 2).neg).div_const 2).exp).const_mul normalHeight
  change HasDerivAt (fun y : ℝ => normalHeight*exp (-(y^2)/2)) _ x
  convert h using 1; dsimp [normalDensity,bell]; ring

private theorem density_derivatives :
    iteratedDeriv 1 normalDensity = fun x => -x*normalDensity x := by
  funext x; rw [iteratedDeriv_one]; exact (density_derivative x).deriv

private theorem density_second : iteratedDeriv 2 normalDensity =
    fun x => (x^2-1)*normalDensity x := by
  rw [iteratedDeriv_succ,density_derivatives]
  funext x
  convert (((hasDerivAt_id' x).neg).mul (density_derivative x)).deriv using 1; dsimp; ring

private theorem density_third : iteratedDeriv 3 normalDensity =
    fun x => (3*x-x^3)*normalDensity x := by
  rw [iteratedDeriv_succ,density_second]
  funext x
  convert ((((hasDerivAt_id' x).pow 2).sub_const 1).mul (density_derivative x)).deriv using 1; dsimp; ring

private theorem density_fourth : iteratedDeriv 4 normalDensity =
    fun x => (x^4-6*x^2+3)*normalDensity x := by
  rw [iteratedDeriv_succ,density_third]
  funext x
  convert (((((hasDerivAt_id' x).const_mul 3).sub ((hasDerivAt_id' x).pow 3))).mul
    (density_derivative x)).deriv using 1; dsimp; ring

private theorem density_smooth (k : ℕ) : ContDiff ℝ k normalDensity := by unfold normalDensity bell; fun_prop

private theorem weighted_bell (x : ℝ) : bell x ≤ 1 ∧ x^2*bell x ≤ 2 ∧ x^4*bell x ≤ 8 := by
  let a := x^2/2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have he (z : ℝ) : z*exp (-a) ≤ 1 ↔ z ≤ exp a := by rw [exp_neg,← div_eq_mul_inv,div_le_one (exp_pos _)]
  have h₁ := (he a).mpr (by linarith only [Real.add_one_le_exp a])
  have h₂ := Real.sum_le_exp_of_nonneg ha 3
  norm_num [Finset.sum_range_succ,Nat.factorial] at h₂
  have h₂' := (he (a^2/2)).mpr (by linarith only [h₂,ha])
  change exp (-(x^2)/2) ≤ 1 ∧ _
  have hb : bell x=exp (-a) := by dsimp [bell,a]; congr 1; ring
  rw [hb]
  dsimp only [a] at h₁ h₂' ⊢
  refine ⟨exp_le_one_iff.mpr (by nlinarith [sq_nonneg x]),?_,?_⟩ <;> linarith only [h₁,h₂']

private theorem density_bounds (x : ℝ) :
    |iteratedDeriv 2 normalDensity x| ≤ 2 ∧ |iteratedDeriv 4 normalDensity x| ≤ 12 := by
  obtain ⟨h₀,h₂,h₄⟩ := weighted_bell x
  have hp : 0 < bell x := exp_pos _
  have hn : 0 ≤ normalHeight := by dsimp [normalHeight]; positivity
  have hn' : normalHeight ≤ 1/2 := by
    apply (div_le_iff₀ (show 0 < √(2*π) by positivity)).mpr
    have h : 2 ≤ √(2*π) := Real.le_sqrt_of_sq_le (by linarith only [pi_gt_three])
    linarith
  have hl : 0 ≤ x^2*bell x := mul_nonneg (sq_nonneg _) hp.le
  have hl' : 0 ≤ x^4*bell x := mul_nonneg (by positivity) hp.le
  rw [density_second,density_fourth]
  dsimp [normalDensity]
  constructor
  · rw [abs_le]
    constructor <;> nlinarith only [mul_le_mul_of_nonneg_left h₂ hn,mul_le_mul_of_nonneg_left h₀ hn,
      mul_nonneg hn hp.le,mul_nonneg hn hl,hn']
  · rw [abs_le]
    constructor <;> nlinarith only [mul_le_mul_of_nonneg_left h₄ hn,mul_le_mul_of_nonneg_left h₂ hn,
      mul_le_mul_of_nonneg_left h₀ hn,mul_nonneg hn hl',mul_nonneg hn hp.le,mul_nonneg hn hl,hn']

private theorem density_taylor {x h : ℝ} (hh : h ≠ 0) (n : ℕ) {K : ℝ}
    (hK : ∀ z, |iteratedDeriv (n+1) normalDensity z| ≤ K) :
    |normalDensity (x+h) - ∑ k ∈ Finset.range (n+1), h^k/(k.factorial:ℝ)*iteratedDeriv k normalDensity x|
      ≤ K*|h|^(n+1)/(n+1).factorial := by
  have hx : x ≠ x+h := by intro he; exact hh (by linarith)
  obtain ⟨z,_,H⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := n) hx (density_smooth _).contDiffOn
  have hpol : taylorWithinEval normalDensity n (Set.uIcc x (x+h)) x (x+h) =
      ∑ k ∈ Finset.range (n+1), h^k/(k.factorial:ℝ)*iteratedDeriv k normalDensity x := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx) (density_smooth k).contDiffAt Set.left_mem_uIcc]
    simp [div_eq_inv_mul]
  rw [← hpol,H,abs_div,abs_mul,abs_pow,abs_of_nonneg (by positivity : (0:ℝ) ≤ (n+1).factorial)]
  simp only [add_sub_cancel_left]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hK z) (by positivity)) (by positivity)

theorem normal_forward_error {σ : ℝ} (hσ : 0 < σ) (x : ℝ) :
    |σ*(normalDensity (x+1/σ)-normalDensity x)+x*normalDensity x| ≤ 1/σ := by
  have h := density_taylor (x := x) (one_div_ne_zero hσ.ne') 1 (fun z => (density_bounds z).1)
  norm_num [Finset.sum_range_succ,Nat.factorial,density_derivatives,abs_of_pos (one_div_pos.mpr hσ)] at h
  have h' := mul_le_mul_of_nonneg_left h hσ.le
  rw [show ∀ a : ℝ, σ*|a|=|σ*a| by intro a; rw [abs_mul,abs_of_pos hσ]] at h'
  rw [(density_derivative x).deriv] at h'
  simp only [one_div]
  convert h' using 1
  · congr 1; field_simp; ring
  · field_simp

theorem normal_curvature_error {σ : ℝ} (hσ : 0 < σ) (x : ℝ) :
    |σ^2*(normalDensity (x-1/σ)+normalDensity (x+1/σ)-2*normalDensity x)-
        (x^2-1)*normalDensity x| ≤ 1/σ^2 := by
  let d := 1/σ
  have hd : 0 < d := one_div_pos.mpr hσ
  have up := density_taylor (x := x) hd.ne' 3 (fun z => (density_bounds z).2)
  have dn := density_taylor (x := x) (neg_ne_zero.mpr hd.ne') 3 (fun z => (density_bounds z).2)
  norm_num [Finset.sum_range_succ,Nat.factorial,density_derivatives,density_second,density_third,
    abs_of_pos hd,abs_neg] at up dn
  have H := (abs_add_le _ _).trans (add_le_add dn up)
  have S := mul_le_mul_of_nonneg_left H (sq_nonneg σ)
  rw [show ∀ a : ℝ, σ^2*|a|=|σ^2*a| by intro a; rw [abs_mul,abs_of_nonneg (sq_nonneg σ)]] at S
  dsimp [d] at S
  convert S using 1 <;> (congr 1; field_simp; ring)

end CentralUnimodality.MarkedExcursion
