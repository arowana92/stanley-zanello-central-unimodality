module

public import CentralUnimodality.PinnedMiddleMass
public import CentralUnimodality.InnerArcNumbers
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Point probabilities for independent signs with possibly different
drifts. A central Fourier arc uses a sine Taylor bound. The complement
is exponentially small at the first admissible block length. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real MeasureTheory Set

private theorem sine_cap {x A : ℝ} (hx : 0≤x) (h : x≤A) :
    (1-A^2/6)*x≤sin x := by
  have he := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx h 2) hx
  linarith only [he,sin_ge_sub_cube hx]

private theorem endpoint_arcs {A p a b θ : ℝ} (hA : 0≤A) (hA' : A≤π/2) (hS : 0≤1-A^2/6)
    (hp : 0≤p) (ha : a≤p*(1-A^2/6)^2/2) (hb : b≤2*p*((1-A^2/6)*A)^2)
    (hθ : |θ|≤π) (c u : ℝ) (t : ℕ)
    (hv : ∀ i<t, p≤upChance (-(u-c*i))*upChance (u-c*i)) :
    ‖downTransform c u t θ‖ ≤ exp (-(a*t)*θ^2)+exp (-(b*t)) := by
  let x := |θ|/2
  have hx : 0≤x := by dsimp [x]; positivity
  have hs : sin (θ/2)^2=sin x^2 := by
    rcases le_total 0 θ with h|h
    · simp [x,abs_of_nonneg h]
    · dsimp [x]; rw [abs_of_nonpos h,neg_div,sin_neg,neg_sq]
  have H := down_transform_bound c u θ t hv
  rw [hs] at H
  have ht : 0≤2*p*(t:ℝ) := by positivity
  by_cases h : x≤A
  · have HH := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hS hx) (sine_cap hx h) 2) ht
    have he := mul_le_mul_of_nonneg_right ha (mul_nonneg (Nat.cast_nonneg (α:=ℝ) t) (sq_nonneg θ))
    dsimp only [x] at HH ⊢
    simp only [mul_pow,div_pow,sq_abs] at HH
    apply H.trans ((exp_le_exp.mpr _).trans (le_add_of_nonneg_right (exp_pos _).le))
    linarith only [HH,he]
  · have hxπ : x≤π/2 := by dsimp [x]; linarith only [hθ]
    have hm := strictMonoOn_sin.monotoneOn (a:=A) (b:=x) (show A∈Icc (-(π/2)) (π/2) from
      ⟨by linarith only [hA,pi_pos],hA'⟩) ⟨by linarith only [hx,pi_pos],hxπ⟩ (le_of_not_ge h)
    have HH := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hS hA) ((sine_cap hA le_rfl).trans hm) 2) ht
    have he := mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg (α:=ℝ) t)
    apply H.trans ((exp_le_exp.mpr _).trans (le_add_of_nonneg_left (exp_pos _).le))
    linarith only [HH,he]

theorem endpoint_gaussian_cap {p A a b : ℝ} (hA : 0≤A) (hA' : A≤π/2) (hS : 0≤1-A^2/6)
    (hp : 0≤p) (ha : 0<a) (ha' : a≤p*(1-A^2/6)^2/2) (hb : b≤2*p*((1-A^2/6)*A)^2)
    (c u : ℝ) {t : ℕ} (ht : 0<t) (j : ℤ)
    (hv : ∀ i<t, p≤upChance (-(u-c*i))*upChance (u-c*i)) :
    downMass c u t j*√t ≤ √(π/a)/(2*π)+√t*exp (-(b*t)) := by
  let G (θ : ℝ) := exp (-(a*t)*θ^2)
  let C := exp (-(b*t))
  let I := Ioc (-π) π
  have ht' : (0:ℝ)<t := by exact_mod_cast ht
  have hg : Integrable G := integrable_exp_neg_mul_sq (mul_pos ha ht')
  have hi : IntegrableOn (fun _ : ℝ => C) I := integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have H := norm_integral_le_of_norm_le (μ:=volume.restrict I) (hg.integrableOn.add hi)
    (f:=fun θ : ℝ => downTransform c u t θ*phase (-θ*j)) (by
      filter_upwards [ae_restrict_mem (measurableSet_Ioc (a:= -π) (b:=π))] with θ hθ
      rw [norm_mul,phase_norm,mul_one]
      exact endpoint_arcs hA hA' hS hp ha' hb (abs_le.mpr ⟨hθ.1.le,hθ.2⟩) c u t hv)
  have hπ : -π≤π := by linarith only [pi_pos]
  have hr := down_mass_inverse c u t j
  rw [intervalIntegral.integral_of_le hπ] at hr
  have hm : 0≤downMass c u t j := Finset.sum_nonneg fun w _ => by
    split <;> first | exact (signMass_pos ..).le | exact le_rfl
  change ‖∫ θ in I, downTransform c u t θ*phase (-θ*j)‖ ≤ ∫ θ in I, G θ+C at H
  rw [hr,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity) hm),
    integral_add hg.integrableOn hi,setIntegral_const,Real.volume_real_Ioc_of_le hπ,smul_eq_mul] at H
  have hg' := setIntegral_le_integral (s:=I) hg (Filter.Eventually.of_forall (fun θ => (exp_pos _).le))
  unfold G at hg'
  rw [integral_gaussian] at hg'
  have h : (2*π)*downMass c u t j≤√(π/(a*t))+(2*π)*exp (-(b*t)) := by
    dsimp only [C] at H; linarith only [H,hg']
  have H' := mul_le_mul_of_nonneg_right h (sqrt_nonneg (t:ℝ))
  have he : √(π/(a*t))*√t=√(π/a) := by
    rw [← sqrt_mul (by positivity),show π/(a*t)*t=π/a by field_simp]
  apply le_of_mul_le_mul_left (a:=2*π) _ (by positivity)
  rw [add_mul,he] at H'
  field_simp at *
  linarith only [H']

private theorem tail_at_start {b t T : ℝ} (hT : 0<T) (ht : T≤t) (hb : 1≤b*T) :
    √t*exp (-(b*t)) ≤ √T*exp (-(b*T)) := by
  have hratio : 1≤t/T := (one_le_div hT).mpr ht
  have hs : √t≤√T*(t/T) := by
    apply (sq_le_sq₀ (sqrt_nonneg _) (mul_nonneg (sqrt_nonneg _) (by positivity))).mp
    rw [sq_sqrt (hT.le.trans ht),mul_pow,sq_sqrt hT.le]
    have H := mul_le_mul_of_nonneg_left hratio (hT.le.trans ht)
    field_simp at H ⊢
    nlinarith only [H]
  have he : t/T≤exp (b*(t-T)) := by
    apply le_trans _ (add_one_le_exp _)
    apply (div_le_iff₀ hT).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hb (sub_nonneg.mpr ht)]
  have H := mul_le_mul_of_nonneg_right (hs.trans (mul_le_mul_of_nonneg_left he (sqrt_nonneg _))) (exp_pos (-(b*t))).le
  rwa [mul_assoc,← exp_add,show b*(t-T)+ -(b*t)= -(b*T) by ring] at H

/-- The narrow early middle block uses t≥80 and site variance ≥.238.
The longer late suffix allows site variance .235, including |u|≤.24. -/
theorem endpoint_cap_numbers (late : Bool) (c u : ℝ) {t : ℕ} (ht : (if late then 255 else 80)≤t)
    (j : ℤ) (hv : ∀ i<t, (if late then 47/200 else 119/500:ℝ)≤upChance (-(u-c*i))*upChance (u-c*i)) :
    downMass c u t j*√t ≤ (if late then 21/25 else 43/50:ℝ) := by
  let t₀ : ℚ := if late then 255 else 80
  let p : ℚ := if late then 47/200 else 119/500
  let A : ℚ := if late then 3/10 else 1/2
  let a := p*(1-A^2/6)^2/2
  let b := 4*A^2*a
  let g : ℚ := if late then 837/1000 else 855/1000
  let e : ℚ := if late then 3/1000 else 5/1000
  let root : ℚ := if late then 16 else 9
  have hg : 1≤4*(314/100)*a*g^2 ∧ root*upperNegExp (b*t₀)≤e :=
    by cases late <;> decide +kernel
  have ht₀ : (t₀:ℝ)≤t := by cases late <;> norm_num [t₀] at ht ⊢ <;> exact_mod_cast ht
  have ht₀p : (0:ℝ)<t₀ := by cases late <;> norm_num [t₀]
  have hpos : (0:ℝ)<a := by cases late <;> norm_num [a,A,p]
  have hπ : (A:ℝ)≤π/2 := by cases late <;> norm_num [A] <;> linarith only [pi_gt_three]
  have hp : (0:ℝ)≤p := by cases late <;> norm_num [p]
  have hCap := endpoint_gaussian_cap (p:=(p:ℝ)) (a:=(a:ℝ)) (b:=(b:ℝ)) (A:=(A:ℝ))
    (by cases late <;> norm_num [A]) hπ (by cases late <;> norm_num [A]) hp hpos
    (by dsimp [a]; push_cast; rfl) (by dsimp [b,a]; push_cast; apply le_of_eq; ring)
    c u (by exact_mod_cast (ht₀p.trans_le ht₀) : 0<t) j (by cases late <;> simpa [p] using hv)
  have hG : √(π/(a:ℝ))/(2*π)≤(g:ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    apply (sqrt_le_left (by cases late <;> dsimp [g] <;> positivity)).mpr
    apply (div_le_iff₀ hpos).mpr
    have H := (Rat.cast_le (K:=ℝ)).mpr hg.1
    push_cast at H
    have hπ₁ := mul_le_mul_of_nonneg_right pi_gt_d2.le (mul_nonneg hpos.le (sq_nonneg (g:ℝ)))
    nlinarith only [mul_le_mul_of_nonneg_left H pi_pos.le,mul_le_mul_of_nonneg_left hπ₁ pi_pos.le]
  have hB := tail_at_start ht₀p ht₀ (b:=(b:ℝ)) (by cases late <;> norm_num [b,t₀,a,p,A])
  have hr : √(t₀:ℝ)≤(root:ℝ) := by cases late <;> apply (sqrt_le_left (by norm_num [root])).mpr <;> norm_num [root,t₀]
  have hh := upperNegExp_sound (x:=b*t₀) (by cases late <;> decide +kernel)
  rw [Rat.cast_mul] at hh
  have hE := mul_le_mul hr hh (exp_pos _).le (by cases late <;> norm_num [root])
  have he : (root:ℝ)*(upperNegExp (b*t₀):ℝ)≤(e:ℝ) := by exact_mod_cast hg.2
  exact hCap.trans ((add_le_add hG (hB.trans (hE.trans he))).trans_eq (by cases late <;> norm_num [g,e]))

end CentralUnimodality.MarkedExcursion
