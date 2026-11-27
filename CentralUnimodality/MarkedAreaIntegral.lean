module

public import CentralUnimodality.MarkedExcursionTail
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The marked-height estimate integrated against an exponential tilt.
The constants agree with the first-hit bound in the right-flank argument. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion

open Real MeasureTheory Set

private noncomputable def gauss (x : ℝ) := exp (-(x^2))

private theorem half_integral {a : ℝ} (ha : 0 ≤ a) :
    ∫ x in 0..a, gauss x ≤ min (√π/2) a := by
  have hg : Continuous gauss := by unfold gauss; fun_prop
  apply le_min
  · rw [intervalIntegral.integral_of_le ha]
    have hi : Integrable gauss := by
      change Integrable (fun x : ℝ => exp (-(x^2)))
      simpa using (integrable_exp_neg_mul_sq (b := 1) one_pos)
    have h := setIntegral_mono_set (μ := volume) (f := gauss) (t := Ioi 0)
      hi.integrableOn (ae_of_all _ (fun _ => (exp_pos _).le))
      (show Ioc 0 a ⊆ Ioi (0:ℝ) from fun _ hx => hx.1).eventuallySubset
    apply h.trans_eq
    simpa [gauss] using integral_gaussian_Ioi 1
  · calc
      _ ≤ ∫ _x in (0:ℝ)..a, (1:ℝ) := by
        apply intervalIntegral.integral_mono_on ha (hg.intervalIntegrable ..) (continuous_const.intervalIntegrable ..)
        intro x _
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg x))
      _ = a := by simp

private theorem shifted_integral {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    ∫ x in 0..z, exp (y*x-x^2) ≤ exp (y^2/4)*((√π+min (√π) y)/2) := by
  let a := y/2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hg : Continuous gauss := by unfold gauss; fun_prop
  have flip : (∫ x in -a..0, gauss x) = ∫ x in 0..a, gauss x := by
    simpa [gauss] using (intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := a) gauss).symm
  have he : (fun x : ℝ => exp (y*x-x^2)) = fun x => exp (y^2/4)*gauss (x-a) := by
    funext x
    rw [gauss,← Real.exp_add]
    congr 1; dsimp [a]; ring
  rw [he,intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_sub_right,zero_sub]
  apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
  calc
    _ ≤ ∫ x in -a..z, gauss x := by
      apply intervalIntegral.integral_mono_interval le_rfl (by linarith only [hz]) (by linarith only [ha])
      · exact ae_of_all _ (fun _ => (exp_pos _).le)
      · exact hg.intervalIntegrable ..
    _ = (∫ x in 0..a, gauss x) + ∫ x in 0..z, gauss x := by
      rw [← flip,intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable ..) (hg.intervalIntegrable ..)]
    _ ≤ min (√π/2) a + √π/2 := add_le_add (half_integral ha) ((half_integral hz).trans (min_le_left ..))
    _ = _ := by dsimp [a]; rw [min_div_div_right (by norm_num : (0:ℝ) ≤ 2)]; ring

private theorem cell_integral {c h : ℝ} (hc : 0 ≤ c) (hh : 0 < h) (i : ℕ) :
    (exp (c*(i+1))-exp (c*i))*exp (-(((i:ℝ)+1)*(i+2)/h^2)) ≤
      ∫ x in (i:ℝ)/h..((i:ℝ)+1)/h, (c*h)*exp ((c*h)*x-x^2) := by
  let y := c*h
  let L := (i:ℝ)/h
  let R := ((i:ℝ)+1)/h
  let g := exp (-(((i:ℝ)+1)*(i+2)/h^2))
  have hi : L ≤ R := by dsimp [L,R]; gcongr; linarith
  have hprimitive : (∫ x in L..R, y*exp (y*x)) = exp (c*(i+1))-exp (c*i) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => exp (y*x))
      (a := L) (b := R) (f' := fun x => y*exp (y*x))
      (fun x _ => by simpa [mul_comm] using (((hasDerivAt_id x).const_mul y).exp))
      ((by fun_prop : Continuous (fun x => y*exp (y*x))).intervalIntegrable ..)
    have hl : y*L = c*i := by dsimp [y,L]; field_simp
    have hr : y*R = c*(i+1) := by dsimp [y,R]; field_simp
    rwa [hl,hr] at h
  rw [← hprimitive,← intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_mono_on hi
    ((by fun_prop : Continuous (fun x => (y*exp (y*x))*g)).intervalIntegrable ..)
    ((by fun_prop : Continuous (fun x => y*exp (y*x-x^2))).intervalIntegrable ..)
  intro x hx
  have hx0 : 0 ≤ x := (div_nonneg (Nat.cast_nonneg _) hh.le).trans hx.1
  have hx2 := sq_le_sq₀ hx0 (show 0 ≤ R by dsimp [R]; positivity) |>.mpr hx.2
  have hg : g ≤ exp (-(x^2)) := by
    apply exp_le_exp.mpr
    dsimp [R] at hx2
    rw [div_pow] at hx2
    have hpc : ((i:ℝ)+1)^2 ≤ (i+1)*(i+2) := by nlinarith only [Nat.cast_nonneg (α := ℝ) i]
    exact neg_le_neg (hx2.trans (div_le_div_of_nonneg_right hpc (sq_nonneg h)))
  rw [sub_eq_add_neg,Real.exp_add,← mul_assoc]
  exact mul_le_mul_of_nonneg_left hg (by dsimp [y]; positivity)

/-- Closed estimate for the excursion area. In the first-hit application
the exponent is λ times the area divided by 2s, so c = λ(2d+1)/(2s). -/
theorem area_exp_gaussian (d : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    let y := c*√((d:ℝ)+1)
    (∑ w ∈ dycks d, exp (c*walkArea w/(2*d+1))) ≤
      (dycks d).card * (exp (y^2/4)*(1+y/2*(√π+min (√π) y))) := by
  let H := √((d:ℝ)+1)
  let y := c*H
  have hH : 0 < H := by dsimp [H]; positivity
  have hsq : H^2 = (d:ℝ)+1 := Real.sq_sqrt (by positivity)
  have hy : 0 ≤ y := mul_nonneg hc hH.le
  apply (area_exp_bound d hc).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have h := Finset.sum_le_sum (s := Finset.range d) (fun i _ => cell_integral hc hH i)
  rw [hsq] at h
  let g := fun x => y*exp (y*x-x^2)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have he := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (a := fun i : ℕ => (i:ℝ)/H)
    (n := d) (f := g) (fun _ _ => hg.intervalIntegrable ..)
  simp only [Nat.cast_succ,Nat.cast_zero,zero_div] at he
  change _ ≤ ∑ i ∈ Finset.range d, ∫ x in (i:ℝ)/H..(i+1)/H, g x at h
  rw [he] at h
  dsimp only [g] at h
  rw [intervalIntegral.integral_const_mul] at h
  have hlim := shifted_integral hy (div_nonneg (Nat.cast_nonneg d) hH.le)
  have hs := h.trans (mul_le_mul_of_nonneg_left hlim hy)
  have h1 : 1 ≤ exp (y^2/4) := Real.one_le_exp (by positivity)
  change _ ≤ exp (y^2/4)*(1+y/2*(√π+min (√π) y))
  linarith only [hs,h1]

end CentralUnimodality.MarkedExcursion
