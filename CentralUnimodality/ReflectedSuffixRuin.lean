module

public import CentralUnimodality.FairRuinReflection
public import CentralUnimodality.EndpointGaussianCap
public import CentralUnimodality.MarkedLateCharacter
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! An endpoint cap under a homogeneous height tilt bounds the original
fair endpoint tail. Heights have span two. Reflection therefore improves
the exponential ruin allowance by the factor .84/(b sqrt n). -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

private theorem homogeneous_mass_change (b : ℝ) {n : ℕ} {w : List Bool} (hw : w∈words n) :
    signMass 0 0 w=cosh b^n*exp (-b*(displacement w:ℝ))*signMass 0 b w := by
  have H := signMass_density 0 b w
  have K := signMass_density 0 0 w
  simp only [coshProduct,zero_mul,sub_zero,Finset.prod_const,Finset.card_range,
    mem_words.mp hw,add_zero,cosh_zero,one_pow,mul_one,exp_zero] at H K
  apply (mul_left_inj' (by positivity : (2:ℝ)^n≠0)).mp
  rw [K,show cosh b^n*exp (-b*(displacement w:ℝ))*signMass 0 b w*2^n=
    exp (-b*(displacement w:ℝ))*(signMass 0 b w*(2^n*cosh b^n)) by ring,H,← exp_add]
  simp

theorem fair_tail_by_endpoints {b P : ℝ} (hb : 0<b) (hP : 0≤P) (n h : ℕ)
    (hcap : ∀ j : ℤ, downMass 0 b n j≤P) :
    fairHeightTail n ((h:ℤ)+1) ≤ cosh b^n*exp (-b*(h+1))*P/(1-exp (-2*b)) := by
  let J := (n-(h+1))/2
  let r := exp (-2*b)
  let A := cosh b^n*exp (-b*(h+1))
  have hr : 0≤r := (exp_pos _).le
  have hr' : r<1 := exp_lt_one_iff.mpr (by linarith only [hb])
  have hA : 0≤A := mul_nonneg (pow_nonneg (cosh_pos _).le _) (exp_pos _).le
  have H : fairHeightTail n ((h:ℤ)+1) ≤
      A*∑ j ∈ Finset.range (J+1), r^(J-j)*downMass 0 b n j := by
    rw [fair_height_words]
    simp only [downMass,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro w hw
    let d := (wordParts w).length
    have hlen := displacement_length w
    rw [mem_words.mp hw] at hlen
    change displacement w+2*(d:ℤ)=(n:ℤ) at hlen
    by_cases he : (h:ℤ)+1≤displacement w
    · rw [ite_eq_left he]
      have hd : d≤J := by dsimp only [J]; omega
      have hd' : d∈Finset.range (J+1) := Finset.mem_range.mpr (by omega)
      have hsingle := Finset.single_le_sum (s:=Finset.range (J+1)) (a:=d)
        (f:=fun j : ℕ => A*(r^(J-j)*(if (d:ℤ)=(j:ℤ) then signMass 0 b w else 0)))
        (fun j _ => mul_nonneg hA (mul_nonneg (pow_nonneg hr _) (ite_nonneg ((signMass_pos ..).le) le_rfl))) hd'
      simp only [ite_true] at hsingle
      apply le_trans _ hsingle
      rw [homogeneous_mass_change b hw]
      have hdisp : (h:ℝ)+1+2*((J-d:ℕ):ℝ)≤(displacement w:ℝ) := by
        exact_mod_cast (show (h:ℤ)+1+2*((J-d:ℕ):ℤ)≤displacement w by dsimp [J]; omega)
      have hex := exp_le_exp.mpr (mul_le_mul_of_nonpos_left hdisp (neg_nonpos.mpr hb.le))
      dsimp only [A,r]
      rw [← exp_nat_mul]
      have K : exp (-b*(displacement w:ℝ)) ≤ exp (-b*(h+1))*exp (((J-d:ℕ):ℝ)*(-2*b)) := by
        rw [← exp_add]; apply hex.trans_eq; congr 1; ring
      linarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left K (pow_nonneg (cosh_pos b).le n)) (signMass_pos 0 b w).le]
    · rw [ite_eq_right he]
      apply Finset.sum_nonneg
      intro j _
      apply mul_nonneg hA (mul_nonneg (pow_nonneg hr _) _)
      split <;> first | exact (signMass_pos ..).le | exact le_rfl
  apply H.trans
  have hsum := Finset.sum_le_sum (s:=Finset.range (J+1)) (fun j _ => mul_le_mul_of_nonneg_left (hcap (j:ℤ)) (pow_nonneg hr (J-j)))
  have href : (∑ i ∈ Finset.range (J+1),r^(J-i))=∑ i ∈ Finset.range (J+1),r^i := by
    simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect (fun i => r^i) (J+1)
  rw [← Finset.sum_mul,href] at hsum
  have hh := geom_sum_mul_of_le_one hr'.le (J+1)
  have hgeom : (∑ j ∈ Finset.range (J+1),r^j)≤1/(1-r) := (le_div_iff₀ (sub_pos.mpr hr')).mpr
    (hh.trans_le (sub_le_self _ (pow_nonneg hr _)))
  exact (mul_le_mul_of_nonneg_left (hsum.trans (mul_le_mul_of_nonneg_right hgeom hP)) hA).trans_eq (by dsimp [A,r]; ring)

/-- Applies uniformly to every nonnegative inhomogeneous suffix slope,
and every starting height in the ballot prefix row. -/
theorem reflected_suffix_ruin {c b : ℝ} (hc : 0≤c) (hb : 0<b) (hb' : b≤6/25)
    {n : ℕ} (hn : 255≤n) (h : ℕ) :
    ruin c n h ≤ exp (-b*h+n*b^2/2)*((21/25)/(b*√n)) := by
  have hnp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hrt := sqrt_pos.mpr hnp
  have hx := chance_interval (x:=b) (by rwa [abs_of_pos hb] : |b|≤6/25)
  have hq := up_total b
  have hv : 47/200≤upChance (-b)*upChance b := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2),congrArg (upChance (-b)*·) hq]
  have cap (j : ℤ) : downMass 0 b n j≤(21/25)/√n := (le_div_iff₀ hrt).mpr (by
    apply endpoint_cap_numbers true 0 b hn j
    intro i _; simpa only [zero_mul,sub_zero,ite_true] using hv)
  have hh := (ruin_le_fair_tails hc n h).trans (mul_le_mul_of_nonneg_left
    (fair_tail_by_endpoints hb (by positivity) n h cap) (by norm_num : (0:ℝ)≤2))
  have he : 2*exp (-b)/(1-exp (-2*b)) ≤ 1/b := by
    have h₁ : exp (-2*b)<1 := exp_lt_one_iff.mpr (by linarith only [hb])
    apply (div_le_div_iff₀ (sub_pos.mpr h₁) hb).mpr
    have hs := (self_le_sinh_iff.mpr hb.le : b≤sinh b)
    rw [sinh_eq] at hs
    have H := mul_le_mul_of_nonneg_right hs (exp_pos (-b)).le
    rw [sub_div,sub_mul,div_mul_eq_mul_div,div_mul_eq_mul_div,← exp_add,← exp_add] at H
    rw [add_neg_cancel,exp_zero,show -b+ -b= -2*b by ring] at H
    linarith only [H]
  have Hc := pow_le_pow_left₀ (cosh_pos b).le (cosh_le_exp_half_sq b) n
  rw [← exp_nat_mul] at Hc
  apply hh.trans
  rw [show -b*(h+1)= -b*h+ -b by ring,exp_add,
    show -b*h+n*b^2/2= -b*h+(n:ℝ)*(b^2/2) by ring,exp_add]
  calc
    _ = (exp (-b*h)*(cosh b)^n)*((21/25)/√n)*(2*exp (-b)/(1-exp (-2*b))) := by ring
    _ ≤ (exp (-b*h)*exp ((n:ℝ)*(b^2/2)))*((21/25)/√n)*(1/b) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hc (exp_pos _).le) (by positivity))
        he (by positivity [sub_pos.mpr (exp_lt_one_iff.mpr (by linarith only [hb]) : exp (-2*b)<1)]) (by positivity)
    _ = _ := by ring

end CentralUnimodality.MarkedExcursion
