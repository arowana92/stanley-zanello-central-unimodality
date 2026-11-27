module

public import CentralUnimodality.TiltedPairRates
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! Choosing the nearest integer to π/θ gives the required label spacing
on each of the four outer arcs. The last interval includes θ=π. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

noncomputable def outerLo : Fin 4 → ℝ
  | 0 => 1/8
  | 1 => 9/50
  | 2 => 1/4
  | 3 => 1/2

noncomputable def outerHi : Fin 4 → ℝ
  | 0 => 9/50
  | 1 => 1/4
  | 2 => 1/2
  | 3 => π

noncomputable def outerSpacing (t : ℝ) := ⌊π/t+1/2⌋₊

private theorem spacing_error {t : ℝ} (ht : 0 < t) (hπ : t ≤ π) :
    1 ≤ outerSpacing t ∧ |(outerSpacing t:ℝ)*t-π| ≤ t/2 := by
  have hl : (outerSpacing t:ℝ) ≤ π/t+1/2 := Nat.floor_le (by positivity)
  have hu : π/t+1/2 < (outerSpacing t:ℝ)+1 := Nat.lt_floor_add_one _
  have h1 : 1 ≤ π/t := (one_le_div ht).mpr hπ
  have H : 0 < (outerSpacing t:ℝ) := by linarith
  refine ⟨by exact_mod_cast (show 0 < (outerSpacing t:ℝ) from H),abs_le.mpr ⟨?_,?_⟩⟩
  · have h := mul_lt_mul_of_pos_right hu ht
    rw [add_mul,div_mul_cancel₀ _ ht.ne',add_mul] at h
    linarith
  · have h := mul_le_mul_of_nonneg_right hl ht.le
    rw [add_mul,div_mul_cancel₀ _ ht.ne'] at h
    linarith

private theorem length_cap {t lo : ℝ} {M : ℕ} (ht : 0 < t) (hlo : lo ≤ t)
    (h : π < ((M:ℝ)+1/2)*lo) : outerSpacing t ≤ M := by
  have hc := mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ (M:ℝ)+1/2)
  have hlt : π/t < (M:ℝ)+1/2 := (div_lt_iff₀ ht).mpr (h.trans_le hc)
  have hl : (outerSpacing t:ℝ) ≤ π/t+1/2 := Nat.floor_le (by positivity)
  have H : (outerSpacing t:ℝ) < ((M+1:ℕ):ℝ) := by push_cast; linarith
  exact Nat.le_of_lt_succ (by exact_mod_cast H)

private theorem angle_identity (x : ℝ) : sin (x/2)=cos ((x-π)/2) := by
  rw [show (x-π)/2= -(π/2-x/2) by ring,cos_neg,cos_pi_div_two_sub]

private theorem angle_small {t C v : ℝ} (ht : 0 < t) (hπ : t ≤ π) (htop : t ≤ C)
    (hpos : 0 ≤ 1-(C/4)^2/2) (hval : v ≤ (1-(C/4)^2/2)^2) :
    v ≤ sin (outerSpacing t*t/2)^2 := by
  let x := ((outerSpacing t:ℝ)*t-π)/2
  have hh := (spacing_error ht hπ).2
  have he : |x| ≤ C/4 := by rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith
  have hsq := pow_le_pow_left₀ (abs_nonneg x) he 2
  rw [sq_abs] at hsq
  have hc := one_sub_sq_div_two_le_cos (x:=x)
  rw [angle_identity]
  exact hval.trans (pow_le_pow_left₀ hpos (by linarith only [hsq,hc] : 1-(C/4)^2/2 ≤ cos x) 2)

private theorem angle_wide {t : ℝ} (ht : 0 < t) (hπ : t ≤ π) :
    3/4 ≤ sin (outerSpacing t*t/2)^2 := by
  let l := outerSpacing t
  have ⟨hl,he⟩ := spacing_error ht hπ
  have hphase : |(l:ℝ)*t-π| ≤ π/3 := by
    rcases le_total t (2*π/3) with h|h
    · exact he.trans (by linarith)
    · by_cases h0 : t=2*π/3
      · exact he.trans (by linarith)
      · have hlt := lt_of_le_of_ne h (Ne.symm h0)
        have hh : π/t < 3/2 := (div_lt_iff₀ ht).mpr (by linarith only [hlt])
        have lcap : (l:ℝ) ≤ π/t+1/2 := Nat.floor_le (by positivity)
        have ltwo : (l:ℝ) < 2 := by linarith
        have lnat : l<2 := by exact_mod_cast ltwo
        have hl1 : l=1 := by change 1 ≤ l at hl; omega
        rw [hl1,Nat.cast_one,one_mul,abs_of_nonpos (sub_nonpos.mpr hπ)]
        linarith
  let x := ((l:ℝ)*t-π)/2
  have hx : |x| ≤ π/6 := by rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith
  have hc := cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x) (by linarith only [pi_pos] : π/6 ≤ π) hx
  rw [cos_abs] at hc
  rw [angle_identity,← sq_cos_pi_div_six]
  exact pow_le_pow_left₀ (by rw [cos_pi_div_six]; positivity) hc 2

/-- Both the integer spacing and the squared-sine lower bound, with all
frequency endpoints included. -/
theorem outer_spacing_data (s : Fin 4) {t : ℝ} (hlo : outerLo s ≤ t) (hhi : t ≤ outerHi s) :
    1 ≤ outerSpacing t ∧ outerSpacing t ≤ (pairArc s).maxLen ∧
      ((pairArc s).sineSq:ℝ) ≤ sin (outerSpacing t*t/2)^2 := by
  have hp := Real.pi_lt_d4
  have hm := Real.pi_gt_three
  fin_cases s <;> norm_num [outerLo,outerHi,pairArc] at hlo hhi ⊢
  all_goals have ht : 0<t := by linarith
  all_goals have hπ : t ≤ π := by linarith
  all_goals refine ⟨(spacing_error ht hπ).1,length_cap ht hlo (by norm_num; linarith),?_⟩
  · exact angle_small ht hπ hhi (by norm_num) (by norm_num)
  · exact angle_small ht hπ hhi (by norm_num) (by norm_num)
  · exact angle_small ht hπ hhi (by norm_num) (by norm_num)
  · exact angle_wide ht hπ

end CentralUnimodality.MarkedExcursion
